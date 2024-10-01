{-# LANGUAGE LambdaCase, OverloadedRecordDot, OverloadedStrings #-}
module Mono (mono) where

import AST.Converged (Prelude)
import AST.Common (Module, AnnStmt, Annotated (..), Expr, Type, Env, UniqueVar (..), UniqueCon (..), UniqueType (..), TVar, EnvUnion, TCon (..), UnionID (..), Ann, EnvID (..))
import AST.Typed (Typed)
import qualified AST.Typed as T
import AST.Mono (Mono)
import qualified AST.Mono as M
import Data.Fix (Fix(..))
import Control.Monad.Trans.Reader (ReaderT, runReaderT)
import Data.Functor.Foldable (transverse, embed, cata, para, Base, project)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map, (!?))
import Control.Monad.Trans.State (StateT, runStateT, get, modify, put, gets)
import qualified Data.Map as Map
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Data.Foldable (fold)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)


data Context' = Context
  { typeFind :: Map (UniqueType, [Type Mono]) UniqueType  -- this is used to find types. (won't be preserved)
  , typeOrder :: [Annotated M.DataDef]  -- this actually orders types. (part of the interface)

  , tvarMap :: Map TVar (Type Mono)  -- this describes the temporary mapping of tvars while monomorphizing.

  -- Monomorphized cached versions of functions
  , funFind :: Map (UniqueVar, Type Mono) UniqueVar
  , conFind :: Map (UniqueCon, Type Mono) UniqueCon

  -- Ordering so that functions won't need forward declarations.
  , funOrder :: [Annotated M.Function]

  -- Typed functions/constructors (not yet monomorphized)
  , functions :: Map UniqueVar (Annotated Function)
  , constructors :: Map UniqueCon T.DataDef
  , types :: Map UniqueType (Annotated T.DataDef)
  }

type Context = StateT Context' IO

mono :: Prelude -> Module Typed -> IO (Module Mono)
mono prelude mod = do
  let combined = T.fromMod prelude <> T.fromMod mod

  -- I think I'll just do it procedurally
  --   But gather types before!
  (stmts, ctx) <- flip runStateT startingContext $ mStmts combined
  let mtypes = ctx.typeOrder
  let mfuns = ctx.funOrder
  let mmod = M.Mod { M.dataTypes = mtypes, M.functions = mfuns, M.main = stmts }
  pure mmod


mStmts = traverse mAnnStmt

mAnnStmt :: AnnStmt Typed -> Context (AnnStmt Mono)
mAnnStmt = cata $ fmap embed . (\(T.AnnStmt ann stmt) -> 
  let mann = M.AnnStmt ann
      noann = M.AnnStmt []
  in case first mExpr stmt of
  T.Pass -> pure $ M.AnnStmt ann M.Pass
  T.Assignment vid expr -> mann . M.Assignment vid <$> expr
  T.Print expr -> mann . M.Print <$> expr
  T.MutDefinition vid ete -> mann . M.MutDefinition vid <$> bitraverse mType id ete
  T.MutAssignment vid expr -> mann . M.MutAssignment vid <$> expr
  T.If cond ifTrue elseIfs else' -> fmap mann $ M.If
    <$> cond
    <*> sequenceA ifTrue
    <*> traverse (bitraverse id sequenceA) elseIfs
    <*> traverse sequenceA else'
  T.ExprStmt expr -> mann . M.ExprStmt <$> expr
  T.Return ete -> mann . M.Return <$> ete

  T.DataDefinition datadef -> do
    addDatatype ann datadef
    pure $ noann M.Pass

  T.FunctionDefinition fundec body -> do
    addFunction ann (Function fundec (sequenceA body))
    pure $ noann M.Pass
  )


mExpr :: Expr Typed -> Context (Expr Mono)
mExpr = cata $ fmap embed . \(T.ExprType t expr) -> do
  t' <- mType t
  expr' <- case expr of

    T.Var locality vid -> do
      vid' <- variable vid t'
      pure $ M.Var locality vid'

    T.Con cid -> do
      cid' <- constructor cid t'
      pure $ M.Con cid'

    T.Lit lit -> pure $ M.Lit lit
    T.Op l op r -> M.Op <$> l <*> pure op <*> r
    T.Call e args -> M.Call <$> e <*> sequenceA args
    T.As e _ -> do
      -- Ignore 'as' by unpacking the variable and passing in the previous expression.
      (Fix (M.ExprType _ e')) <- e
      pure e'
    T.Lam env args ret ->
      let args' = (traverse . traverse) mType args
      in M.Lam <$> mEnv (mType <$> env) <*> args' <*> ret

  pure $ M.ExprType t' expr'

mType :: Type Typed -> Context (Type Mono)
mType = cata $ fmap embed . \case
  T.TCon tid pts -> do

    params <- sequenceA pts
    mt <- typeCon tid params "mono"
    pure $ decoMonoType mt

  T.TFun union params ret -> do
    union' <- mUnion union
    params' <- sequenceA params

    M.TFun union' params' <$> ret

  T.TVar tv -> decoMonoType <$> retrieveTV tv

mUnion :: T.EnvUnionF (Context (Type Mono)) -> Context (EnvUnion Mono)
mUnion T.EnvUnion { T.unionID = unionID, T.union = union } = do
  union' <- traverse mEnv union
  case union' of
    [] -> error $ "This means that we have some empty union during monomorphization, which should not happen. The union ID is " <> show unionID <> "."
    e:es -> pure $ M.EnvUnion
      { M.unionID = unionID, M.union = e :| es }

mEnv :: T.EnvF (Context (Type Mono)) -> Context (Env Mono)
mEnv T.Env { T.envID = envID, T.env = env } = do
  env' <- traverse sequenceA env
  pure $ M.Env { M.envID = envID, M.env = env' }





-- <---------8

-- Adds a new monomorphized type.
--   Reuses previously added types where possible.
typeCon :: UniqueType -> [Type Mono] -> Text -> Context (Type Mono)
typeCon t apps nameAppend = do
  typeFind <- gets typeFind

  -- Check if we've already monomorphized this type before.
  case typeFind !? (t, apps) of

    -- Yes, we have. Just return it.
    Just tid -> pure $ convertUT tid apps

    -- No, do funny stuff.
    Nothing -> do
      -- Find the type
      types <- gets types
      let (Annotated anns oldType@(T.DD _ tvs _)) = case types !? t of
              Just t' -> t'
              Nothing -> error "Should not happen. (But will happen in practice though due to environments)"

      -- Make a new type.
      newTID <- liftIO newUnique
      let newUniqueType = TI { typeID = newTID, typeName = TC (fromTC t.typeName <> nameAppend) }
      let newType = convertUT newUniqueType apps

      -- Add the monotype (to be referred to later)
      -- Add it here to prevent infinite recursion (for example, in case of pointers, which refer back to the structure, which are mono-ed in the constructor)
      modify $ \ctx -> ctx { typeFind = Map.insert (t, apps) newUniqueType ctx.typeFind }

      -- Monomorphize data definition here (by comparing old type to new type)
      let tempOldType = Fix $ T.TCon t $ Fix . T.TVar <$> tvs  -- it is trivial to make one
      mDataDef <- mapType tempOldType newType $ do
        let (T.DD _ _ dcs) = oldType
        newDCs <- for dcs $ \(Annotated anns (T.DC uc ts)) ->
          fmap (Annotated anns) $ do
            -- we need to update searchable constructors (used by 'constructor')
            mts <- traverse mType ts
            conType <- case mts of
                  [] -> pure newType
                  mts -> do
                    union <- emptyUnion
                    pure $ Fix $ M.TFun union mts newType
            modify $ \ctx -> ctx { conFind = Map.insert (uc, conType) uc ctx.conFind }

            -- I don't think we need to change UniqueCon, as we will not directly compare constructors from now on? (and in codegen, they will be prefixed with the newUniqueType)
            pure $ M.DC uc mts

        let newDataDef = Annotated anns $ M.DD newUniqueType newDCs
        pure newDataDef


      -- Add the monomorphized data definition to data order
      modify $ \ctx -> ctx { typeOrder = ctx.typeOrder ++ [ mDataDef ] }

      pure newType

emptyUnion :: Context (EnvUnion Mono)
emptyUnion = do
  envID <- EnvID <$> liftIO newUnique
  let env = M.Env { M.envID = envID, M.env = [] }
  unionID  <- UnionID <$> liftIO newUnique
  let union = M.EnvUnion { M.unionID = unionID, M.union = NonEmpty.singleton env }
  pure union


-- TODO: Example why we need previous knowledge about applications/later substitutions.
-- x =& :1  # we need type knowledge here.
-- ....
-- f (x a)
--  x <&= :printThenReturn(x, 420)
-- f(1)
-- f(True)
retrieveTV :: TVar -> Context (Type Mono)
retrieveTV tv = do
  ctx <- get
  case ctx.tvarMap !? tv of
    Nothing -> error "It should not be possible. Probably, because the polymorphic application somehow leaked?"
    Just t -> pure t


-- Both of these functions should contains this logic:
--  1. check if variable is a function
--     if it's not, leave it unchanged
--  2. when it's a function, we want to monomorphize this function. check if we already have the monomorphic version of this function somewhere (eg. from a (UniqueVar, Type Mono) map)
--     if it is, return its UniqueVar
--  3. if it's not, apply the body and function declaration. then add it to those maps, so next time it will be selected like this.
variable :: UniqueVar -> Type Mono -> Context UniqueVar
variable ti t = do
  monofuns <- gets funFind
  case monofuns !? (ti, t) of
    Just monofun -> pure monofun
    Nothing -> do
      funs <- gets functions
      case funs !? ti of
        Nothing -> pure ti
        Just fun -> do
          mFunction fun t



constructor :: UniqueCon -> Type Mono -> Context UniqueCon
constructor ci t = do
  monocons <- gets conFind
  case monocons !? (ci, t) of
    Just monocon -> pure monocon
    Nothing -> do
      let relatedCons = filter (\((uc, _), _) -> uc == ci) $ Map.toList monocons
      error $ "Not really possible. A monomorphic type means that the type was already added: " <> show ci <> "\n" <> show t <> "\nWITH: " <> show relatedCons


addFunction :: [Ann] -> Function -> Context ()
addFunction anns function@(Function (T.FD _ uv _ _) _) =
  modify $ \ctx -> ctx { functions = Map.insert uv (Annotated anns function) ctx.functions }

addDatatype :: [Ann] -> T.DataDef -> Context ()
addDatatype anns dd@(T.DD ut _ dc) =
  let cids = fmap (\(Annotated _ (T.DC uc _)) -> uc) dc

  -- For each constructor ID adds this datatype.
  in modify $ \ctx -> ctx
    { constructors = foldr (`Map.insert` dd) ctx.constructors cids
    , types = Map.insert ut (Annotated anns dd) ctx.types
    }


-- These functions do
--   - map types
--   - type function
--   - order it and add it to context
-- then, these mappings are retrieved by the 'retrieveTV' function
mFunction :: Annotated Function -> Type Mono -> Context UniqueVar
mFunction (Annotated anns (Function fundec@(T.FD _ tv _ _) ctxBody)) monoType = do
  -- !!! THIS SHOULD BE REMOVED BECAUSE IT IS SHITTY
  let placeholderUnionID = case monoType of
        Fix (M.TFun (M.EnvUnion uid _) _ _) -> uid
        tmono -> error $ "SHOULD NOT HAPPEN. This type should have been a function type: " <> show tmono

  let funtype = fundec2type placeholderUnionID fundec  -- convert from function declaration to a Type Typed
  mapType funtype monoType $ do
    mfd@(M.FD _ uv _ _) <- mFunDec fundec
    body <- ctxBody

    let mFun = M.Fun mfd body

    -- add it to monomorphized functions
    ctx <- get
    let ctx' = ctx { funFind = Map.insert (tv, monoType) uv ctx.funFind, funOrder = ctx.funOrder ++ [Annotated anns mFun] }
    put ctx'

    pure uv

mFunDec :: T.FunDec -> Context M.FunDec
mFunDec (T.FD env oldUV params ret) = do
  env' <- mEnv $ fmap mType env
  newUV <- mkUV oldUV
  params' <- traverse2 mType params
  ret' <- mType ret
  pure $ M.FD env' newUV params' ret'


-- Figures out TVar -> MonoType mappings from two types: one before and one after monomorphization.
--  it produces a type map which is then passed to the context in a stack-like way
--   Used only in mFunction (for mono-ing functions) and typeCon (for mono-ing types and data definitions)
--    however, the one in 'typeCon' is trivial - so much so, that we can specialize it for mFunction OR generalize it for both use cases (pass in a TVar -> MonoVar map instead of two types.)
--      TODO: do the generalized version - will be cleaner
--   !!! It might not be needed (the interface might be bad)
mapType :: Type Typed -> Type Mono -> Context a -> Context a
mapType og mono ctx = do
  let doMap :: Type Typed -> Type Mono -> Context (Map TVar (Type Mono))
      doMap (Fix (T.TFun tunion tparams tret)) (Fix (M.TFun munion mparams mret)) = do
        -- not sure if we have to do that and how careful should we be with IDs
        union <- doUnion tunion munion
        ret <- doMap tret mret
        pmap <- doMaps tparams mparams
        pure $ union <> ret <> pmap

      doMap (Fix (T.TCon _ tts)) (Fix (M.TCon _ mts)) = doMaps tts mts

      doMap (Fix (T.TVar tv)) mt = pure $ Map.singleton tv mt
      doMap mt mm = error $ "Mono: Type mapping failed. Should not happen: " <> show mt <> " | " <> show mm

      doMaps :: [Type Typed] -> [Type Mono] -> Context (Map TVar (Type Mono))
      doMaps tts mts = fold <$> traverse (uncurry doMap) (zip tts mts)

      doUnion :: EnvUnion Typed -> EnvUnion Mono -> Context (Map TVar (Type Mono))
      doUnion (T.EnvUnion _ tenvs) (M.EnvUnion _ menvs) = do
        -- make EnvID -> Env map
        let tenvmap = Map.fromList $ fmap (\env -> (env.envID, env.env)) tenvs
            menvmap = Map.fromList $ NonEmpty.toList $ fmap (\env -> (env.envID, env.env)) menvs

        let doEnv :: [(UniqueVar, Type Typed)] -> [(UniqueVar, Type Mono)] -> Context (Map TVar (Type Mono))
            doEnv tenvs menvs =
              let envmap = Map.intersectionWith doMap (Map.fromList tenvs) (Map.fromList menvs)
              in fold <$> sequenceA (Map.elems envmap)

        let envmap = Map.intersectionWith doEnv tenvmap menvmap
        didmaps <- fold <$> sequenceA (Map.elems envmap)
        pure didmaps

  mapping <- doMap og mono  -- generate this mapping (this will have greater precedence over other)

  -- Temporarily add mapping in a stack-like way.
  oldtvarMap <- gets tvarMap
  modify $ \s -> s { tvarMap = Map.union mapping oldtvarMap }  -- Reminder: Map.union prefers keys from first argument
  result <- ctx
  modify $ \s -> s { tvarMap = oldtvarMap }

  pure result

-- just makes a new UniqueVar (creates a new ID for deduplication with the unmonomorphized)
mkUV :: UniqueVar -> Context UniqueVar
mkUV uv = do
  newVar <- liftIO newUnique
  pure $ uv { varID = newVar }

convertUT :: UniqueType -> [Type Mono] -> Type Mono
convertUT ut apps = Fix $ M.TCon ut apps

decoMonoType :: Type Mono -> M.TypeF (Type Mono)
decoMonoType = project

fundec2type :: UnionID -> T.FunDec -> Type Typed
fundec2type placeholderUnionID (T.FD env _ params ret) = 
  let union = T.EnvUnion placeholderUnionID [env]
  in Fix $ T.TFun union (snd <$> params) ret



data Function = Function T.FunDec (Context (NonEmpty (AnnStmt Mono)))


startingContext :: Context'
startingContext = Context
  { typeFind = Map.empty
  , typeOrder = []

  , tvarMap = Map.empty

  , funFind = Map.empty
  , conFind = Map.empty
  , funOrder = []

  , functions = Map.empty
  , constructors = Map.empty
  , types = Map.empty
  }


traverse2 = traverse . traverse
