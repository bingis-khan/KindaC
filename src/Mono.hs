{-# LANGUAGE LambdaCase, OverloadedRecordDot, OverloadedStrings #-}
module Mono (mono) where

import AST.Converged (Prelude(..))
import AST.Common (Module, AnnStmt, Annotated (..), Expr, Type, Env, UniqueVar (..), UniqueCon (..), UniqueType (..), TVar, EnvUnion, TCon (..), UnionID (..), Ann, EnvID (..), Mutability (..), VarName (..), (<+>))
import AST.Typed (Typed)
import qualified AST.Typed as T
import AST.Mono (Mono, MonoInt)
import qualified AST.Mono as M
import qualified AST.Common as Common
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
import Data.Functor ((<&>))


data Context' = Context
  { typeFind :: Map (UniqueType, [Type Mono], [EnvUnion Mono]) UniqueType  -- this is used to find types. (won't be preserved)
  , typeOrder :: [Annotated M.DataDef]  -- this actually orders types. (part of the interface)

  , tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.

  -- Monomorphized cached versions of functions
  , funFind :: Map (UniqueVar, Type Mono) M.EnvDef  -- Env and Union are for later environment addition
  , conFind :: Map (UniqueCon, Type Mono) UniqueCon

  -- Ordering so that functions won't need forward declarations.
  , funOrder :: [Annotated (M.Function (AnnStmt MonoInt))]

  -- Typed functions/constructors (not yet monomorphized)
  , functions :: Map UniqueVar (Annotated Function)
  , constructors :: Map UniqueCon T.DataDef
  , types :: Map UniqueType (Annotated T.DataDef)
  }



type Context = StateT Context' IO

mono :: Prelude -> Module Typed -> IO (Module Mono)
mono prelude mod = do
  let combined = T.fromMod prelude.tpModule <> T.fromMod mod

  -- I think I'll just do it procedurally
  --   But gather types before!
  (mistmts, ctx) <- flip runStateT startingContext $ mStmts combined
  let mtypes = ctx.typeOrder
  let mifuns = ctx.funOrder

  -- Change the representation of a funFind map from (UV, Type) -> UV to UV -> [UV]
  let usageFind = toUsageFind ctx.funFind

  let mstmts = substEnv usageFind <$> mistmts 
  let mfuns = substEnv usageFind `fmap3` mifuns
  let mmod = M.Mod { M.dataTypes = mtypes, M.functions = mfuns, M.main = mstmts }
  pure mmod


substEnv :: Map UniqueVar (NonEmpty M.EnvDef) -> AnnStmt MonoInt -> AnnStmt Mono
substEnv usageFind = cata $ embed . first substf
  where
    substf :: M.EnvPlaceholder -> M.EnvDefs
    substf (M.EPH uv) = case usageFind !? uv of
      Nothing -> []
      Just (v:|vs) -> v:vs

toUsageFind :: Map (UniqueVar, Type Mono) M.EnvDef -> Map UniqueVar (NonEmpty M.EnvDef)
toUsageFind = Map.mapKeysWith (<>) fst . fmap NonEmpty.singleton


mStmts = traverse mAnnStmt

mAnnStmt :: AnnStmt Typed -> Context (AnnStmt MonoInt)
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

  T.FunctionDefinition fundec@(T.FD _ uv _ _) body -> do
    addFunction ann (Function fundec (sequenceA body))
    pure $ noann $ M.EnvHere $ M.EPH uv
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
      M.EnvInit <$> mLambda t' env args ret  -- M.Lam <$> mEnv (mType <$> env) <*> args' <*> ret

  pure $ M.ExprType t' expr'

mType :: Type Typed -> Context (Type Mono)
mType = cata $ fmap embed . \case
  T.TCon tid pts unions -> do

    params <- sequenceA pts
    unions' <- mUnion `traverse` unions
    mt <- typeCon tid params unions' ""
    pure $ decoMonoType mt

  T.TFun union params ret -> do
    union' <- mUnion union
    params' <- sequenceA params

    M.TFun union' params' <$> ret

  T.TVar tv -> decoMonoType <$> retrieveTV tv

mUnion :: T.EnvUnionF (Context (Type Mono)) -> Context (EnvUnion Mono)
mUnion T.EnvUnion { T.unionID = unionID, T.union = union } = do
  typemap <- gets tvarMap
  case lookupUnionMap typemap unionID of
    Just munion -> pure munion
    Nothing -> do
      union' <- traverse mEnv union
      case union' of
        [] -> error $ "This means that we have some empty union during monomorphization, which should not happen. The union ID is " <> show unionID <> "."

        -- TEMP
        -- [] -> pure $ M.EnvUnion { M.unionID = unionID, M.union = (M.Env { M.envID = EnvID (fromUnionID unionID), M.env = [] }) :| [] }

        e:es -> pure $ M.EnvUnion
          { M.unionID = unionID, M.union = e :| es }

mEnv :: T.EnvF (Context (Type Mono)) -> Context (Env Mono)
mEnv T.Env { T.envID = envID, T.env = env } = do
  env' <- for env $ \(uv, ctxt) -> do
    ctxt' <- ctxt
    uv' <- variable uv ctxt'
    pure (uv', ctxt')
  pure $ M.Env { M.envID = envID, M.env = env' }





-- <---------8

-- Adds a new monomorphized type.
--   Reuses previously added types where possible.
typeCon :: UniqueType -> [Type Mono] -> [EnvUnion Mono] -> Text -> Context (Type Mono)
typeCon t apps unions nameAppend = do
  typeFind <- gets typeFind

  -- Check if we've already monomorphized this type before.
  case typeFind !? (t, apps, unions) of

    -- Yes, we have. Just return it.
    Just tid -> pure $ convertUT tid apps

    -- No, do funny stuff.
    Nothing -> do
      -- Find the type
      types <- gets types
      let (Annotated anns oldType@(T.DD _ tvs tunions _)) = case types !? t of
              Just t' -> t'

              -- this should not happen when we add memoized definitions in types.
              Nothing -> error "Should not happen. (But will happen in practice though due to environments) ((why? we still haven't fixed the problem of union'ing environments from outside of module))"

      -- Make a new type.
      newTID <- liftIO newUnique
      let newUniqueType = TI { typeID = newTID, typeName = TC (fromTC t.typeName <> nameAppend) }
      let newType = convertUT newUniqueType apps

      -- Add the monotype (to be referred to later)
      -- Add it here to prevent infinite recursion (for example, in case of pointers, which refer back to the structure, which are mono-ed in the constructor)
      modify $ \ctx -> ctx { typeFind = Map.insert (t, apps, unions) newUniqueType ctx.typeFind }

      -- monomorphize by unifying applied
      --  1. type variables (applied)
      --  2. unions (from function types in the datatype)
      mDataDef <- mapType (zip (Fix . T.TVar <$> tvs) apps) (zip tunions unions) $ do
        let (T.DD _ _ _ dcs) = oldType
        newDCs <- for dcs $ \(Annotated anns (T.DC uc ts)) ->
          fmap (Annotated anns) $ do
            -- we need to update searchable constructors (used by 'constructor')
            mts <- traverse mType ts
            conType <- case mts of
                  [] -> pure newType
                  mts -> do
                    union <- emptyUnion
                    pure $ Fix $ M.TFun union mts newType

            -- I don't think we need to change UniqueCon, as we will not directly compare constructors from now on? (and in codegen, they will be prefixed with the newUniqueType)
            -- UPDATE: we need to do that. example: Proxy Int and Proxy Bool will use the same constructor, which uses the same enum -> type error in C.
            newCID <- liftIO newUnique
            let uc' = uc { conID = newCID }

            modify $ \ctx -> ctx { conFind = Map.insert (uc, conType) uc' ctx.conFind }
            pure $ M.DC uc' mts

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
  case lookupTVarMap ctx.tvarMap tv of
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
    Just (M.EnvDef (M.FD _ monofun _ _) _) -> pure monofun
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
      -- error $ "Not really possible. A monomorphic type means that the type was already added: " <> show ci <> "\n" <> M.ctx M.tType t <> "\n" <> M.ctx (Common.indent "With:" . Common.sepBy "\n" . fmap (\((conFrom, typeFrom), conTo) -> Common.ppCon conFrom <> ":" <+> M.tType typeFrom <+> "=>" <+> Common.ppCon conTo)) relatedCons
      -- TEMP
      pure ci


addFunction :: [Ann] -> Function -> Context ()
addFunction anns function@(Function (T.FD _ uv _ _) _) =
  modify $ \ctx -> ctx { functions = Map.insert uv (Annotated anns function) ctx.functions }

addDatatype :: [Ann] -> T.DataDef -> Context ()
addDatatype anns dd@(T.DD ut _ _ dc) =
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
  -- !!! THIS SHOULD BE REMOVED BECAUSE IT IS SHITTY (by that I meant the placeholderUnionID, which is used to create a function type. But "downcasting" the type to get a union is also very iffy. )
  let union@(M.EnvUnion placeholderUnionID _) = case monoType of
        Fix (M.TFun union _ _) -> union
        tmono -> error $ "SHOULD NOT HAPPEN. This type should have been a function type: " <> show tmono

  let funtype = fundec2type placeholderUnionID fundec  -- convert from function declaration to a Type Typed
  mapType [(funtype, monoType)] [] $ do
    mfd@(M.FD _ uv _ _) <- mFunDec fundec
    body <- ctxBody

    let mFun = M.Fun mfd union body

    -- add it to monomorphized functions
    modify $ \ctx -> ctx { funFind = Map.insert (tv, monoType) (M.EnvDef mfd union) ctx.funFind, funOrder = ctx.funOrder ++ [Annotated anns mFun] }

    pure uv

mLambda :: Type Mono -> Env Typed -> [(UniqueVar, Type Typed)] -> Context (Expr Mono) -> Context M.EnvDef
mLambda t tenv tparams tret = do
  let (Fix (M.TFun union _ _)) = t  -- safe but unsafe cast.
  env <- mEnv $ mType <$> tenv
  params <- traverse2 mType tparams
  expr@(Fix (M.ExprType ret _)) <- tret

  -- Make fundec (outside :0)
  newUV <- mkLambdaUV
  let fundec = M.FD env newUV params ret
  let body = NonEmpty.singleton $ Fix $ M.AnnStmt [] $ M.Return expr
  let mFun = M.Fun fundec union body

  -- add it to monomorphized functions
  modify $ \ctx -> ctx { funOrder = ctx.funOrder ++ [Annotated [] mFun] }

  let envdef = M.EnvDef fundec union

  pure envdef

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
mapType :: [(Type Typed, Type Mono)] -> [(EnvUnion Typed, EnvUnion Mono)] -> Context a -> Context a
mapType types2uni unions2uni ctx = do
  let doMap :: Type Typed -> Type Mono -> Context TypeMap
      doMap (Fix (T.TFun tunion tparams tret)) (Fix (M.TFun munion mparams mret)) = do
        -- not sure if we have to do that and how careful should we be with IDs
        union <- doUnion tunion munion
        ret <- doMap tret mret
        pmap <- doMaps $ zip tparams mparams
        pure $ union <> ret <> pmap

      -- notice that we don't unify unions here. this information is absent from the type signature of monomorphic types as it is not really needed.
      doMap (Fix (T.TCon _ tts _)) (Fix (M.TCon _ mts)) = doMaps $ zip tts mts

      doMap (Fix (T.TVar tv)) mt = pure $ mkTVarMap tv mt
      doMap mt mm = error $ "Mono: Type mapping failed. Should not happen: " <> show mt <> " | " <> show mm

      doMaps :: [(Type Typed, Type Mono)] -> Context TypeMap
      doMaps = fmap fold . traverse (uncurry doMap)

      doUnion :: EnvUnion Typed -> EnvUnion Mono -> Context TypeMap
      doUnion tunion@(T.EnvUnion _ tenvs) munion@(M.EnvUnion _ menvs) = do
        -- make EnvID -> Env map
        let tenvmap = Map.fromList $ fmap (\env -> (env.envID, env.env)) tenvs
            menvmap = Map.fromList $ NonEmpty.toList $ fmap (\env -> (env.envID, env.env)) menvs

        let doEnv :: [(UniqueVar, Type Typed)] -> [(UniqueVar, Type Mono)] -> Context TypeMap
            doEnv tenvs menvs =
              let envmap = Map.intersectionWith doMap (Map.fromList tenvs) (Map.fromList menvs)
              in fold <$> sequenceA (Map.elems envmap)

        let envmap = Map.intersectionWith doEnv tenvmap menvmap
        didmaps <- fold <$> sequenceA (Map.elems envmap)
        let unionMap = mkUnionMap tunion munion
        pure $ unionMap <> didmaps

      doUnions :: [(EnvUnion Typed, EnvUnion Mono)] -> Context TypeMap
      doUnions = fmap fold . traverse (uncurry doUnion)

  mapping <- liftA2 (<>) (doMaps types2uni) (doUnions unions2uni) -- generate this mapping (this will have greater precedence over other)

  -- Temporarily add mapping in a stack-like way.
  oldtvarMap <- gets tvarMap
  modify $ \s -> s { tvarMap = mapping <> oldtvarMap }  -- Reminder: union prefers keys from first argument
  result <- ctx
  modify $ \s -> s { tvarMap = oldtvarMap }

  pure result

-- just makes a new UniqueVar (creates a new ID for deduplication with the unmonomorphized)
mkUV :: UniqueVar -> Context UniqueVar
mkUV uv = do
  newVar <- liftIO newUnique
  pure $ uv { varID = newVar }

-- used by 'mLambda' (lambdas don't have UniqueVars)
mkLambdaUV :: Context UniqueVar
mkLambdaUV = do
  newVar <- liftIO newUnique
  pure $ VI
    { varID = newVar
    , varName = VN "lambda"
    , mutability = Immutable
    }

convertUT :: UniqueType -> [Type Mono] -> Type Mono
convertUT ut apps = Fix $ M.TCon ut apps

decoMonoType :: Type Mono -> M.TypeF (Type Mono)
decoMonoType = project

fundec2type :: UnionID -> T.FunDec -> Type Typed
fundec2type placeholderUnionID (T.FD env _ params ret) = 
  let union = T.EnvUnion placeholderUnionID [env]
  in Fix $ T.TFun union (snd <$> params) ret


-- TypeMap stuff

data TypeMap = TypeMap (Map TVar (Type Mono)) (Map UnionID (EnvUnion Mono))


lookupTVarMap :: TypeMap -> TVar -> Maybe (Type Mono)
lookupTVarMap (TypeMap tvars _) tvar = tvars !? tvar

lookupUnionMap :: TypeMap -> UnionID -> Maybe (EnvUnion Mono)
lookupUnionMap (TypeMap _ unions) union = unions !? union

mkTVarMap :: TVar -> Type Mono -> TypeMap
mkTVarMap tv ty = TypeMap (Map.singleton tv ty) mempty

mkUnionMap :: EnvUnion Typed -> EnvUnion Mono -> TypeMap
mkUnionMap (T.EnvUnion { T.unionID = unionID }) munion = TypeMap mempty (Map.singleton unionID munion)

instance Semigroup TypeMap where
  TypeMap tvars unions <> TypeMap tvars' unions' = TypeMap (tvars <> tvars') (unions <> unions')

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty


data Function = Function T.FunDec (Context (NonEmpty (AnnStmt MonoInt)))


startingContext :: Context'
startingContext = Context
  { typeFind = Map.empty
  , typeOrder = []

  , tvarMap = mempty

  , funFind = Map.empty
  , conFind = Map.empty
  , funOrder = []

  , functions = Map.empty
  , constructors = Map.empty
  , types = Map.empty
  }


traverse2 = traverse . traverse
fmap3 = fmap . fmap . fmap

