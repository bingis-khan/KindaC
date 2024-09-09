{-# LANGUAGE LambdaCase, OverloadedRecordDot, OverloadedStrings #-}
module Mono (mono) where

import AST.Converged (Prelude)
import AST.Common (Module, AnnStmt, Annotated (..), Expr, Type, Env, UniqueVar (..), UniqueCon (..), UniqueType (..), TVar, EnvUnion, TCon (..))
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
import Control.Monad.Trans.State (StateT, runStateT, get, modify, put)
import qualified Data.Map as Map
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)


data Context' = Context
  { typeFind :: Map (UniqueType, [Type Mono]) UniqueType  -- this is used to find types. (won't be preserved)
  , typeOrder :: [Type Mono]  -- this actually orders types. (part of the interface)

  , tvarMap :: Map TVar (Type Mono)

  , varFind :: Map (UniqueVar, Type Mono) UniqueVar
  , conFind :: Map (UniqueCon, Type Mono) UniqueCon

  , functions :: Map UniqueVar Function
  , constructors :: Map UniqueCon T.DataDef
  }

type Context = StateT Context' IO

mono :: Prelude -> Module Typed -> IO (Module Mono)
mono prelude mod = do
  let combined = T.fromMod prelude <> T.fromMod mod

  -- I think I'll just do it procedurally
  --   But gather types before!
  stmts <- flip runStateT startingContext $ mStmts combined
  undefined


mStmts = traverse mAnnStmt

mAnnStmt :: AnnStmt Typed -> Context (AnnStmt Mono)
mAnnStmt = cata $ fmap embed . (\(T.AnnStmt ann stmt) -> M.AnnStmt ann <$> case first mExpr stmt of
  T.Pass -> pure M.Pass
  T.Assignment vid expr -> M.Assignment vid <$> expr
  T.Print expr -> M.Print <$> expr
  T.MutDefinition vid ete -> M.MutDefinition vid <$> bitraverse mType id ete
  T.MutAssignment vid expr -> M.MutAssignment vid <$> expr
  T.If cond ifTrue elseIfs else' -> M.If
    <$> cond
    <*> sequenceA ifTrue
    <*> traverse (bitraverse id sequenceA) elseIfs
    <*> traverse sequenceA else'
  T.ExprStmt expr -> M.ExprStmt <$> expr
  T.Return ete -> M.Return <$> bitraverse mType id ete

  T.DataDefinition datadef -> do
    addDatatype datadef
    pure M.Pass

  T.FunctionDefinition fundec body -> do
    addFunction (Function fundec (sequenceA body))
    pure M.Pass
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
      -- Ignore 'As' by unpacking the variable and passing in the previous expression.
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
    tid' <- type_ tid params "mono"
    pure $ M.TCon tid'

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
type_ :: UniqueType -> [Type Mono] -> Text -> Context UniqueType
type_ t apps nameAppend = do
  ctx <- get

  -- Check if we've already monomorphized this type before.
  case ctx.typeFind !? (t, apps) of

    -- Yes, we have. Just return it.
    Just tid -> pure tid

    -- No, do funny stuff.
    Nothing -> do

      -- Make a new type.
      newTID <- liftIO newUnique
      let
        newType = TI { typeID = newTID, typeName = TC (fromTC t.typeName <> nameAppend) }
        ctx' = ctx { typeFind = Map.insert (t, apps) newType ctx.typeFind, typeOrder = ctx.typeOrder ++ [ undefined ] }

      put ctx'
      pure newType


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
variable ti t = undefined

constructor :: UniqueCon -> Type Mono -> Context UniqueCon
constructor ci t = undefined


addFunction :: Function -> Context ()
addFunction function@(Function (T.FD _ uv _ _) _) =
  modify $ \ctx -> ctx { functions = Map.insert uv function ctx.functions }

addDatatype :: T.DataDef -> Context ()
addDatatype dd@(T.DD _ _ dc) =
  let cids = fmap (\(Annotated _ (T.DC uc _)) -> uc) dc

  -- For each constructor ID adds this datatype.
  in modify $ \ctx -> ctx { constructors = foldr (`Map.insert` dd) ctx.constructors cids }


decoMonoType :: Type Mono -> M.TypeF (Type Mono)
decoMonoType = project


data Function = Function T.FunDec (Context (NonEmpty (AnnStmt Mono)))


startingContext :: Context'
startingContext = Context
  { typeFind = Map.empty
  , typeOrder = []

  , tvarMap = Map.empty

  , varFind = Map.empty
  , conFind = Map.empty

  , functions = Map.empty
  , constructors = Map.empty
  }
