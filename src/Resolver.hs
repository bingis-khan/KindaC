{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
module Resolver (resolve, ResolveError) where

import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Foldable (fold)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map)
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map

import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Applicative ((<|>))
import Control.Monad (when)
import Data.Set (Set)
import Data.Bifoldable (bifoldMap)
import qualified Data.Set as Set

import AST.Common (Module, AnnStmt, Expr, Type, UniqueVar (..), UniqueCon (..), UniqueType (..), Mutability (..), Locality (..), VarName, TCon, ConName, Annotated (..))
import AST.Converged (Prelude(..))
import qualified AST.Converged as Prelude
import AST.Untyped (Untyped, StmtF (..), DataDef (..), DataCon (..), FunDec (..), ExprF (..), TypeF (..))
import qualified AST.Untyped as U
import AST.Resolved (Resolved, Env (..))
import qualified AST.Resolved as R
import qualified AST.Typed as T
import Data.Fix (Fix(..))
import Data.Functor ((<&>))




-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> Module Untyped -> IO ([ResolveError], Module Resolved)
resolve mPrelude uMod = do
  let newState = maybe emptyState mkState mPrelude
  (rmod, errs) <- RWST.evalRWST (rMod uMod) () newState
  return (errs, rmod)


rMod :: Module Untyped -> Ctx (Module Resolved)
rMod (U.Mod stmts) = R.Mod <$> rStmts stmts

rStmts :: [AnnStmt Untyped] -> Ctx [AnnStmt Resolved]
rStmts = traverse -- traverse through the list with Ctx
  $ cata (fmap embed . (\(U.AnnStmt anns utStmt) -> R.AnnStmt anns <$> rStmt utStmt)) -- go through Stmt recursively with Ctx. cata (fmap embed . ...) is transverse without the forall type.
  where
    -- actual logic
    -- maybe try to generalize it if possible using traverse n shit
    stmt = pure . R.NormalStmt
    rStmt = \case
      Print e -> do
        re <- rExpr e
        stmt $ R.Print re
      Assignment name e -> do
        re <- rExpr e
        vid <- newVar Immutable name
        stmt $ R.Assignment vid re
      Pass -> stmt R.Pass
      MutDefinition name me -> do
        mre <- traverse rExpr me
        vid <- newVar Mutable name
        stmt $ R.MutDefinition vid mre
      MutAssignment name e -> do
        re <- rExpr e
        (_, vid) <- resolveVar name
        stmt $ R.MutAssignment vid re
      If cond ifTrue elseIfs elseBody -> do
        rcond <- rExpr cond
        rIfTrue <- scope $ sequenceA ifTrue
        rElseIfs <- traverse (\(c, b) -> do
          rc <- rExpr c
          tb <- rBody b
          pure (rc, tb)) elseIfs
        rElseBody <- traverse rBody elseBody
        stmt $ R.If rcond rIfTrue rElseIfs rElseBody
      ExprStmt e -> do
        re <- rExpr e
        stmt $ R.ExprStmt re
      Return e -> do
        mre <- traverse rExpr e
        re <- case mre of
          Just re -> pure re
          Nothing -> do
            uc <- unit
            pure $ Fix (R.Con uc)

        stmt $ R.Return re
      DataDefinition (DD tyName tyParams cons) -> do
        tid <- newType tyName
        rCons <- traverse (\(Annotated anns (DC cname ctys)) -> do
          cid <- newCon cname
          rConTys <- traverse rType ctys
          pure $ Annotated anns (R.DC cid rConTys)) cons
        pure $ R.DataDefinition $ R.DD tid tyParams rCons
      FunctionDefinition (FD name params ret) body -> do
        vid <- newVar Immutable name
        (rparams, rret, rbody) <- closure $ do
          rparams <- traverse (\(n, t) -> do
            rn <- newVar Immutable n
            rt <- traverse rType t
            return (rn, rt)) params
          rret <- traverse rType ret
          rbody <- rBody body
          pure (rparams, rret, rbody)

        -- set the environment
        -- TODO: maybe just make it a part of 'closure'?
        let innerEnv = gatherVariables rbody
        env <- 
          -- traceShowId <$> 
          mkEnv (
            -- traceShowWith (\ienv -> show vid <> show " " <> show ienv)
            innerEnv)

        pure $ R.FunctionDefinition (R.FD env vid rparams rret) rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA


rExpr :: Expr Untyped -> Ctx (Expr Resolved)
rExpr = cata $ fmap embed . \case  -- transverse, but unshittified
  Lit x -> pure $ R.Lit x
  Var v -> do
    (l, vid) <- resolveVar v
    pure $ R.Var l vid
  Con conname -> do
    con <- resolveCon conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor conname
        placeholderCon conname

    pure $ R.Con con
  Op l op r -> R.Op <$> l <*> pure op <*> r
  Call c args -> R.Call <$> c <*> sequenceA args
  As e t -> R.As <$> e <*> rType t
  Lam params body -> do
    (rParams, rBody) <- closure $ do
      rParams <- traverse (newVar Immutable) params
      rBody <- scope body
      pure (rParams, rBody)

    let innerEnv = gatherVariablesFromExpr rBody  -- TODO: environment making in 'closure' function.
    env <- mkEnv innerEnv
    pure $ R.Lam env rParams rBody


rType :: Type Untyped -> Ctx (Type Resolved)
rType = transverse $ \case
  TCon t tapps -> do
    rt <- resolveType t
    rtApps <- sequenceA tapps
    pure $ R.TCon rt rtApps
  TVar v -> pure $ R.TVar v
  TFun args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ R.TFun rArgs rret


------------
-- Utility
------------

scope :: Ctx a -> Ctx a
scope x = do
  -- Enter scope
  oldScope <- RWST.get  -- enter scope
  x' <- x               -- evaluate body
  RWST.put oldScope     -- exit scope

  return x'

closure :: Ctx a -> Ctx a
closure x = do
  oldScope <- RWST.get          -- enter scope

  RWST.modify $ \state@(CtxState { scopes = scopes }) -> state { scopes = emptyScope <| fmap (\scope -> scope -- set all reachable variables as immutable
    { varScope = fmap (\v -> v { mutability = Immutable } :: UniqueVar) scope.varScope
    }) scopes }
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] CtxState IO  -- I might add additional context later.

data CtxState = CtxState
  { scopes :: NonEmpty Scope
  , prelude :: Maybe Prelude  -- Only empty when actually parsing prelude.
  }

data Scope = Scope
  { varScope :: Map VarName UniqueVar
  , conScope :: Map ConName UniqueCon
  , tyScope :: Map TCon UniqueType
  }

emptyState :: CtxState
emptyState =
  CtxState { scopes = NonEmpty.singleton emptyScope, prelude = Nothing }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty }

getScopes :: Ctx (NonEmpty Scope)
getScopes = RWST.gets scopes

-- Add later after I do typechecking.
mkState :: Prelude -> CtxState
mkState prelude = CtxState
  { scopes = NonEmpty.singleton scope
  , prelude = Just prelude
  } where
    scope = Scope
      { varScope = prelude.varNames <&> \case
          Left (T.FD _ uv _ _) -> uv
          Right (uv, _) -> uv
      , conScope = prelude.conNames <&> \(_, _, T.DC uc _) -> uc
      , tyScope = prelude.tyNames <&> \(T.DD ut _ _) -> ut
      }

    -- cons = Map.fromList $ fmap (\ci -> (ci.conName, ci)) $ foldMap extractCons $ T.fromMod prelude
    -- extractCons = \case
    --   Fix (T.AnnStmt _ (T.DataDefinition (T.DD _ _ dcons))) -> fmap (\(Annotated _ (T.DC con _)) -> con) dcons
    --   _ -> []

    -- types = Map.fromList $ mapMaybe extractTypes $ T.fromMod prelude
    -- extractTypes = \case
    --   Fix (T.AnnStmt _ (T.DataDefinition (T.DD tid _ _))) -> Just (tid.typeName, tid)
    --   _ -> Nothing

    -- -- right now, we're only taking functions and IMMUTABLE variables. not sure if I should include mutable ones
    -- vars = Map.fromList $ mapMaybe extractVars $ T.fromMod prelude
    -- extractVars = \case
    --   Fix (T.AnnStmt _ (T.Assignment v _)) -> Just (v.varName, v)
    --   Fix (T.AnnStmt _ (T.FunctionDefinition (T.FD _ v _ _) _)) -> Just (v.varName, v)
    --   _ -> Nothing


newVar :: Mutability -> VarName -> Ctx UniqueVar
newVar mut name = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = name, mutability = mut }
  modifyThisScope $ \sc -> sc { varScope = Map.insert name var sc.varScope }
  return var

resolveVar :: VarName -> Ctx (Locality, UniqueVar)
resolveVar name = do
  scopes <- getScopes
  case lookupScope name (fmap varScope scopes) of
    Just v -> pure v
    Nothing -> do
      err $ UndefinedVariable name
      (Local,) <$> placeholderVar name

placeholderVar :: VarName -> Ctx UniqueVar
placeholderVar name = do
  vid <- liftIO newUnique
  pure $ VI { varID = vid, varName = name, mutability = Mutable }  -- mutable, because we it might be a placeholder of a mutable assignment


newCon :: ConName -> Ctx UniqueCon
newCon name = do
  cid <- liftIO newUnique
  let con = CI { conID = cid, conName = name }
  modifyThisScope $ \sc -> sc { conScope = Map.insert name con sc.conScope }
  pure con

resolveCon :: ConName -> Ctx (Maybe UniqueCon)
resolveCon name = do
  scopes <- getScopes
  -- This has been generalized to return Maybe instead of throwing an error.
  --   WHY? I needed this function somewhere else AND I the usage should be the same.
  --    This is more in line with the spiritual usage of Haskell - bubble up errors and handle them there. this makes it obvious what is happening with the value - no need to check inside the function. (remember this :3)
  let maybeCon = snd <$> lookupScope name (fmap conScope scopes)
  pure maybeCon

placeholderCon :: ConName -> Ctx UniqueCon
placeholderCon name = do
  cid <- liftIO newUnique
  pure $ CI { conID = cid, conName = name }


newType :: TCon -> Ctx UniqueType
newType name = do
  -- Check for duplication first
  -- if it exists, we still replace it, but an error is signaled.
  scope <- NonEmpty.head <$> getScopes
  when (name `Map.member` scope.tyScope) $
    err $ TypeRedeclaration name

  -- Generate a new unique type.
  tid <- liftIO newUnique
  let ty = TI { typeID = tid, typeName = name }
  modifyThisScope $ \sc -> sc { tyScope = Map.insert name ty sc.tyScope }
  pure ty

resolveType :: TCon -> Ctx UniqueType
resolveType name = do
  scopes <- getScopes
  case lookupScope name (fmap tyScope scopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedType name
      placeholderType name

placeholderType :: TCon -> Ctx UniqueType
placeholderType name = do
  tid <- liftIO newUnique
  pure $ TI { typeID = tid, typeName = name }

modifyThisScope :: (Scope -> Scope) -> Ctx ()
modifyThisScope f =
  let modifyFirstScope (sc :| scs) = f sc :| scs
  in RWST.modify $ \sctx -> sctx { scopes = modifyFirstScope sctx.scopes }

lookupScope :: (Ord b) => b -> NonEmpty (Map b c) -> Maybe (Locality, c)
lookupScope k = foldr (\(locality, l) r -> (locality,) <$> Map.lookup k l <|> r) Nothing . (\(cur :| envs) -> (Local, cur) :| fmap (FromEnvironment,) envs)

unit :: Ctx UniqueCon
unit = do
  ctx <- RWST.get
  case ctx.prelude of
    -- When prelude was already typechecked, it should always be available.
    Just prelud -> pure $ fst prelud.unitValue

    -- When we're resolving prelude, find it from the environment.
    Nothing ->
      resolveCon Prelude.unitName <&> \case
        Just uc -> uc
        Nothing -> error $ "[COMPILER ERROR]: Could not find Unit type with the name: '" <> show Prelude.unitName <> "'. This must not happen."

err :: ResolveError -> Ctx ()
err = RWST.tell .  (:[])

data ResolveError
  = UndefinedVariable VarName
  | UndefinedConstructor ConName
  | UndefinedType TCon
  | TypeRedeclaration TCon
  deriving Show


-- environment stuff
mkEnv :: Set UniqueVar -> Ctx Env
mkEnv innerEnv = do
  scope <- getScopes

  -- gather elements in current scope (we assume we are just "outside" of the env we compare it with)
  let outerEnv = foldMap (Set.fromList . Map.elems. varScope) scope
  pure $ Env $ Set.toList $ (
    -- traceShowId 
    outerEnv) `Set.intersection` innerEnv

-- used for function definitions
gatherVariables :: NonEmpty (AnnStmt Resolved) -> Set UniqueVar
gatherVariables = foldMap $ cata $ \(R.AnnStmt _ bstmt) -> case bstmt of
  R.DataDefinition _ -> mempty
  R.FunctionDefinition _ vars -> fold vars
  stmt -> bifoldMap gatherVariablesFromExpr id stmt

-- used for lambdas
gatherVariablesFromExpr :: Expr Resolved -> Set UniqueVar
gatherVariablesFromExpr = cata $ \case
  R.Var _ v -> Set.singleton v  -- TODO: Is this... correct? It's used for making the environment, but now we can just use this variable to know. This is todo for rewrite.
  expr -> fold expr
