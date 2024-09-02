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
import AST.Converged (Prelude)
import AST.Untyped (Untyped, StmtF (..), DataDef (..), DataCon (..), FunDec (..), ExprF (..), TypeF (..))
import qualified AST.Untyped as U
import AST.Resolved (Resolved, Env (..))
import qualified AST.Resolved as R




-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> Module Untyped -> IO ([ResolveError], Module Resolved)
resolve mPrelude uMod = do
  let newScope = maybe emptyScope undefined mPrelude
  (rmod, errs) <- RWST.evalRWST (rMod uMod) () (NonEmpty.singleton newScope)
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
        vid <- newVar Immutable name
        re <- rExpr e
        stmt $ R.Assignment vid re
      Pass -> stmt R.Pass
      MutDefinition name me -> do
        vid <- newVar Mutable name
        mre <- traverse rExpr me
        stmt $ R.MutDefinition vid mre
      MutAssignment name e -> do
        (_, vid) <- resolveVar name
        re <- rExpr e
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
        re <- traverse rExpr e
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
        env <- mkEnv innerEnv

        pure $ R.FunctionDefinition (R.FD env vid rparams rret) rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA


rExpr :: Expr Untyped -> Ctx (Expr Resolved)
rExpr = cata $ fmap embed . \case  -- transverse, but unshittified
  Lit x -> pure $ R.Lit x
  Var v -> do
    (l, vid) <- resolveVar v
    pure $ R.Var l vid
  Con c -> R.Con <$> resolveCon c
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
  RWST.modify $ \scopes -> emptyScope <| fmap (\scope -> scope -- set all reachable variables as immutable
    { varScope = fmap (\v -> v { mutability = Immutable } :: UniqueVar) scope.varScope
    }) scopes
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] (NonEmpty Scope) IO  -- I might add additional context later.

data Scope = Scope
  { varScope :: Map VarName UniqueVar
  , conScope :: Map ConName UniqueCon
  , tyScope :: Map TCon UniqueType
  }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty }

-- Add later after I do typechecking.
-- mkScope :: Prelude -> Scope
-- mkScope prelude = Scope
--   { varScope = vars
--   , conScope = cons
--   , tyScope = types
--   } where
--     cons = Map.fromList $ fmap (\ci -> (ci.conName, ci)) $ foldMap extractCons prelude
--     extractCons = \case
--       Fix (AnnStmt _ (DataDefinition (DD _ _ dcons))) -> fmap (\(DC con _) -> con) dcons
--       _ -> []

--     types = Map.fromList $ mapMaybe extractTypes prelude
--     extractTypes = \case
--       Fix (AnnStmt _ (DataDefinition (DD tid _ _))) -> Just (tid.typeName, tid)
--       _ -> Nothing

--     -- right now, we're only taking functions and IMMUTABLE variables. not sure if I should include mutable ones
--     vars = Map.fromList $ mapMaybe extractVars prelude
--     extractVars = \case
--       Fix (AnnStmt _ (Assignment v _)) -> Just (v.varName, v)
--       Fix (AnnStmt _ (FunctionDefinition (FD v _ _) _)) -> Just (v.varName, v)
--       _ -> Nothing


newVar :: Mutability -> VarName -> Ctx UniqueVar
newVar mut name = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = name, mutability = mut }
  RWST.modify $ mapFirst $ \sc -> sc { varScope = Map.insert name var sc.varScope }
  return var

resolveVar :: VarName -> Ctx (Locality, UniqueVar)
resolveVar name = do
  scopes <- RWST.get
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
  RWST.modify $ mapFirst $ \sc -> sc { conScope = Map.insert name con sc.conScope }
  pure con

resolveCon :: ConName -> Ctx UniqueCon
resolveCon name = do
  scopes <- RWST.get
  case lookupScope name (fmap conScope scopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedConstructor name
      placeholderCon name

placeholderCon :: ConName -> Ctx UniqueCon
placeholderCon name = do
  cid <- liftIO newUnique
  pure $ CI { conID = cid, conName = name }


newType :: TCon -> Ctx UniqueType
newType name = do
  -- Check for duplication first
  -- if it exists, we still replace it, but an error is signaled.
  scope <- RWST.gets NonEmpty.head
  when (name `Map.member` scope.tyScope) $
    err $ TypeRedeclaration name

  -- Generate a new unique type.
  tid <- liftIO newUnique
  let ty = TI { typeID = tid, typeName = name }
  RWST.modify $ mapFirst $ \sc -> sc { tyScope = Map.insert name ty sc.tyScope }
  pure ty

resolveType :: TCon -> Ctx UniqueType
resolveType name = do
  scopes <- RWST.get
  case lookupScope name (fmap tyScope scopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedType name
      placeholderType name

placeholderType :: TCon -> Ctx UniqueType
placeholderType name = do
  tid <- liftIO newUnique
  pure $ TI { typeID = tid, typeName = name }

mapFirst :: (a -> a) -> NonEmpty a -> NonEmpty a
mapFirst f (x :| xs) = f x :| xs

lookupScope :: (Ord b) => b -> NonEmpty (Map b c) -> Maybe (Locality, c)
lookupScope k = foldr (\(locality, l) r -> (locality,) <$> Map.lookup k l <|> r) Nothing . (\(cur :| envs) -> (Local, cur) :| fmap (FromEnvironment,) envs)


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
  scope <- RWST.get

  -- gather elements in current scope (we assume we are just "outside" of the env we compare it with)
  let outerEnv = foldMap (Set.fromList . Map.elems. varScope) scope
  pure $ Env $ Set.toList $ outerEnv `Set.intersection` innerEnv

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
