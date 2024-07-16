{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
module Resolver (resolve, ResolveError) where

import AST
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Foldable (fold)
import Data.Text (Text)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map)
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map

import Data.Maybe (mapMaybe)
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Applicative ((<|>))
import Control.Monad (when)
import Data.Set (Set)
import Data.Bifoldable (bifoldMap)
import qualified Data.Set as Set



-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> Module Untyped -> IO ([ResolveError], Module Resolved)
resolve mPrelude uStmts = do
  let newScope = maybe emptyScope mkScope mPrelude
  (rMod, errs) <- RWST.evalRWST (rStmts uStmts) () (NonEmpty.singleton newScope)
  return (errs, rMod)


rStmts :: [AnnStmt Untyped] -> Ctx [AnnStmt Resolved]
rStmts = traverse -- traverse through the list with Ctx
  $ cata (fmap embed . (\(AnnStmt anns utStmt) -> AnnStmt anns <$> rStmt utStmt)) -- go through Stmt recursively with Ctx. cata (fmap embed . ...) is transverse without the forall type.
  where
    -- actual logic
    -- maybe try to generalize it if possible using traverse n shit
    rStmt = \case
      NormalStmt stmt -> NormalStmt <$> case stmt of
        Print e -> do
          re <- rExpr e
          pure $ Print re
        Assignment name e -> do
          vid <- newVar Immutable name
          re <- rExpr e
          pure $ Assignment vid re
        Pass -> pure Pass
        MutDefinition name me -> do
          vid <- newVar Mutable name
          mre <- traverse rExpr me
          pure $ MutDefinition vid mre
        MutAssignment name e -> do
          (_, vid) <- resolveVar name
          re <- rExpr e
          pure $ MutAssignment vid re
        If cond ifTrue elseIfs elseBody -> do
          rcond <- rExpr cond
          rIfTrue <- scope $ sequenceA ifTrue
          rElseIfs <- traverse (\(c, b) -> do
            rc <- rExpr c
            tb <- rBody b
            pure (rc, tb)) elseIfs
          rElseBody <- traverse rBody elseBody
          pure $ If rcond rIfTrue rElseIfs rElseBody
        ExprStmt e -> do
          re <- rExpr e
          pure $ ExprStmt re
        Return e -> do
          re <- traverse rExpr e
          pure $ Return re
      DataDefinition (DD tyName tyParams cons) -> do
        tid <- newType tyName
        rCons <- traverse (\(DC cname ctys anns) -> do
          cid <- newCon cname
          rConTys <- traverse rType ctys
          pure $ DC cid rConTys anns) cons
        pure $ DataDefinition $ DD tid tyParams rCons
      FunctionDefinition (FD name params _ ret) body -> do
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

        pure $ FunctionDefinition (FD vid rparams env rret) rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA


rExpr :: Expr Untyped -> Ctx (Expr Resolved)
rExpr = cata $ fmap embed . \case  -- transverse, but unshittified
  Lit x -> pure $ Lit x
  Var () v -> do
    (l, vid) <- resolveVar v
    pure $ Var l vid
  Con c -> Con <$> resolveCon c
  Op l op r -> Op <$> l <*> pure op <*> r
  Call c args -> Call <$> c <*> sequenceA args
  As e t -> As <$> e <*> rType t
  Lam _ params body -> do
    (rParams, rBody) <- closure $ do
      rParams <- traverse (newVar Immutable) params
      rBody <- scope body
      pure (rParams, rBody)

    let innerEnv = gatherVariablesFromExpr rBody  -- TODO: environment making in 'closure' function.
    env <- mkEnv innerEnv
    pure $ Lam env rParams rBody


rType :: Type Untyped -> Ctx (Type Resolved)
rType = transverse $ \case
  TCon t tapps -> do
    rt <- resolveType t
    rtApps <- sequenceA tapps
    pure $ TCon rt rtApps
  TVar v -> pure $ TVar v
  TFun _ args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ TFun (TNoEnv ()) rArgs rret


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
    { varScope = fmap (\v -> v { varType = Immutable } :: VarInfo) scope.varScope
    }) scopes
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] (NonEmpty Scope) IO  -- I might add additional context later.

data Scope = Scope
  { varScope :: Map Text VarInfo
  , conScope :: Map Text ConInfo
  , tyScope :: Map Text TypeInfo
  }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty }

mkScope :: Prelude -> Scope
mkScope prelude = Scope
  { varScope = mempty
  , conScope = cons
  , tyScope = types
  } where
    cons = Map.fromList $ fmap (\ci -> (ci.conName, ci)) $ foldMap extractCons prelude
    extractCons = \case
      Fix (AnnStmt _ (DataDefinition (DD _ _ dcons))) -> fmap (\(DC con _ _) -> con) dcons
      _ -> []

    types = Map.fromList $ mapMaybe extractTypes prelude
    extractTypes = \case
      Fix (AnnStmt _ (DataDefinition (DD tid _ _))) -> Just (tid.typeName, tid)
      _ -> Nothing


newVar :: VarType -> Text -> Ctx VarInfo
newVar mut name = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = name, varType = mut }
  RWST.modify $ mapFirst $ \sc -> sc { varScope = Map.insert name var sc.varScope }
  return var

resolveVar :: Text -> Ctx (Locality, VarInfo)
resolveVar name = do
  scopes <- RWST.get
  case lookupScope name (fmap varScope scopes) of
    Just v -> pure v
    Nothing -> do
      err $ UndefinedVariable name
      (Local,) <$> placeholderVar name

placeholderVar :: Text -> Ctx VarInfo
placeholderVar name = do
  vid <- liftIO newUnique
  pure $ VI { varID = vid, varName = name, varType = Mutable }  -- mutable, because we it might be a placeholder of a mutable assignment


newCon :: Text -> Ctx ConInfo
newCon name = do
  cid <- liftIO newUnique
  let con = CI { conID = cid, conName = name }
  RWST.modify $ mapFirst $ \sc -> sc { conScope = Map.insert name con sc.conScope }
  pure con

resolveCon :: Text -> Ctx ConInfo
resolveCon name = do
  scopes <- RWST.get
  case lookupScope name (fmap conScope scopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedConstructor name
      placeholderCon name

placeholderCon :: Text -> Ctx ConInfo
placeholderCon name = do
  cid <- liftIO newUnique
  pure $ CI { conID = cid, conName = name }


newType :: Text -> Ctx TypeInfo
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

resolveType :: Text -> Ctx TypeInfo
resolveType name = do
  scopes <- RWST.get
  case lookupScope name (fmap tyScope scopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedType name
      placeholderType name

placeholderType :: Text -> Ctx TypeInfo
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
  = UndefinedVariable Text
  | UndefinedConstructor Text
  | UndefinedType Text
  | TypeRedeclaration Text
  deriving Show


-- environment stuff
mkEnv :: Set VarInfo -> Ctx (VarEnv VarInfo t)
mkEnv innerEnv = do
  scope <- RWST.get

  -- gather elements in current scope (we assume we are just "outside" of the env we compare it with)
  let outerEnv = foldMap (Set.fromList . Map.elems. varScope) scope
  pure $ VarEnv $ Set.toList $ outerEnv `Set.intersection` innerEnv

-- used for function definitions
gatherVariables :: NonEmpty (AnnStmt Resolved) -> Set VarInfo
gatherVariables = foldMap $ cata $ \(AnnStmt _ bstmt) -> case bstmt of
  DataDefinition _ -> mempty
  FunctionDefinition _ vars -> fold vars
  NormalStmt stmt -> bifoldMap gatherVariablesFromExpr id stmt

-- used for lambdas
gatherVariablesFromExpr :: Expr Resolved -> Set VarInfo
gatherVariablesFromExpr = cata $ \case
  Var _ v -> Set.singleton v  -- TODO: Is this... correct? It's used for making the environment, but now we can just use this variable to know. This is todo for rewrite.
  expr -> fold expr
