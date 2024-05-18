{-# LANGUAGE LambdaCase, OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Resolver (resolve, ResolveError) where

import AST
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse)
import Data.Text (Text)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map)
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map



-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Module Untyped -> IO ([ResolveError], Module Resolved)
resolve uStmts = do
  (rMod, errs) <- RWST.evalRWST (rStmts uStmts) () (Scope { varScope = mempty, conScope = mempty, tyScope = mempty })
  return (errs, rMod)


rStmts :: [AnnStmt Untyped] -> Ctx [AnnStmt Resolved]
rStmts = traverse -- traverse through the list with Ctx
  $ transverse (\(AnnStmt anns utStmt) -> AnnStmt anns <$> rStmt utStmt) -- go through Stmt recursively with Ctx
  where
    -- actual logic
    rStmt = \case
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
        vid <- resolveVar name
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
        re <- rExpr e
        pure $ Return re
      DataDefinition (DD tyName tyParams cons) -> do
        tid <- newType tyName
        rCons <- traverse (\(DC cname ctys anns) -> do
          cid <- newCon cname
          rConTys <- traverse rType ctys
          pure $ DC cid rConTys anns) cons
        pure $ DataDefinition $ DD tid tyParams rCons
      FunctionDefinition (FD name params ret) body -> do
        vid <- newVar Immutable name
        closure $ do
          rparams <- traverse (\(n, t) -> do
            rn <- newVar Immutable n
            rt <- traverse rType t
            return (rn, rt)) params
          rret <- traverse rType ret
          rbody <- rBody body
          pure $ FunctionDefinition (FD vid rparams rret) rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA


rExpr :: Expr Untyped -> Ctx (Expr Resolved)
rExpr = transverse $ \case
  Lit x -> pure $ Lit x
  Var v -> Var <$> resolveVar v
  Con c -> Con <$> resolveCon c
  Op l op r -> Op <$> l <*> pure op <*> r
  Call c args -> Call <$> c <*> sequenceA args
  As e t -> As <$> e <*> rType t
  Lam params body -> closure $ do
    rParams <- traverse (newVar Immutable) params
    rBody <- scope body
    pure $ Lam rParams rBody


rType :: Type Untyped -> Ctx (Type Resolved)
rType = transverse $ \case
  TCon t tapps -> do
    rt <- resolveType t
    rtApps <- sequenceA tapps
    pure $ TCon rt rtApps
  TVar v -> pure $ TVar v
  TFun args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ TFun rArgs rret


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
  RWST.modify $ \scope -> scope -- set all reachable variables as immutable
    { varScope = fmap (\v -> v { varType = Immutable }) scope.varScope
    }
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] Scope IO  -- I might add additional context later.

data Scope = Scope
  { varScope :: Map Text VarInfo
  , conScope :: Map Text ConInfo
  , tyScope :: Map Text TypeInfo
  }



newVar :: VarType -> Text -> Ctx VarInfo
newVar mut name = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = name, varType = mut }
  RWST.modify $ \sc -> sc { varScope = Map.insert name var sc.varScope }
  return var

resolveVar :: Text -> Ctx VarInfo
resolveVar name = do
  scope <- RWST.get
  case Map.lookup name scope.varScope of
    Just v -> pure v
    Nothing -> do
      err $ UndefinedVariable name
      placeholderVar name

placeholderVar :: Text -> Ctx VarInfo
placeholderVar name = do
  vid <- liftIO newUnique
  pure $ VI { varID = vid, varName = name, varType = Mutable }  -- mutable, because we it might be a placeholder of a mutable assignment


newCon :: Text -> Ctx ConInfo
newCon name = do
  cid <- liftIO newUnique
  let con = CI { conID = cid, conName = name }
  RWST.modify $ \sc -> sc { conScope = Map.insert name con sc.conScope }
  pure con

resolveCon :: Text -> Ctx ConInfo
resolveCon name = do
  scope <- RWST.get
  case Map.lookup name scope.conScope of
    Just c -> pure c
    Nothing -> do
      err $ UndefinedConstructor name
      placeholderCon name

placeholderCon :: Text -> Ctx ConInfo
placeholderCon name = do
  cid <- liftIO newUnique
  pure $ CI { conID = cid, conName = name }


newType :: Text -> Ctx TypeInfo
newType name = do
  tid <- liftIO newUnique
  let ty = TI { typeID = tid, typeName = name }
  RWST.modify $ \sc -> sc { tyScope = Map.insert name ty sc.tyScope }
  pure ty

resolveType :: Text -> Ctx TypeInfo
resolveType name = do
  scope <- RWST.get
  case Map.lookup name scope.tyScope of
    Just c -> pure c
    Nothing -> do
      err $ UndefinedType name
      placeholderType name

placeholderType :: Text -> Ctx TypeInfo
placeholderType name = do
  tid <- liftIO newUnique
  pure $ TI { typeID = tid, typeName = name }



err :: ResolveError -> Ctx ()
err = RWST.tell .  (:[])

data ResolveError
  = UndefinedVariable Text
  | UndefinedConstructor Text
  | UndefinedType Text
  deriving Show
