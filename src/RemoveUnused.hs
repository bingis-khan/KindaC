{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
module RemoveUnused (removeUnused) where

import qualified AST.Typed as T
import Misc.Memo (Memo, memo, emptyMemo)
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Bitraversable (bitraverse)
import AST.Common (Annotated(..), type (:.) (..), Locality (..), UniqueVar, EnvID, ctx, ppMap, ppEnvID)
import Data.Set (Set)
import Data.Bifoldable (bifold)
import Data.Foldable (Foldable(..))
import Data.Map (Map, (!?))
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Traversable (for)
import Data.Maybe (catMaybes, fromJust)
import Control.Monad.Trans.RWS (RWS)
import Control.Applicative (liftA3)
import Control.Monad ((<=<))
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Fix (Fix(..))
import Data.List (find)
import qualified Control.Monad.Trans.RWS as RWS
import Debug.Trace (traceShow, trace)
import Data.Bifunctor (bimap)


-- 30.12.24: wait, what did i need it for??? i forgot...
-- ah, right. if a function is not called (not reachable) remove other variables (from the environment) that are refernced only by unused functions
--  we do this by remapping environments.

removeUnused :: [T.AnnStmt] -> [T.AnnStmt]
removeUnused stmts =
  -- phase 1: create new environments.
  let (_, envs) = State.runState (rScope stmts) mempty

  -- phase 2: substitute environments.
      (nuStmts, _) = RWS.evalRWS (sScope stmts) envs emptyMemo
  in trace (ctx ppMap $ bimap ppEnvID T.tEnv <$> Map.toList envs)  nuStmts


--- PHASE 1: Create filtered environments.

rScope :: Traversable t => t T.AnnStmt -> Reach
rScope = fmap fold <$> traverse rStmt

rStmt :: T.AnnStmt -> Reach
rStmt = cata $ \(O (Annotated _ stmt)) -> do
  stmt' <- bitraverse rExpr id stmt
  let ss = bifold stmt'
  pure ss

rExpr :: T.Expr -> Reach
rExpr = cata $ \(T.TypedExpr t te) -> case te of
  T.Var loc v -> case v of
    T.DefinedFunction fun -> do
      -- when a function is directly referenced, we know it's reachable inside its current scope, so we add it as used
      usedInsideFunction <- rFunction fun
      (usedInsideFunction <>) <$> used (T.DefinedFunction fun) t
    T.DefinedVariable uv -> if loc == FromEnvironment then used (T.DefinedVariable uv) t else pure Set.empty

  T.Con envID _ -> do 
    let emptyEnv = T.Env envID []
    State.modify $ Map.insert envID emptyEnv
    pure mempty

  T.Lam env _ ret -> withEnv env ret

  e -> fold <$> sequenceA e

rFunction :: T.Function -> Reach
rFunction fun = withEnv fun.functionDeclaration.functionEnv $ rScope fun.functionBody


used :: T.Variable -> T.Type -> Reach
used v t = pure $ Set.singleton (v, t)

withEnv :: T.Env -> Reach -> Reach
withEnv env r = do
  usedVars <- r
  let nuEnv = case env of
        -- we can let it go, but it shouldn't happen!!
        T.RecursiveEnv eid _ -> error $ "[COMPILER ERROR] An environment assigned to a function was a recursive env. Technically shouldn't happen! [EnvID: " <> show eid <> "]"
        T.Env eid envContent -> do
          T.Env eid (filter (\(v, _, t) -> Set.member (v, t) usedVars) envContent)  -- we may optionally filter variables here to decrease the Set size.

  State.modify $ Map.insert (T.envID nuEnv) nuEnv
  pure usedVars


type Reach = State (Map EnvID T.Env) (Set (T.Variable, T.Type))


--- PHASE 2: Substitute them

sScope :: Mem [T.AnnStmt]
sScope stmts = fmap catMaybes $ for stmts $ cata $ \(O (Annotated anns stmt)) -> do
  stmt' <- bitraverse sExpr id stmt
  let 
    body :: NonEmpty (Maybe T.AnnStmt) -> NonEmpty T.AnnStmt
    body b = 
      let stmts = catMaybes $ NonEmpty.toList b
      in case stmts of
        [] -> Fix (O (Annotated [] T.Pass)) :| []
        (x:xs) -> x :| xs

  fmap2 (embed . O . Annotated anns) $ case stmt' of
    T.EnvDef env -> fmap2 T.EnvDef $ replace env

    -- we have to take care of eliminating stuff from bodies.
    T.If e ifTrue elseIfs else' -> pure $ Just $ T.If e (body ifTrue) (fmap2 body elseIfs) (body <$> else')
    T.Switch _ _ -> undefined

    s -> pure $ sequenceA s

sExpr :: Mem T.Expr
sExpr = transverse $ \(T.TypedExpr t expr) -> do
  t' <- sType t
  fmap (T.TypedExpr t') $ case expr of
    T.Var loc v -> T.Var loc <$> sVariable v
    T.Lam env params ret -> liftA3 T.Lam (mustReplace env) (traverse2 sType params) ret
    T.As e at -> liftA2 T.As e (sType at)
    T.Con envID con -> T.Con envID <$> sDataCon con
    e -> sequenceA e

sType :: Mem T.Type
sType = cata $ fmap embed . \case
  T.TCon dd params unions -> liftA3 T.TCon (sDataDef dd) (sequenceA params) (traverse (sUnion <=< sequenceA) unions)
  T.TFun union args ret -> liftA3 T.TFun ((sUnion <=< sequenceA) union) (sequenceA args) ret
  t -> sequenceA t

sUnion :: Mem T.EnvUnion
sUnion union = do
  nuEnvs <- catMaybes <$> traverse replace union.union
  pure $ union { T.union = nuEnvs }

sVariable :: Mem T.Variable
sVariable (T.DefinedVariable v) = pure $ T.DefinedVariable v
sVariable (T.DefinedFunction fn) = T.DefinedFunction <$> liftA2 T.Function (sFunDec fn.functionDeclaration) (sBody fn.functionBody)

sFunDec :: Mem T.FunDec
sFunDec fd = do
  env <- mustReplace fd.functionEnv
  params <- traverse2 sType fd.functionParameters
  ret <- sType fd.functionReturnType
  pure $ fd { T.functionEnv = env, T.functionParameters = params, T.functionReturnType = ret }

sBody :: Mem (NonEmpty T.AnnStmt)
sBody stmts = do
  stmts' <- sScope $ NonEmpty.toList stmts
  pure $ case stmts' of
    [] -> Fix (O (Annotated [] T.Pass)) :| []
    (x:xs) -> x :| xs


sDataDef :: Mem T.DataDef
sDataDef = memo id const $ \(T.DD uv tvs dcs anns) addMemo -> mdo
  let dd = T.DD uv tvs dcs' anns
  addMemo dd

  dcs' <- for dcs $ \(T.DC _ uc ts canns) -> do
    ts' <- traverse sType ts
    pure $ T.DC dd uc ts' canns

  pure dd

sDataCon :: Mem T.DataCon
sDataCon (T.DC dd uc _ _) = do
  (T.DD _ _ cons _) <- sDataDef dd
  pure $ fromJust $ find (\(T.DC _ suc _ _) -> suc == uc) cons


mustReplace :: Mem T.Env
mustReplace = fmap fromJust . replace

replace :: T.Env -> Mem' (Maybe T.Env)
replace env = do
  let eid = T.envID env
  envs <- RWS.ask
  pure $ envs !? eid


type Mem t = t -> Mem' t
type Mem' = RWS (Map EnvID T.Env) () (Memo T.DataDef T.DataDef)


fmap2 :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
fmap2 = fmap . fmap

traverse2 :: (Applicative f, Traversable t1, Traversable t2) => (a -> f b) -> t1 (t2 a) -> f (t1 (t2 b))
traverse2 = traverse . traverse
