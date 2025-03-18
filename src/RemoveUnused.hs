{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedStrings #-}
module RemoveUnused (removeUnused) where

import qualified AST.Typed as T
import Misc.Memo (Memo, memo, emptyMemo)
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Bitraversable (bitraverse)
import AST.Common (Annotated(..), type (:.) (..), Locality (..), EnvID, fmap2, traverse2, eitherToMaybe)
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
import Data.Functor ((<&>))



-- 30.12.24: wait, what did i need it for??? i forgot...
-- ah, right. if a function is not called (not reachable) remove other variables (from the environment) that are refernced only by unused functions
--  we do this by remapping environments.
-- 13.03.25 update: I should probably put this logic in the monomorphisation module. To know which environments and which instance functions end up being used, we have to apply it... i guess? It might be easier.

removeUnused :: [T.AnnStmt] -> [T.AnnStmt]
removeUnused stmts =
  -- phase 1: create new environments.
  let (_, envs, _) = RWS.runRWS (rScope stmts) mempty mempty

  -- phase 2: substitute environments.
      (nuStmts, _) = RWS.evalRWS (sScope stmts) envs emptyMemo
  in nuStmts --trace (ctx ppMap $ bimap ppEnvID T.tEnv <$> Map.toList envs)  nuStmts



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
    T.DefinedFunction fun insts -> do
      -- when a function is directly referenced, we know it's reachable inside its current scope, so we add it as used
      usedInsideFunction <- rFunction fun
      (usedInsideFunction <>) <$> used (T.DefinedFunction fun insts) t
    T.DefinedVariable uv -> if loc == FromEnvironment then used (T.DefinedVariable uv) t else pure Set.empty
    T.DefinedClassFunction cfd insts self -> do
      let (selectedFn, _) = T.selectInstanceFunction cfd self insts
      usedInsideFunction <- rFunction selectedFn.instFunction

      usedInstanceFunction <- used (T.DefinedFunction selectedFn.instFunction mempty) t
      usedClassFunction <- used (T.DefinedClassFunction cfd insts self) t
      pure $ usedInsideFunction <> usedInstanceFunction <> usedClassFunction

  T.Con envID _ -> do
    let emptyEnvMask = []
    RWS.modify $ Map.insert envID emptyEnvMask
    pure mempty

  T.Lam env _ ret -> withEnv env ret

  e -> fold <$> sequenceA e



rFunction :: T.Function -> Reach
rFunction fun = withEnv fun.functionDeclaration.functionEnv $ withInstances undefined $ rScope fun.functionBody


used :: T.Variable -> T.Type -> Reach
used v t = pure $ Set.singleton (v, t)

withInstances :: Map T.TVar (Map T.ClassDef T.InstDef) -> Reach -> Reach
withInstances tvm = RWS.local (Map.union tvm)

withEnv :: T.Env -> Reach -> Reach
withEnv env r = do
  usedVars <- r
  let (eid, mask) = case env of
        -- we can let it go, but it shouldn't happen!!
        T.RecursiveEnv teid _ -> error $ "[COMPILER ERROR] An environment assigned to a function was a recursive env. Technically shouldn't happen! [EnvID: " <> show teid <> "]"
        T.Env teid envContent -> do
          (teid, envContent <&> \(v, _, t) -> Set.member (v, t) usedVars)

  RWS.modify $ Map.insert eid mask
  pure usedVars


type Reach = RWS (Map T.TVar (Map T.ClassDef T.InstDef)) () (Map EnvID EnvMask) (Set (T.Variable, T.Type))

-- KEKEKEKEKEKKEK THIS IS SO RETARDED BUT IT MIGHT JUST WORK
-- because environments can escape out of the context, mapping them is the wrong way to go, because they might be instantiated.
-- instead, create a "BitMask" to know which parts of the environment to remove.
type EnvMask = [Bool]



--- PHASE 2: Substitute them

sScope :: Mem [T.AnnStmt]
sScope stmts = fmap catMaybes $ for stmts $ cata $ \(O (Annotated anns stmt)) -> do
  stmt' <- bitraverse sExpr id stmt
  let
    body :: NonEmpty (Maybe T.AnnStmt) -> NonEmpty T.AnnStmt
    body b =
      let bstmts = catMaybes $ NonEmpty.toList b
      in case bstmts of
        [] -> Fix (O (Annotated [] T.Pass)) :| []
        (x:xs) -> x :| xs

  fmap2 (embed . O . Annotated anns) $ case stmt' of
    -- if an environment is not used, remove it.
    T.EnvDef fn -> fmap2 (T.EnvDef . (\env -> fn {T.functionDeclaration = fn.functionDeclaration { T.functionEnv = env }})) $ replace fn.functionDeclaration.functionEnv

    T.InstDefDef inst -> do
      fns <- traverse (\ifn -> fmap2 (\env -> ifn { T.instFunction = ifn.instFunction { T.functionDeclaration = ifn.instFunction.functionDeclaration { T.functionEnv = env } } }) $ replace ifn.instFunction.functionDeclaration.functionEnv) inst.instFunctions
      case catMaybes fns of
        [] -> pure Nothing
        (f:fs) -> pure $ Just $ T.InstDefDef $ inst { T.instFunctions = f:fs }  --sequenceA fns <&> undefined

    -- we have to take care of eliminating stuff from bodies.
    T.If e ifTrue elseIfs else' -> pure $ Just $ T.If e (body ifTrue) (fmap2 body elseIfs) (body <$> else')
    T.Switch e cases -> pure $ Just $ T.Switch e $ cases <&> \kase -> kase { T.body = body kase.body }

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
sVariable (T.DefinedFunction fn insts) = T.DefinedFunction <$> liftA2 T.Function (sFunDec fn.functionDeclaration) (sBody fn.functionBody) <*> pure insts
sVariable (T.DefinedClassFunction cfd insts self) = do
  T.DefinedClassFunction cfd <$> traverse sInst insts <*> sType self

sInst :: Mem T.InstDef
sInst inst = do
  dds <- sDataDef $ fst inst.instType
  fns <- for inst.instFunctions $ \ifn -> do
    tfn <- liftA2 T.Function (sFunDec ifn.instFunction.functionDeclaration) (sBody ifn.instFunction.functionBody)
    let tifn = ifn { T.instFunction = tfn }
    pure tifn

  pure T.InstDef
    { T.instClass = inst.instClass
    , T.instType = (dds, snd inst.instType)
    , T.instFunctions = fns
    }


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
sDataDef = memo id const $ \(T.DD uv tvs edcs anns) addMemo -> mdo
  let dd = T.DD uv tvs dcs' anns
  addMemo dd

  dcs' <- case edcs of
    Right dcs -> fmap Right $ for dcs $ \(T.DC _ uc ts canns) -> do
      ts' <- traverse sType ts
      pure $ T.DC dd uc ts' canns

    Left drs -> fmap Left $ for drs $ \(T.DR _ memname t canns) -> do
      t' <- sType t
      pure $ T.DR dd memname t' canns

  pure dd


sDataCon :: Mem T.DataCon
sDataCon (T.DC dd uc _ _) = do
  (T.DD _ _ cons _) <- sDataDef dd
  pure $ fromJust  -- now force it, because it *must* be a constructor.
    $ find (\(T.DC _ suc _ _) -> suc == uc)  -- then find it.
    =<< eitherToMaybe cons  -- we know it's a constructor (Right is constructor, Left is record), so eitherToMaybe -> rightToMaybe



mustReplace :: Mem T.Env
mustReplace = fmap fromJust . replace

-- TODO: i modified it. I should add test cases for why I implemented this module. (See my master's thesis. i literally forgot kekekkekekekekkekekekek i wanna kms)
replace :: T.Env -> Mem' (Maybe T.Env)
replace env = do
  let eid = T.envID env
  envs <- RWS.ask
  pure $ applyEnvMask env <$> (envs !? eid)


applyEnvMask :: T.Env -> EnvMask -> T.Env
applyEnvMask (T.RecursiveEnv _ _) _ = error "[COMPILER ERROR: RemoveUnused] Recursive envs not yet supported (probably a noop in the future!)"
applyEnvMask (T.Env eid content) mask =
  let maskedContent = map fst $ filter snd $ zip content mask
  in T.Env eid maskedContent



type Mem t = t -> Mem' t
type Mem' = RWS (Map EnvID EnvMask) () (Memo T.DataDef T.DataDef)


