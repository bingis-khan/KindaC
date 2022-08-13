{-# LANGUAGE LambdaCase #-}
module Monomorphizer where

import AST
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Data.Map (Map, (!))
import qualified Data.Map as M
import Control.Monad.Trans.Reader (Reader, ask, runReader)
import Typecheck (Subst(..), apply)
import Data.Functor.Foldable (cata)
import Data.Fix (Fix(Fix))
import Data.Biapplicative (first)
import Data.Foldable (fold)
import Data.Bifoldable (bifold)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Graph (stronglyConnComp, SCC (..))


type Funs = Reader (Map Global TFunDec)

-- Assumes this is the same type.
substitution :: TypedType -> TypedType -> Subst
substitution t t' = Subst $ go t t'
    where
        go :: TypedType -> TypedType -> Map TVar TypedType
        go (Fix (TCon t ts)) (Fix (TCon t' ts')) = mconcat $ zipWith go ts ts'
        go (Fix (TFun args ret)) (Fix (TFun args' ret')) = mconcat $ go ret ret' : zipWith go args args'
        go (Fix (TVar tv)) t = M.singleton tv t
        go (Fix (TCon _ _)) (Fix (TVar tv)) = M.singleton tv t
        go t t' = error $ show t ++ " " ++ show t'


findApplyFun :: MonoFunDec -> Funs TFunDec
findApplyFun (MonoFunDec g t) = do
    funs <- ask
    let fun@(FD _ params ret _) = funs ! g
        subst = substitution (Fix (TFun (map snd params) ret)) t
        monoFun = apply subst fun
    return monoFun

bodyCalls :: Foldable f => f TStmt -> Set MonoFunDec
bodyCalls = foldMap $ cata $ bifold . first expr
    where
        expr :: TExpr -> Set MonoFunDec
        expr = cata $ \case
            ExprType t (Var (Left g)) -> S.singleton (MonoFunDec g t)
            expr -> fold expr

calls :: TFunDec -> Set MonoFunDec
calls (FD _ _ _ body) = bodyCalls body

collectApplyFun :: MonoFunDec -> Funs (TFunDec, Set MonoFunDec)
collectApplyFun dec = do
    fun <- findApplyFun dec
    let calls' = calls fun
    return (fun, calls')

collectFuns :: [MonoFunDec] -> Map MonoFunDec (TFunDec, Set MonoFunDec) -> Funs (Map MonoFunDec (TFunDec, Set MonoFunDec))
collectFuns next callGraph = case filter (`M.notMember` callGraph) next of
  [] -> return callGraph
  call : next' -> do
    (fun, calls) <- collectApplyFun call
    collectFuns (S.toList calls ++ next') (M.insert call (fun, calls) callGraph)

collect :: Set TFunDec -> Set MonoFunDec -> [(TFunDec, MonoFunDec, [MonoFunDec])]
collect funs initial =
    let funMap = M.fromList $ map (\fun@(FD g _ _ _) -> (g, fun)) $ S.toList funs
        funCalls = runReader (collectFuns (S.toList initial) mempty) funMap
    in map (\(mfd, (fun, calls)) -> (fun, mfd, S.toList calls)) $ M.toList funCalls

toCallGraph :: [SCC TFunDec] -> [Either MonoFunDec TFunDec]
toCallGraph = concatMap $ \case
   AcyclicSCC fd -> pure $ Right fd
   CyclicSCC fds -> go mempty fds
    where
        go :: Set MonoFunDec -> [TFunDec] -> [Either MonoFunDec TFunDec]
        go declared [] = []
        go declared (fd : fds) =
            let mfd = toMonoFunDec fd
                declarations = S.fromList (map toMonoFunDec fds) \\ S.insert mfd declared
            in map Left (S.toList declarations) ++ [Right fd] ++ go (S.insert mfd (declared <> declarations)) fds

monomorphize :: TModule -> ([Either MonoFunDec TFunDec], [TStmt])
monomorphize (TModule funs dds tls) =
    let initial = bodyCalls tls
        collected = collect funs initial
    in (toCallGraph $ stronglyConnComp collected, tls)
