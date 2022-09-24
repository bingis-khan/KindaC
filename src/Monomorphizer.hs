{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Monomorphizer where

import AST
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Data.Map (Map, (!), (!?))
import qualified Data.Map as M
import Control.Monad.Trans.Reader (Reader, ask, runReader)
import Typecheck (Subst(..), apply)
import Data.Functor.Foldable (cata, Corecursive (embed), Recursive (project))
import Data.Fix (Fix(Fix))
import Data.Biapplicative (first, bimap)
import Data.Foldable (fold)
import Data.Bifoldable (bifold)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Graph (stronglyConnComp, SCC (..))
import Data.Either (rights)
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Tuple (swap)
import Control.Monad.Trans.Maybe (MaybeT(MaybeT, runMaybeT))
import Control.Monad.Trans.Class (lift)
import Debug.Trace (traceShowId)


type Funs = Reader (Map Global TFunDec)

-- Assumes this is the same type.
substitution :: TypedType -> TypedType -> Subst
substitution t t' = Subst $ go t t'
    where
        go :: TypedType -> TypedType -> Map TVar TypedType
        go (Fix (TCon t ts)) (Fix (TCon t' ts')) = mconcat $ zipWith go ts ts'
        go (Fix (TFun args ret)) (Fix (TFun args' ret')) = mconcat $ go ret ret' : zipWith go args args'
        go (Fix (TVar tv)) t = M.singleton tv t
        go (Fix (TDecVar tv)) t = M.singleton tv t
        go t (Fix (TVar tv)) = M.singleton tv t
        go t (Fix (TDecVar tv)) = M.singleton tv t
        go t t' = error $ "Not the same type:" ++ show t ++ " " ++ show t'


hoistMaybe = MaybeT . pure

findApplyFun :: MonoFunDec -> MaybeT Funs TFunDec
findApplyFun (MonoFunDec g t) = do
    funs <- lift ask
    fun@(FD _ params ret _) <- hoistMaybe $ funs !? g
    let subst = substitution (Fix (TFun (map snd params) ret)) t
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

collectApplyFun :: MonoFunDec -> MaybeT Funs (TFunDec, Set MonoFunDec)
collectApplyFun dec = do
    fun <- findApplyFun dec
    let calls' = calls fun
    return (fun, calls')

collectFuns :: [MonoFunDec] -> Map MonoFunDec (TFunDec, Set MonoFunDec) -> Funs (Map MonoFunDec (TFunDec, Set MonoFunDec))
collectFuns next callGraph = case filter (`M.notMember` callGraph) next of
  [] -> return callGraph
  call : next' -> do
    mFunCalls <- runMaybeT $ collectApplyFun call
    case mFunCalls of
      Nothing -> collectFuns next' callGraph
      Just (fun, calls) -> collectFuns (S.toList calls ++ next') (M.insert call (fun, calls) callGraph)

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


-- Gather types and declare them as structs.
class Typed a where
    gather :: a -> Set TypedType

instance Typed TypedType where
    gather = (\(t, t') -> S.insert t (fold t')) . (fmap . fmap) gather . (\t -> (t, project t))

instance Typed TExpr where
    gather = cata $ \(ExprType t exprs) -> S.insert t $ fold exprs

instance Typed TStmt where
    gather = cata $ bifold . first gather

instance Typed a => Typed [a] where
    gather = foldMap gather

instance Typed TFunDec where
    gather = bifold . bimap S.singleton gather

usedTypes :: Builtins -> Set TDataDec -> [TFunDec] -> [TStmt] -> [Either MonoDataDec (TDataDec, [TypedType])]
usedTypes (Builtins builtins _ _ _) dataDecs fds stmts =
    let
        dataDecMap = M.fromList $ map (\dd@(DD t _ _) -> (t, dd)) $ S.toList dataDecs
        builtinTypes = S.fromList $ M.elems builtins
        usedTypes = (gather fds <> gather stmts) \\ builtinTypes

        typeRefs :: TypedType -> Maybe (([TypedType], TDataDec), TypedType, [TypedType])
        typeRefs t@(Fix (TCon tid refs)) = Just ((refs, dataDecMap ! tid), t, refs)
        typeRefs _ = Nothing

        connections = stronglyConnComp $ mapMaybe typeRefs $ S.toList usedTypes

        structDecl :: SCC ([TypedType], TDataDec) -> [Either MonoDataDec (TDataDec, [TypedType])]
        structDecl (CyclicSCC dts) = map (\(ts, DD g _ _) -> Left (MonoDataDec g ts)) dts ++ map (Right . swap) dts
        structDecl (AcyclicSCC (ts, dt)) = [Right (dt, ts)]

        decsDefs = concatMap structDecl connections
    in decsDefs

monomorphize :: Builtins -> TModule -> ([Either MonoDataDec (TDataDec, [TypedType])], [Either MonoFunDec TFunDec], [TStmt])
monomorphize builtins (TModule funs dds tls) =
    let initial = bodyCalls tls
        collected = collect funs initial
        orderedDecls = toCallGraph $ stronglyConnComp collected

        types = usedTypes builtins dds (rights orderedDecls) tls
    in (types, orderedDecls, tls)
