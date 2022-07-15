{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module TypecheckAdditional where

import AST

import Data.Set (Set, (\\))
import qualified Data.Set as S
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.List.NonEmpty (NonEmpty ((:|)), groupBy)
import Control.Monad.Trans.State (execState, evalState, get, modify)
import Data.Fix (Fix(Fix))
import Data.Bimap (Bimap)
import qualified Data.Bimap as BM
import qualified Data.List.NonEmpty as NE
import Data.Biapplicative (first)
import Data.List.Split (whenElt, keepDelimsR, split)
import Data.Functor.Foldable (cata)
import Data.Foldable (fold)
import Data.Bifoldable (bifold)
import Debug.Trace (trace)
import Data.List (partition, nub)


-- A containment module for experiments and stuff which I don't know where to put...


refGlobalsInStmt :: RStmt -> Set Global
refGlobalsInStmt = cata $ bifold . first (cata $ \case
    Var (Left g) -> S.singleton g
    expr -> fold expr)

referencedGlobals :: RFunDec -> Set Global
referencedGlobals (FD _ _ _ body) = foldMap refGlobalsInStmt body

groupStmts :: Bimap Local Global -> [RStmt] -> ([RStmt], Map Global (NonEmpty RStmt, Set Global))
groupStmts _ [] = mempty
groupStmts lgs stmts = (noGlobalAss, foldr addNext M.empty withGlobalAss)
    where
        onGlobals = whenElt $ \(Fix stmt) -> case stmt of
            Assignment l _ -> BM.member l lgs
            _ -> False

        -- If we have no global assignments, then the right part will be empty
        stmtsWtf = flip split stmts $ keepDelimsR onGlobals
        noGlobalAss = last stmtsWtf
        withGlobalAss = map NE.fromList $ init stmtsWtf

        addNext stmts remaining = M.insert global (stmts, refs) $ (fmap . fmap) (S.insert global) remaining
            where
                refs = foldMap refGlobalsInStmt stmts
                global = case NE.last stmts of
                    Fix (Assignment l _) -> lgs BM.! l
                    _ -> error "Should not happen :)"





makeCallGraph :: RModule -> Map Global (Set Global)
makeCallGraph RModule { rmFunctions, rmDataDecs, rmTLStmts, rmTLLocaLGlobals }
    = funRefs `M.union` (snd <$> stmtsWithGlobal)
    where
        availableGlobals = S.fromList (BM.keysR rmTLLocaLGlobals) `S.union` M.keysSet funRefs
        (cleanStmts, stmtsWithGlobal) = groupStmts rmTLLocaLGlobals rmTLStmts

        funRefs = fmap (S.intersection availableGlobals . referencedGlobals)
                $ M.fromList $ map (\f@(FD g _ _ _) -> (g, f)) $ S.toList rmFunctions


findCycles :: Map Global (Set Global) -> Set (Set Global)
findCycles cg = S.fromList $ map (go S.empty) $ M.toList cg
    where 
        go visited (g, next) = S.insert g $ foldMap (go (S.insert g visited) . (\k -> (k, cg ! k))) $ next \\ visited
        

findIndependentCycles :: Map Global (Set Global) -> Set (Set Global) -> Set (Set Global)
findIndependentCycles cg = S.filter (\cs -> all ((`S.isSubsetOf` cs) . (cg !)) cs)

flattenCallGraph :: Map Global (Set Global) -> [Set Global]
flattenCallGraph = nub . go  
    where go :: Map Global (Set Global) -> [Set Global]
          go cg = case M.partition null cg of
            (ind, rem) | null ind && null rem -> []
            (ind, rem) | null ind -> case findIndependentCycles rem (findCycles rem) of
                ids | null ids -> error "No independent cycles. Should not by physically possible."
                ids -> 
                    let cycles = ids  -- Get any element from each set to break the cycle.
                        allEdges = foldr S.union S.empty cycles
                    in S.toList cycles ++ go (fmap (S.\\ allEdges) rem) 
            (ind, rem) -> map S.singleton (M.keys ind) ++ go (fmap (S.\\ M.keysSet ind) rem)