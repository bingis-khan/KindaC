{-# LANGUAGE LambdaCase #-}
module TypecheckAdditional (poukładaj) where
import Data.Set (Set)
import qualified Data.Set as S
import AST
import Data.Graph (stronglyConnComp, SCC)
import Data.Functor.Foldable (cata)
import Data.Foldable (fold)
import Data.Bifoldable (bifold)
import Data.Biapplicative (first)


exprStuff :: RExpr -> Set Global
exprStuff = cata $ \case
    Var (Left g) -> S.singleton g
    expr -> fold expr

calls' :: RFunDec -> Set Global
calls' (FD _ _ _ stmts) = flip foldMap stmts $ cata $ bifold . first exprStuff
    

calls :: Set RFunDec -> [(RFunDec, Global, [Global])]
calls = fmap (\f@(FD g _ _ _) -> (f, g, S.toList (calls' f))) . S.toList


poukładaj :: Set RFunDec -> [SCC RFunDec]
poukładaj = stronglyConnComp . calls
