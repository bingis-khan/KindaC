{-# LANGUAGE LambdaCase #-}
module Mono (monoModule) where

import AST
import Data.Map (Map)
import Data.Set (Set)
import Control.Monad.Trans.State (State, runState, evalState)
import Data.Functor.Foldable (transverse, Base)


-- this is more complicated than i thought
--  - unfortunately, right now, i have to compile even unused functions, because I don't know if they are executed.
--  - i can optimize it later, because this is more of an unusual case...
--    - where we check which functions get executed.
--    - ie trace the expression n shit and see if it's just a normal function
-- TODO: finish excuses

-- okay, so how should i do it?
-- 1. go through top level functions... IN REVERSE
--    1.5 there's a context
-- 2. gather variables and their types
--    2.1 scan for identifiers n shit
--    2.2 when reaching the variable that was used, replace the type with a tuple of types. ????
--    2.3 let's see what happens


monoModule :: Module Typed -> Module Mono
monoModule m = evalState (monoStmts m) mempty


type MonoCtx = State (Map VarInfo (Set (Type Mono)))


monoStmts :: Module Typed -> MonoCtx (Module Mono)
monoStmts = traverse (transverse monoAnnStmt) . reverse
  where
    monoAnnStmt :: Base (AnnStmt Typed) (MonoCtx a) -> MonoCtx (Base (AnnStmt Mono) a)
    monoAnnStmt (AnnStmt anns bigStmt) = AnnStmt anns <$> case bigStmt of
      NormalStmt stmt -> NormalStmt <$> case stmt of
        Print expr -> Print <$> monoExpr expr


monoExpr :: Expr Typed -> MonoCtx (Expr Mono)
monoExpr = transverse $ \(ExprType t expr) -> case expr of
  Lit (LInt x) -> do
    t' <- monoType t
    pure $ ExprType t' $ Lit $ LInt x
  Var v -> undefined


monoType :: Type Typed -> MonoCtx (Type Mono)
monoType = undefined


findVarType :: VarInfo -> MonoCtx (Type Mono)
findVarType = undefined
