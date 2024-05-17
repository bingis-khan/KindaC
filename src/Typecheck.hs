{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module Typecheck (typecheck) where

import AST
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (bimap, first)
import Data.Map (Map)
import Control.Monad.Trans.RWS (RWS, evalRWS)
import Data.Fix (Fix)
import Data.Functor.Foldable (transverse)
import Control.Monad ((<=<))


-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)


typecheck :: Module Resolved -> Either Text (Module Typed)
typecheck rStmts = do
    -- Three phases (excluding resolving - might put it in another file if not for the fact, that errors are related)
    let (tyStmts, constraints) = generateConstraints rStmts
    subst <- solveConstraints constraints

    let tStmts = substituteTypes subst tyStmts

    return tStmts


---------------------------
-- CONSTRAINT GENERATION --
---------------------------

generateConstraints :: Module Resolved -> (Module TyVared, [Constraint])
generateConstraints  utModule = (tvModule, constraints)
  where
    (tvModule, constraints) = evalRWS inferModule env newTVarGen
    inferModule = conStmts utModule
    env = emptyEnv

-- Parses the top level part of the file.
--  Note: for top level, the return value will be set as U8 in order to "exit" the program.
conStmts :: [AnnStmt Resolved] -> Infer [AnnStmt TyVared]
conStmts = traverse conStmtScaffolding  -- go through the list (effectively)
  where
    -- map expressions, then go to stmt
    --  all in a recursion-schemes way.
    conStmtScaffolding = transverse $ conStmt <=< undefined -- (pure . first conExpr) <=< sequenceA

    -- this is actual logic. two steps:
    --  - basic resolving
    --  - type inference
    conStmt = undefined

conExpr :: Expr Resolved -> Infer (Expr TyVared)
conExpr = undefined


-- todo: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer a = RWS Env [Constraint] TVarGen a


data Env = Env
  { variables :: Map VarInfo (Type Typed)  -- For variables and functions.
  , constructors :: Map ConInfo (Type Typed)
  }

emptyEnv = Env { variables = mempty, constructors = mempty }


type Constraint = (Type Typed, Type Typed)


newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst




------------------------
-- CONSTRAINT SOLVING --
------------------------

data TypeError

solveConstraints :: [Constraint] -> Either Text Subst  -- returns literally error text. don't be afraid to change the interface tho.
solveConstraints = undefined

substituteTypes :: Subst -> Module TyVared -> Module Typed
substituteTypes = undefined


------------------------------
-- INTERMEDIATE REPRESENTATION for AST with TYPE PARAMETERS --
------------------------------

data TyVared  -- change this name to something simpler and more descriptive

type instance Type TyVared = TyVar
type instance Expr TyVared = Fix (ExprType (Type TyVared))

type instance DataCon TyVared = GDataCon ConInfo TyVared
type instance DataDef TyVared = GDataDef TypeInfo (DataCon TyVared)
type instance FunDec TyVared = GFunDec ConInfo VarInfo (Type TyVared)
type instance AnnStmt TyVared = Fix (StmtF (DataDef TyVared) (FunDec TyVared) ConInfo VarInfo (Expr TyVared))
type instance Stmt TyVared = StmtF (DataDef TyVared) (FunDec TyVared) ConInfo VarInfo (Expr TyVared) (AnnStmt TyVared)

newtype TyVar = TyVar String
