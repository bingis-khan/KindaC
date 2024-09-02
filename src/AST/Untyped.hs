{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.Untyped where

import AST.Common (LitType, Op, Type, Expr, Annotated, TCon, TVar, Stmt, Ann, Module, ConName, VarName, AnnStmt)

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Fix (Fix)
import Data.List.NonEmpty (NonEmpty)


data Untyped


----------
-- Type --
----------

data TypeF a
  = TCon TCon [a]
  | TVar TVar
  | TFun [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type Untyped = Fix TypeF


----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var VarName
  | Con ConName

  | Op a Op a
  | Call a [a]
  | As a (Type Untyped)
  | Lam [VarName] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type instance Expr Untyped = Fix ExprF


---------------------
-- Data Definition --
---------------------

data DataCon = DC ConName [Type Untyped] deriving (Eq, Show)
data DataDef = DD TCon [TVar] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD VarName [(VarName, Maybe (Type Untyped))] (Maybe (Type Untyped)) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment VarName expr
  | Pass

  | MutDefinition VarName (Maybe expr)
  | MutAssignment VarName expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return (Maybe expr)

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt expr a = AnnStmt [Ann] (StmtF expr a) deriving (Functor)

type instance Stmt Untyped = StmtF (Expr Untyped) (AnnStmt Untyped)
type instance AnnStmt Untyped = Fix (AnnotatedStmt (Expr Untyped))


---------------
-- Module --
---------------

newtype Mod = Mod [AnnStmt Untyped]

type instance Module Untyped = Mod


