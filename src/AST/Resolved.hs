{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, UndecidableInstances #-}
module AST.Resolved (module AST.Resolved) where

import AST.Common (LitType, Op, Type, Expr, Annotated, TVar, Stmt, Ann, Module, AnnStmt, UniqueType, UniqueVar, UniqueCon, Locality)

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Fix (Fix)
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)


data Resolved


----------
-- Type --
----------

data TypeF a
  = TCon UniqueType [a]
  | TVar TVar
  | TFun [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type Resolved = Fix TypeF



----------------
-- Expression --
----------------

newtype Env = Env [UniqueVar] deriving (Show, Eq, Ord)

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | As a (Type Resolved)
  | Lam Env [UniqueVar] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type instance Expr Resolved = Fix ExprF


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type Resolved] deriving (Eq, Show)
data DataDef = DD UniqueType [TVar] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD Env UniqueVar [(UniqueVar, Maybe (Type Resolved))] (Maybe (Type Resolved)) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Maybe expr)
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return (Maybe expr)
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- The "big statement" - the distinction here is that the non-normal stmts need special treatment while typechecking. Not required (might remove later), but makes generating constraints slightly less annoying!
data BigStmtF expr a
  = NormalStmt (StmtF expr a)
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifoldable ''StmtF)
$(deriveBifoldable ''BigStmtF)
$(deriveBifunctor ''StmtF)
$(deriveBifunctor ''BigStmtF)
$(deriveBitraversable ''StmtF)
$(deriveBitraversable ''BigStmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (BigStmtF (Expr Resolved) a) deriving (Functor, Foldable, Traversable)

type instance Stmt Resolved = BigStmtF (Expr Resolved) (AnnStmt Resolved)
type instance AnnStmt Resolved = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod { fromMod :: [AnnStmt Resolved] }

type instance Module Resolved = Mod


