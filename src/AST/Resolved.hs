{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, UndecidableInstances #-}
module AST.Resolved (module AST.Resolved) where

import AST.Common (LitType, Op, Type, Expr, Annotated, TVar, Stmt, Ann, Module, AnnStmt, UniqueType, UniqueVar, UniqueCon, Locality, Decon)

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

newtype Env = Env { fromEnv :: [(UniqueVar, Locality)]} deriving (Show, Eq, Ord)

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


----------
-- Case --
----------

data DeconF a
  = CaseVariable UniqueVar
  | CaseConstructor UniqueCon [a]
  deriving (Show, Eq, Functor)
$(deriveShow1 ''DeconF)
$(deriveEq1 ''DeconF)

type instance Decon Resolved = Fix DeconF

data Case expr a = Case 
  { deconstruction :: Decon Resolved
  , caseCondition :: Maybe expr
  , body :: NonEmpty a
  } deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifunctor ''Case)
$(deriveBifoldable ''Case)
$(deriveBitraversable ''Case)



---------------
-- Statement --
---------------

$(deriveShow1 ''Case)

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Maybe expr)
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (Case expr a))
  | ExprStmt expr
  | Return expr
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)

-- The "big statement" - the distinction here is that the non-normal stmts need special treatment while typechecking. Not required (might remove later), but makes generating constraints slightly less annoying!
-- TODO: really?
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
$(deriveShow1 ''BigStmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (BigStmtF (Expr Resolved) a) deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''AnnotatedStmt)

type instance Stmt Resolved = BigStmtF (Expr Resolved) (AnnStmt Resolved)
type instance AnnStmt Resolved = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod { fromMod :: [AnnStmt Resolved] } deriving Show

type instance Module Resolved = Mod


