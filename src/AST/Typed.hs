{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.Typed (module AST.Typed) where

import AST.Common (LitType, Op, Type, Expr, Annotated, TVar, Stmt, Ann, Module, AnnStmt, UniqueType, UniqueVar, UniqueCon, Locality, VarName, Env, EnvUnion)

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Fix (Fix)
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifoldable)
import Data.Unique (Unique)
import Data.Functor.Classes (Show1 (..), Eq1 (liftEq))


data Typed


----------
-- Type --
----------

-- Env without this "superposition" - present when defining functions and lambdas.
-- do I need ID here?
-- reasons:
--  - always nice to have additional information?
data EnvF t = Env  -- right now, make Env local to "Typed" module, because the definition will change with monomorphization.
  { envID :: Unique
  , env :: [(UniqueVar, t)]  -- t is here, because of recursion schemes.
  } deriving (Functor, Foldable, Traversable)

instance Show (EnvF t) where
  show = undefined

instance Eq (EnvF t) where
  Env { envID = l } == Env { envID = r }  = l == r

instance Ord (EnvF t) where
  Env { envID = l } `compare` Env { envID = r } = l `compare` r

-- The Env "superposition".
-- do I need the ID here?
-- reasons:
--  - always nice to have additional information?
data EnvUnionF t = EnvUnion
  { unionID :: Unique
  , union :: NonEmpty (EnvF t)
  } deriving (Functor, Foldable, Traversable)

instance Show (EnvUnionF t) where
  show = undefined

instance Show1 EnvUnionF where
  liftShowsPrec = undefined

instance Eq1 EnvUnionF where
  liftEq = undefined  


instance Eq (EnvUnionF t) where
  EnvUnion { unionID = l } == EnvUnion { unionID = r }  = l == r

instance Ord (EnvUnionF t) where
  EnvUnion { unionID = l } `compare` EnvUnion { unionID = r } = l `compare` r


data TypeF a
  = TCon UniqueType [a]
  | TVar TVar  -- should I make a unique TVar?
  | TFun (EnvUnionF a) [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type Typed = Fix TypeF
type instance Env Typed = EnvF (Type Typed)
type instance EnvUnion Typed = EnvUnionF (Type Typed)



----------------
-- Expression --
----------------

-- newtype Env = Env [UniqueVar] deriving (Show, Eq, Ord)

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | As a (Type Typed)
  | Lam (Env Typed) [(UniqueVar, Type Typed)] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExprType a = ExprType (Type Typed) (ExprF a) deriving (Show, Eq, Functor, Foldable, Traversable)


$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type instance Expr Typed = Fix ExprType


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type Typed] deriving (Eq, Show)
data DataDef = DD UniqueType [TVar] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD (Env Typed) UniqueVar [(UniqueVar, Type Typed)] (Type Typed) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Either (Type Typed) expr)  -- additional type inserted to preserve the information we got during typechecking.
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return (Either (Type Typed) expr)

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifoldable ''StmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (StmtF (Expr Typed) a) deriving (Functor, Foldable, Traversable)

type instance Stmt Typed = StmtF (Expr Typed) (AnnStmt Typed)
type instance AnnStmt Typed = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod { fromMod :: [AnnStmt Typed] }

type instance Module Typed = Mod


