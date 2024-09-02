{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.TyVared (module AST.TyVared) where

import Data.Unique (Unique)
import AST.Common (VarName, UniqueType, TVar, Type, LitType, Locality, UniqueVar, UniqueCon, Op, Expr, Annotated, Ann, AnnStmt, Stmt, Module, Env, EnvUnion)
import Data.List.NonEmpty (NonEmpty)
import Data.Functor.Classes (Show1 (liftShowsPrec), Eq1 (liftEq))
import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.Fix (Fix)
import Data.Text (Text)


data TyVared

-- Note, that a lot of instances are basically the same as Typed.
-- Right now, due to "principles", I want to ensure that TyVared and Typed ASTs are distinct.
-- In the future, however, I might make Typed just slightly more polymorphic, so I can throw out most of the code here.
--  (because I think we can just reuse TyVared IDs in Typed)


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
  , union :: [EnvF t]
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


newtype TyVar = TyV Text deriving (Eq, Ord)

instance Show TyVar where
  show = undefined


data TypeF a
  = TCon UniqueType [a]
  | TVar TVar  -- should I make a unique TVar?
  | TFun (EnvUnionF a) [a] a
  | TyVar TyVar
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type TyVared = Fix TypeF
type instance Env TyVared = EnvF (Type TyVared)
type instance EnvUnion TyVared = EnvUnionF (Type TyVared)


----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | As a (Type TyVared)
  | Lam (EnvF (Type TyVared)) [(UniqueVar, Type TyVared)] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExprType a = ExprType (Type TyVared) (ExprF a) deriving (Show, Eq, Functor, Foldable, Traversable)


$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type instance Expr TyVared = Fix ExprType


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type TyVared] deriving (Eq, Show)
data DataDef = DD UniqueType [TVar] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD (Env TyVared) UniqueVar [(UniqueVar, Type TyVared)] (Type TyVared) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Either (Type TyVared) expr)  -- additional type inserted to preserve the information we got during typechecking.
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return (Either (Type TyVared) expr)

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)
$(deriveBitraversable ''StmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (StmtF (Expr TyVared) a) deriving (Functor, Foldable, Traversable)

type instance Stmt TyVared = StmtF (Expr TyVared) (AnnStmt TyVared)
type instance AnnStmt TyVared = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod [AnnStmt TyVared]

type instance Module TyVared = Mod


