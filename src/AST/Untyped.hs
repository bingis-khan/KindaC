{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module AST.Untyped (module AST.Untyped) where

import AST.Common (LitType, Op, Annotated, TCon (..), ConName, VarName, (:.), (<+>), Context, pretty, ppTCon, encloseSepBy, UnboundTVar (..), MemName, ClassName)

import Data.Eq.Deriving
import Data.Fix (Fix)
import Data.List.NonEmpty (NonEmpty)
import Data.Foldable (foldl')
import Data.Functor.Foldable (cata)



----------
-- Type --
----------

data TypeF a
  = TCon TCon [a]
  | TVar UnboundTVar
  | TFun [a] a
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type Type = Fix TypeF

$(deriveEq1 ''TypeF)


data ClassTypeF a
  = Self
  | NormalType (TypeF a)
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type ClassType = Fix ClassTypeF

$(deriveEq1 ''ClassTypeF)



----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var VarName
  | Con ConName

  | RecCon TCon (NonEmpty (MemName, a))
  | RecUpdate a (NonEmpty (MemName, a))
  | MemAccess a MemName

  | Op a Op a
  | Call a [a]
  | As a Type
  | Lam [VarName] a
  deriving (Eq, Functor, Foldable, Traversable)
type Expr = Fix ExprF

$(deriveEq1 ''ExprF)



---------------------
-- Data Definition --
---------------------

data DataRec = DR MemName Type deriving Eq
data DataCon = DC ConName [Type] deriving Eq
data DataDef = DD TCon [UnboundTVar] (Either (NonEmpty (Annotated DataRec)) [Annotated DataCon]) deriving Eq  -- ISSUE(record-as-separate-type): TODO: in the future should probably be split ADTs and Records into two separate data types, but it makes working with these easier, as we just reuse functions (less things to worry about and less code.) everything else is a bit scuffed.



----------
-- Case --
----------

data DeconF a
  = CaseVariable VarName
  | CaseConstructor ConName [a]
  | CaseRecord TCon (NonEmpty (MemName, a))
  deriving (Eq, Functor)
$(deriveEq1 ''DeconF)
type Decon = Fix DeconF

data CaseF expr stmt = Case
  { deconstruction :: Decon
  , caseCondition :: Maybe expr
  , body :: NonEmpty stmt
  } deriving (Eq, Functor, Foldable, Traversable)
type Case = CaseF Expr AnnStmt


--------------
-- Function --
--------------

data FunDec = FD VarName [(Decon, Maybe Type)] (Maybe Type) deriving Eq


---------------
-- Typeclass --
---------------

data ClassDef = ClassDef
  { classID :: ClassName
  , classDependentTypes :: [DependentType]
  , classFunctions :: [ClassFunDec]  -- TODO: soon will contain default implementations
  } deriving Eq

data ClassFunDec = CFD VarName [(Decon, ClassType)] ClassType deriving Eq
newtype DependentType = Dep TCon deriving Eq  -- temporarily no parameters?

data InstDef stmt = InstDef
  { instClassName :: ClassName
  , instType :: (TCon, [UnboundTVar])  -- we accept only constructors yo!... (or should it involve more types... i mean, scoped type variables :OOO)
  , instConstraints :: [ClassConstraint]
  , instDependentTypes :: [(DependentType, ClassType)]
  , instFunctions :: [(FunDec, NonEmpty stmt)]
  } deriving (Eq, Foldable, Functor, Traversable)

data ClassConstraint = CC ClassName UnboundTVar deriving Eq


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment VarName expr
  | Mutation VarName expr

  | Pass


  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (CaseF expr a))
  | ExprStmt expr
  | Return (Maybe expr)

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)

  -- Typeclasses
  | ClassDefinition ClassDef
  | InstDefinition (InstDef a)
  deriving (Eq, Functor, Foldable, Traversable)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.

type Stmt = StmtF Expr AnnStmt
type AnnStmt = Fix (Annotated :. StmtF Expr)


---------------
-- Module --
---------------

newtype Module = Mod [AnnStmt]



--------
-- PP --
--------

uType :: Type -> Context
uType = cata $ \case
  TCon con params -> 
    foldl' (<+>) (ppTCon con) params
  TVar (UTV tv) -> pretty tv
  TFun args ret -> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

uClassType :: ClassType -> Context
uClassType = undefined
