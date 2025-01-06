{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module AST.Untyped (module AST.Untyped) where

import AST.Common (LitType, Op, Annotated, TCon (..), ConName, VarName, (:.), (<+>), Context, pretty, ppTCon, encloseSepBy, UnboundTVar (..))

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


----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var VarName
  | Con ConName

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

data DataCon = DC ConName [Type] deriving Eq
data DataDef = DD TCon [UnboundTVar] [Annotated DataCon] deriving Eq


--------------
-- Function --
--------------

data FunDec = FD VarName [(VarName, Maybe Type)] (Maybe Type) deriving Eq


----------
-- Case --
----------

data DeconF a
  = CaseVariable VarName
  | CaseConstructor ConName [a]
  deriving (Eq, Functor)
$(deriveEq1 ''DeconF)
type Decon = Fix DeconF

data CaseF expr stmt = Case
  { deconstruction :: Decon
  , caseCondition :: Maybe expr
  , body :: NonEmpty stmt
  } deriving (Eq, Functor, Foldable, Traversable)
type Case = CaseF Expr AnnStmt


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
