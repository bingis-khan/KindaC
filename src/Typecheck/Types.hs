{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Typecheck.Types  where

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Ord.Deriving
import Data.Text (Text)
import AST
import Data.Fix (Fix)
import qualified Data.Text as Text


data TyVared  -- change this name to something simpler and more descriptive


newtype TyVar = TyVar Text deriving (Eq, Ord)
instance Show TyVar where
  show (TyVar t) = Text.unpack t
data TyFunEnv' v = TyFunEnv TyVar (FunEnv v) deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
$(deriveShow1 ''TyFunEnv')
$(deriveEq1 ''TyFunEnv')
$(deriveOrd1 ''TyFunEnv')

type TyFunEnv = TyFunEnv' (Type TyVared)

newtype TypeF' a = TF' { fromTF' :: Either TyVar (TypeF TyFunEnv' TypeInfo a) } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
$(deriveShow1 ''TypeF')
$(deriveEq1 ''TypeF')
$(deriveOrd1 ''TypeF')


type instance Type TyVared = Fix TypeF'

type instance Expr TyVared = Fix (ExprType (Type TyVared) (Type Typed))

type instance DataCon TyVared = GDataCon ConInfo (Type Typed)
type instance DataDef TyVared = GDataDef TypeInfo (DataCon TyVared)
type instance FunDec TyVared = GFunDec VarEnv ConInfo VarInfo (Type TyVared)
type instance AnnStmt TyVared = Fix (AnnStmtF (BigStmtF (DataDef TyVared) (FunDec TyVared) (StmtF ConInfo VarInfo (Expr TyVared))))
type instance Stmt TyVared = BigStmtF (DataDef TyVared) (FunDec TyVared) (StmtF ConInfo VarInfo (Expr TyVared)) (AnnStmt TyVared)

