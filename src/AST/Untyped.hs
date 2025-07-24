{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
module AST.Untyped (module AST.Untyped) where
import AST.Common
import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import AST.Def (PP (..), (<+>))
import Data.Fix (Fix)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')


data Untyped
type U = Untyped

type instance XTCon Untyped = Def.TCon
type instance XDTCon Untyped = Def.TCon
type instance XMem Untyped = Def.MemName
type instance XTVar Untyped = Def.UnboundTVar
type instance XLamOther Untyped = ()
type instance XFunOther Untyped = ()
type instance XDataScheme Untyped = [Def.UnboundTVar]

type instance XVar Untyped = Def.VarName
type instance XVarOther Untyped = ()
type instance XLamVar Untyped = Def.VarName
type instance XLVar Untyped = Def.VarName
type instance XCon Untyped = Def.ConName
type instance XConOther Untyped = ()
type instance XClass Untyped = Def.ClassName
type instance XDClass Untyped = Def.ClassName
type instance Rec Untyped a = ()
type instance XDCon Untyped = Def.ConName
type instance XFunVar Untyped = Def.VarName
type instance XTOther Untyped = Def.UnboundTVar
type instance XTFun Untyped = ()
type instance XTConOther Untyped = ()
type instance XNode Untyped = ()
type instance XFunType Untyped = DeclaredType U
type instance XMutAccess Untyped = MutAccess U

data ClassConstraint = CC Def.ClassName Def.UnboundTVar deriving Eq
type instance ClassConstraints Untyped = [ClassConstraint]

type instance XEnv Untyped = ()

type instance XReturn Untyped = Maybe (Expr Untyped)

data FunDef = FunDef (FunDec Untyped) (NonEmpty (AnnStmt Untyped))
type instance XFunDef Untyped = FunDef
type instance XInstDef Untyped = InstDef Untyped

data UntypedStmt
  = ClassDefinition (ClassDef U)
  | DataDefinition (DataDef U)
type instance XOther Untyped = UntypedStmt

newtype Mod = Mod [AnnStmt Untyped]
type instance Module Untyped = Mod



--------
-- PP --
--------

instance PP Mod where
  pp (Mod stmts) = Def.ppLines pp stmts

instance PP FunDef where
  pp (FunDef fd body) = Def.ppBody' pp (pp fd) body

-- instance PP (Maybe (Expr U)) where
--   pp = maybe mempty pp

instance PP UntypedStmt where
  pp = \case
    ClassDefinition cd -> pp cd
    DataDefinition d -> pp d
