{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
module AST.Untyped (module AST.Untyped) where
import AST.Common
import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import AST.Def (PP (..), (<+>), PPDef (..))
import qualified Data.List.NonEmpty as NonEmpty


data Untyped
type U = Untyped

type instance XTCon Untyped = Qualified Def.TCon
type instance XDTCon Untyped = Def.TCon
type instance XMem Untyped = Def.MemName
type instance XTVar Untyped = Def.UnboundTVar
type instance XLamOther Untyped = ()
type instance XFunOther Untyped = [ClassConstraint]
type instance XDataScheme Untyped = [Def.UnboundTVar]

type instance XVar Untyped = Qualified Def.VarName
type instance XVarOther Untyped = ()
type instance XLamVar Untyped = Def.VarName
type instance XLVar Untyped = Def.VarName
type instance XCon Untyped = Qualified Def.ConName
type instance XConOther Untyped = ()
type instance XClass Untyped = Qualified Def.ClassName
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

data ClassConstraint = CC (Qualified Def.ClassName) Def.UnboundTVar deriving Eq
type instance XClassConstraints Untyped = [ClassConstraint]

type instance XEnv Untyped = ()

type instance XReturn Untyped = Maybe (Expr Untyped)

data FunDef = FunDef (FunDec Untyped) (NonEmpty (AnnStmt Untyped))
type instance XFunDef Untyped = FunDef
type instance XInstDef Untyped = InstDef Untyped

data UntypedStmt
  = ClassDefinition (ClassDef U)
  | DataDefinition (DataDef U)
  | UseStmt Use
  | ExternalFunctionDeclaration (FunDec U)
type instance XOther Untyped = UntypedStmt

data Use = Use
  { moduleQualifier :: ModuleQualifier
  , items :: [UseItem]
  }

data UseItem
  = UseVarOrFun Def.VarName
  | UseType Def.TCon (NonEmpty Def.ConName)        -- Type(ConName, ConName')
  | UseClass Def.ClassName (NonEmpty Def.VarName)  -- Class(funName, funName')

  | UseTypeOrClass Def.TCon  -- we can't distinguish between ConName, TCon or Class. only after we resolve em we can do that

newtype ModuleQualifier = ModuleQualifier (NonEmpty Def.ModuleName) deriving (Eq, Ord, Show)
data Qualified a = Qualified
  { qualifier :: Maybe ModuleQualifier
  , qualify :: a
  } deriving (Eq, Show)

unqualified :: a -> Qualified a
unqualified x = Qualified { qualifier = Nothing, qualify = x }

newtype Mod = Mod [AnnStmt Untyped]
type instance Module Untyped = Mod



--------
-- PP --
--------

instance PP Mod where
  pp (Mod stmts) = Def.ppLines pp stmts

instance PP FunDef where
  pp (FunDef fd body) = Def.ppBody' pp (pp fd) body

instance PP ClassConstraint where
  pp (CC cn tv) = pp cn <+> pp tv

-- instance PP (Maybe (Expr U)) where
--   pp = maybe mempty pp

instance PP a => PP (Qualified a) where
  pp (Qualified Nothing a) = pp a
  pp (Qualified (Just mq) a) = pp mq <> "." <> pp a

instance PPDef a => PPDef (Qualified a) where
  ppDef (Qualified Nothing a) = ppDef a
  ppDef (Qualified (Just mq) a) = pp mq <> "." <> ppDef a

instance PP ModuleQualifier where
  pp (ModuleQualifier mods) = Def.sepBy "." $ pp <$> NonEmpty.toList mods

instance PP UntypedStmt where
  pp = \case
    ClassDefinition cd -> pp cd
    DataDefinition d -> pp d
    UseStmt us -> pp us
    ExternalFunctionDeclaration fn -> "external" <+> pp fn

instance PP Use where
  pp use = Def.ppBody pp (pp use.moduleQualifier) use.items

instance PP UseItem where
  pp = \case
    UseVarOrFun v -> pp v
    UseType tc conname -> pp tc <> Def.encloseSepBy "(" ")" ", " (pp <$> NonEmpty.toList conname)
    UseClass cn vns -> pp cn <> Def.encloseSepBy "(" ")" ", " (pp <$> NonEmpty.toList vns)
    UseTypeOrClass t -> "?" <> pp t
