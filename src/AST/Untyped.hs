{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module AST.Untyped (module AST.Untyped) where
import AST.Common
import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import AST.Def (PP (..))

data Untyped
type U = Untyped

type instance XTCon Untyped = Def.TCon
type instance XMem Untyped = Def.MemName
type instance XTVar Untyped = Def.UnboundTVar


type instance XVar Untyped = Def.VarName
type instance XCon Untyped = Def.ConName
type instance XClass Untyped = Def.ClassName

type instance XEnv Untyped = ()

type instance XReturn Untyped = Maybe (Expr Untyped)

type instance XFunDef Untyped = (FunDec Untyped, NonEmpty (AnnStmt Untyped))
type instance XInstDef Untyped = InstDef Untyped

data UntypedStmt
  = ClassDefinition (ClassDef U)
  | DataDefinition (Either (DataRec U) (DataDef U))
type instance XOther Untyped = UntypedStmt



type instance Module Untyped = [AnnStmt Untyped]



--------
-- PP --
--------

instance PP [AnnStmt U] where
  pp = Def.ppLines pp

instance PP (FunDec U, NonEmpty (AnnStmt U)) where
  pp (fd, body) = Def.ppBody' pp (pp fd) body

instance PP (Maybe (Expr U)) where
  pp = maybe mempty pp

instance PP UntypedStmt where
  pp = \case
    ClassDefinition cd -> pp cd
    DataDefinition (Right dd) -> pp dd
    DataDefinition (Left dr) -> pp dr
