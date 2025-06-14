{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
module AST.Resolved (module AST.Resolved) where

import AST.Common
import qualified AST.Def as Def
import AST.Typed (T)
import Data.Map (Map)
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty)
import Data.Functor ((<&>))
import AST.Def (PP (..))

data Resolved
type R = Resolved


type instance XVar Resolved = Variable
type instance XVarOther Resolved = Def.Locality
type instance XLVar Resolved = Def.UniqueVar
type instance XCon Resolved = Constructor
type instance XTCon Resolved = DataType
type instance XDTCon Resolved = Def.UniqueType
type instance XReturn Resolved = Expr R
type instance Rec Resolved a = a
type instance XDCon Resolved = Def.UniqueCon
type instance XTVar Resolved = TVar R
type instance XMem Resolved = Def.MemName
type instance XFunVar Resolved = Def.UniqueVar
type instance XFunDef Resolved = Function R
type instance XClass Resolved = Class
type instance XDClass Resolved = Def.UniqueClass
type instance XInstDef Resolved = InstDef R
type instance ClassConstraints Resolved = Map (TVar R) (Set Class)
type instance XOther Resolved = ()

data Env = Env { fromEnv :: [(VariableProto, Def.Locality)], level :: Int }
data LamDec = LamDec Def.UniqueVar Env

type instance XEnv R = Env
type instance XLamOther Resolved = LamDec


type ScopeSnapshot = Map Class PossibleInstances


-- A variable prototype.
-- the only difference is that classes don't have assigned instances.
data VariableProto
  = PDefinedVariable Def.UniqueVar

  | PDefinedFunction (Function R)
  | PExternalFunction (Function T)  -- it's only defined as external, because it's already typed. nothing else should change.

  | PDefinedClassFunction (ClassFunDec R)
  | PExternalClassFunction (ClassFunDec T)
  deriving (Eq, Ord)

data Variable
  = DefinedVariable Def.UniqueVar
  | DefinedFunction (Function R) ScopeSnapshot
  | ExternalFunction (Function T) ScopeSnapshot
  | DefinedClassFunction (ClassFunDec R) ScopeSnapshot
  | ExternalClassFunction (ClassFunDec T) ScopeSnapshot

asPUniqueVar :: VariableProto -> Def.UniqueVar
asPUniqueVar = \case
  PDefinedVariable var -> var

  PDefinedFunction (Function { functionDeclaration = FD { functionId = fid } }) -> fid
  PExternalFunction (Function { functionDeclaration = FD { functionId = fid } }) -> fid

  PDefinedClassFunction (CFD _ uv _ _) -> uv
  PExternalClassFunction (CFD _ uv _ _) -> uv

asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  DefinedFunction fn _ -> PDefinedFunction fn
  ExternalFunction fn _ -> PExternalFunction fn
  DefinedClassFunction cd _ -> PDefinedClassFunction cd
  ExternalClassFunction cd _ -> PExternalClassFunction cd


data Constructor
  = DefinedConstructor (DataCon R)
  | ExternalConstructor (DataCon T)

data DataType
  = DefinedDatatype (DataDef R)
  | ExternalDatatype (DataDef T)
  deriving (Eq, Ord)

asUniqueType :: DataType -> Def.UniqueType
asUniqueType (DefinedDatatype (DD ut _ _ _)) = ut
asUniqueType (ExternalDatatype (DD ut _ _ _)) = ut

tryGetMembersFromDatatype :: DataType -> Maybe (NonEmpty Def.MemName)
tryGetMembersFromDatatype = \case
  DefinedDatatype (DD _ _ (Left recs) _) -> Just $ recs <&> \(Def.Annotated _ (mem, _)) -> mem
  ExternalDatatype (DD _ _ (Left recs) _) -> Just $ recs <&> \(Def.Annotated _ (mem, _)) -> mem
  _ -> Nothing


-- TODO: because it's used in TVar, we might make this a type family!
-- I'll see the context in which they are used.
data Class
  = DefinedClass (ClassDef R)
  | ExternalClass (ClassDef T)
  deriving (Eq, Ord)

asUniqueClass :: Class -> Def.UniqueClass
asUniqueClass = \case
  DefinedClass cd -> cd.classID
  ExternalClass cd -> cd.classID

data Inst
  = DefinedInst (InstDef R)
  | ExternalInst (InstDef T)
  

type PossibleInstances = Map DataType Inst

bindTVar :: Def.Binding -> Def.UnboundTVar -> TVar R
bindTVar b (Def.UTV tvname) = TV tvname b mempty

data Mod = Mod
  { toplevel :: [AnnStmt R]
  , exports :: Exports R

  , allFunctions :: [Function R]
  , allDatatypes :: [DataDef R]
  , allClasses :: [ClassDef R]
  , allInstances :: [InstDef R]
  }
type instance Module Resolved = Mod



-- Instances

instance PP Mod where
  pp mod = Def.ppLines pp mod.toplevel

instance PP Variable where
  pp = pp . asPUniqueVar . asProto

instance PP Constructor where
  pp = \case
    DefinedConstructor con -> pp con.conID
    ExternalConstructor con -> pp con.conID

instance PP DataType where
  pp = pp . asUniqueType

instance PP Class where
  pp = pp . asUniqueClass

instance PP LamDec where
  pp (LamDec uv e) = pp uv <> pp e

instance PP Env where
  pp env = Def.encloseSepBy "[" "]" ", " $ env.fromEnv <&> \(v, l) -> Def.ppVar l $ asPUniqueVar v
