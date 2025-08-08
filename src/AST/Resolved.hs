{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module AST.Resolved (module AST.Resolved) where

import AST.Common
import qualified AST.Def as Def
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty)
import Data.Functor ((<&>))
import AST.Def (PP (..), PPDef, ppDef)
import AST.Typed (TC)
import Data.String (fromString)
import Data.Text (Text)

data Resolved
type R = Resolved


type instance XVar Resolved = Variable
type instance XVarOther Resolved = Def.Locality
type instance XLVar Resolved = Def.UniqueVar
type instance XLamVar Resolved = Def.UniqueVar
type instance XCon Resolved = Constructor
type instance XConOther Resolved = Def.EnvID
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
type instance XClassFunDec Resolved = ClassFun
type instance XDClass Resolved = Def.UniqueClass
type instance XInstDef Resolved = InstDef R
type instance XClassConstraints Resolved = () -- Map (TVar R) (Set Class)
type instance XOther Resolved = ()
type instance XFunOther Resolved = ([Def.Ann], Def.Location)
type instance XTOther Resolved = RTO
type instance XTFun Resolved = ()
type instance XTConOther Resolved = ()
type instance XExprNode Resolved = Def.Location
type instance XFunType Resolved = DeclaredType R
type instance XDataScheme Resolved = [TVar R]
type instance XMutAccess Resolved = MutAccess R
type instance XInstExport R = Inst
type instance XStringInterpolation R = Text  -- we "unpack" string interpolation pretty early - here. NOTE: I might change it if the errors are bad tho.
type instance XExportType R = ()


data Env = Env { envID :: Def.EnvID, envStackLevel :: Def.EnvStack, fromEnv :: [(VariableProto, Def.Locality)] }
data LamDec = LamDec Def.UniqueVar Env

type instance XEnv R = Env
type instance XLamOther Resolved = LamDec


type ScopeSnapshot = Map Class PossibleInstances

data RTO
  = TVar (TVar R)
  | TClass Class


-- A variable prototype.
-- the only difference is that classes don't have assigned instances.
data VariableProto
  = PDefinedVariable Def.UniqueVar
  | PExternalVariable Def.UniqueVar (Type TC)  -- we seem to actually need the type here.....

  | PDefinedFunction (Function R)
  | PExternalFunction (Function TC)  -- it's only defined as external, because it's already typed. nothing else should change.

  | PDefinedClassFunction (ClassFunDec R)
  | PExternalClassFunction (ClassFunDec TC)
  deriving (Eq, Ord)

data Variable
  = DefinedVariable Def.UniqueVar
  | ExternalVariable Def.UniqueVar (Type TC)
  | DefinedFunction (Function R) ScopeSnapshot
  | ExternalFunction (Function TC) ScopeSnapshot
  | DefinedClassFunction (ClassFunDec R) ScopeSnapshot
  | ExternalClassFunction (ClassFunDec TC) ScopeSnapshot

asPUniqueVar :: VariableProto -> Def.UniqueVar
asPUniqueVar = \case
  PDefinedVariable var -> var
  PExternalVariable var _ -> var

  PDefinedFunction (Function { functionDeclaration = FD { functionId = fid } }) -> fid
  PExternalFunction (Function { functionDeclaration = FD { functionId = fid } }) -> fid

  PDefinedClassFunction (CFD _ uv _ _ _ _) -> uv
  PExternalClassFunction (CFD _ uv _ _ _ _) -> uv

asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  ExternalVariable v t -> PExternalVariable v t
  DefinedFunction fn _ -> PDefinedFunction fn
  ExternalFunction fn _ -> PExternalFunction fn
  DefinedClassFunction cd _ -> PDefinedClassFunction cd
  ExternalClassFunction cd _ -> PExternalClassFunction cd


data Constructor
  = DefinedConstructor (DataCon R)
  | ExternalConstructor (DataCon TC)

data DataType
  = DefinedDatatype (DataDef R)
  | ExternalDatatype (DataDef TC)
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
  | ExternalClass (ClassDef TC)
  deriving (Eq, Ord)

asUniqueClass :: Class -> Def.UniqueClass
asUniqueClass = \case
  DefinedClass cd -> cd.classID
  ExternalClass cd -> cd.classID

data ClassFun
  = DefinedClassFunDec (ClassFunDec R)
  | ExternalClassFunDec (ClassFunDec TC)

data Inst
  = DefinedInst (InstDef R)
  | ExternalInst (InstDef TC)


type PossibleInstances = Map DataType Inst

bindTVar :: Set Class -> Def.Binding -> Def.UnboundTVar -> TVar R
bindTVar scs b (Def.UTV tvname) = TV tvname b scs

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
  pp mod = Def.ppLines mod.toplevel

instance PP Variable where
  pp = pp . asPUniqueVar . asProto

instance PP RTO where
  pp = \case
    TVar tv -> pp tv
    TClass klass-> ppDef klass

instance PP Constructor where
  pp = \case
    DefinedConstructor con -> pp con.conID
    ExternalConstructor con -> pp con.conID

instance PP DataType where
  pp = pp . asUniqueType

instance PPDef DataType where
  ppDef = pp . asUniqueType

instance PP Class where
  pp = pp . asUniqueClass

instance PPDef Class where
  ppDef = pp . asUniqueClass

instance PP LamDec where
  pp (LamDec uv e) = pp uv <> pp e

instance PP Env where
  pp env = fromString $ Def.printf "%s(%s)%s" (pp env.envID) (pp env.envStackLevel) $ Def.encloseSepBy "[" "]" ", " $ env.fromEnv <&> \(v, l) -> Def.ppVar l $ asPUniqueVar v
