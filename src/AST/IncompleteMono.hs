-- EnvID reexport for me to know which union PHASE I am referencing.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
module AST.IncompleteMono (module AST.IncompleteMono, Def.EnvID) where
import AST.Common (Function, Type, XLVar, XReturn, XNode, Expr, XLamOther, XLamVar, XVarOther, XFunDef, XVar, XConOther, DataCon, XCon, DataDef, XTCon, XMem, XFunOther, XFunVar, XFunType, XEnv, XTOther, XTConOther, XTFun, XDTCon, XDataScheme, Rec, XDCon, functionDeclaration, functionId, XTVar, XOther, XInstDef)
import qualified AST.Def as Def
import AST.Def (Locality, PP (..), (<+>), PPDef)
import Data.List.NonEmpty (NonEmpty)
import AST.Typed (TC)
import qualified AST.Typed as T
import qualified Data.List.NonEmpty as NonEmpty
import Data.String (fromString)
import Data.Text (Text)

data IMono
type IM = IMono

type instance Rec IM a = a
type instance XLVar IM = Def.UniqueVar
type instance XReturn IM = Expr IM
type instance XNode IM = Type IM
type instance XLamOther IM = Env
type instance XLamVar IM = (Def.UniqueVar, Type IM)
type instance XVarOther IM = Locality
type instance XFunDef IM = NonEmpty (Function IM, Env)
type instance XVar IM = Variable
type instance XVarOther IM = Def.Locality
type instance XCon IM = DataCon IM
type instance XConOther IM = ()
type instance XTCon IM = DataDef IM
type instance XMem IM = Def.UniqueMem
type instance XFunOther IM = ()
type instance XFunVar IM = Def.UniqueVar
type instance XFunType IM = Type IM
type instance XEnv IM = Env
type instance XTOther IM = OtherT
type instance XTConOther IM = [EnvUnion]
type instance XTFun IM = EnvUnion
type instance XDTCon IM = Def.UniqueType
type instance XDataScheme IM = OtherDD
type instance XDCon IM = Def.UniqueCon
type instance XTVar IM = TVar
type instance XOther IM = ()
type instance XInstDef IM = ()

newtype OtherT
  = TVar TVar
  deriving (Eq, Ord)

data TVar = TV
  { fromTV :: Text
  , binding :: Def.Binding
  } deriving (Eq, Ord)

data OtherDD = OtherDD
  { appliedTypes :: [Type IM]
  , ogDataDef :: DataDef TC
  }

data Variable
  = DefinedFunction (Function IM)
  | DefinedVariable Def.UniqueVar
  deriving (Eq, Ord)

data Env
  = Env Def.EnvID [(Variable, Locality, Type IM)]
  | RecursiveEnv Def.EnvID IsRecursive

data EnvTypes
  = EnvTypes Def.EnvID [Type IM]
  deriving (Eq, Ord)

type IsRecursive = Bool

envID :: Env -> Def.EnvID
envID = \case
  Env eid _ -> eid
  RecursiveEnv eid _ -> eid

data EnvUnion = EnvUnion
  { unionID :: Def.UnionID
  , union :: NonEmpty (T.EnvF (Type IM))
  }


-----------

instance Eq EnvUnion where
  EnvUnion {unionID = l} == EnvUnion {unionID = r} = l == r

-- instance Eq1 EnvUnion where
--   liftEq _ (EnvUnion {unionID = uid}) (EnvUnion {unionID = uid'}) = uid == uid'

instance Ord EnvUnion where
  EnvUnion {unionID = l} `compare` EnvUnion {unionID = r} = l `compare` r

-- instance Ord1 EnvUnion where
--   liftCompare _ (EnvUnion {unionID = uid}) (EnvUnion {unionID = uid'}) = uid `compare` uid'

instance Eq Env where
  e == e' = envID e == envID e'

instance Ord Env where
  e `compare` e' = envID e `compare` envID e'


-----------
-- PP --
--------

instance PP EnvUnion where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> NonEmpty.toList us)

instance PP Env where
  pp = \case
    Env eid vs -> pp eid <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp v <+> pp t) vs)
    RecursiveEnv eid isEmpty -> fromString $ Def.printf "%s[REC%s]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

instance PP Variable where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f -> pp f.functionDeclaration.functionId <> "&F"

instance PP OtherT where
  pp (TVar tv) = pp tv

instance PP TVar where
  pp tv =
    let bindingCtx = case tv.binding of
          Def.BindByType ut -> pp ut.typeName
          Def.BindByVar uv -> pp uv.varName
          Def.BindByInst uc -> pp uc.className
    in pp tv.fromTV <> "<" <> bindingCtx <> ">"

instance PP OtherDD where
  pp = mempty

instance PPDef Variable where
  ppDef = \case
    DefinedVariable uv -> pp uv
    DefinedFunction fn -> pp fn.functionDeclaration.functionId
