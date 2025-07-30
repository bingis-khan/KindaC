-- EnvID reexport for me to know which union PHASE I am referencing.
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NamedFieldPuns #-}
module AST.IncompleteMono (module AST.IncompleteMono, Def.EnvID) where
import AST.Common (Function, Type, XLVar, XReturn, XNode, Expr, XLamOther, XLamVar, XVarOther, XFunDef, XVar, XConOther, DataCon, XCon, DataDef, XTCon, XMem, XFunOther, XFunVar, XFunType, XEnv, XTOther, XTConOther, XTFun, XDTCon, XDataScheme, Rec, XDCon, functionDeclaration, functionId, XTVar, XOther, XInstDef, functionEnv, functionBody, MutAccess, XMutAccess, XStringInterpolation)
import qualified AST.Def as Def
import AST.Def (Locality, PP (..), (<+>), PPDef)
import Data.List.NonEmpty (NonEmpty)
import AST.Typed (TC)
import qualified AST.Typed as T
import qualified Data.List.NonEmpty as NonEmpty
import Data.String (fromString)
import Data.Text (Text)
import Data.Functor ((<&>))
import Data.Map (Map)
import Data.Set (Set)

data IMono
type IM = IMono

type instance Rec IM a = a
type instance XLVar IM = Def.UniqueVar
type instance XReturn IM = Expr IM
type instance XNode IM = Type IM
type instance XLamOther IM = Env
type instance XLamVar IM = (Def.UniqueVar, Type IM)
type instance XVarOther IM = Locality
type instance XFunDef IM = EnvDefs
type instance XVar IM = Variable
type instance XVarOther IM = Def.Locality
type instance XCon IM = DataCon IM
type instance XConOther IM = ()
type instance XTCon IM = DataDef IM
type instance XMem IM = Def.UniqueMem
type instance XFunOther IM = FunOther
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
type instance XOther IM = ()  -- TODO: should probably be EnvMod, but I don't want to modify the mStmts code yet.
type instance XInstDef IM = ()
type instance XMutAccess IM = (MutAccess IM, Type IM)
type instance XStringInterpolation IM = Text

newtype EnvDefs = EnvDefs (NonEmpty (Either EnvMod EnvDef))

data EnvDef = EnvDef
  { envDef :: Function IM

  -- this tells us which functions are not yet instantiated and should be excluded.
  , notYetInstantiated :: [Function IM]
  }

data EnvMod = EnvMod
  { assigned :: EnvAssign
  , assignee :: Function IM  -- Type IM  see AST/Mono
  }

data EnvAssign
  = LocalEnv Env
  | EnvFromEnv (NonEmpty EnvAccess)

data EnvAccess = EnvAccess
  { access :: NonEmpty (Function IM, Type IM)
  , accessedEnv :: Env  -- TODO: NOT NEEDED. ITS THE ENVIRONMENT OF LAST FUNCTION.
  }


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
  = Env Def.EnvID [(Variable, Locality, Type IM)] Def.Level
  | RecursiveEnv Def.EnvID IsRecursive

data EnvTypes
  = EnvTypes Def.EnvID [Type IM]
  deriving (Eq, Ord)

type IsRecursive = Bool

envID :: Env -> Def.EnvID
envID = \case
  Env eid _ _ -> eid
  RecursiveEnv eid _ -> eid

envLevel :: Env -> Def.Level
envLevel = \case
  Env _ _ lvl -> lvl
  RecursiveEnv {} -> undefined

data EnvUnion = EnvUnion
  { unionID :: Def.UnionID
  , union :: NonEmpty (T.EnvF (Type IM))  -- TODO: maybe having a typechecked version here is already passe (due to RemoveUnused effectively happening in Typecheck). I don't want to touch this before finishing class functions, because there were no real problems with it yet and I don't want to introduce any subtle bugs (eg. creating too many env defs, too large unions)
  , oldUnion :: T.EnvUnion
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

instance PP EnvDefs where
  pp (EnvDefs eds) = flip Def.ppLines eds $ \case
    Left em -> pp em
    Right ed -> pp ed

instance PP EnvDef where
  pp (EnvDef { envDef, notYetInstantiated = [] }) = pp envDef
  pp (EnvDef { envDef, notYetInstantiated }) = Def.ppBody' pp (pp envDef.functionDeclaration <+>  "|" <+> Def.encloseSepBy "" "" ", " (notYetInstantiated <&> \fn -> pp fn.functionDeclaration.functionId)) envDef.functionBody

instance PP FunOther where
  pp fo = pp fo.envInstantiations <+> pp fo.functionAnnotations

instance PP EnvMod where
  pp em =
    let envAss = "<-" <+> pp (envID $ functionEnv $ functionDeclaration em.assignee)
    in case em.assigned of
      LocalEnv ea -> pp (envID ea) <+> envAss
      EnvFromEnv eas -> Def.ppLines ((<+> envAss) . pp) eas

instance PP EnvAccess where
  pp ea = Def.sepBy "." (NonEmpty.toList $ ea.access <&> \(fn, _) -> pp fn.functionDeclaration.functionId <> "(" <> pp (envID fn.functionDeclaration.functionEnv) <> ")") <> "." <> pp (envID ea.accessedEnv)


instance PP EnvUnion where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> NonEmpty.toList us)

instance PP Env where
  pp = \case
    Env eid vs level -> fromString $ Def.printf "%s(%s)%s" (pp eid) (pp level) $ Def.encloseSepBy "[" "]" ", " (fmap (\(v, l, t) -> pp l <> pp v <+> pp t) vs)
    RecursiveEnv eid isEmpty -> fromString $ Def.printf "%s[REC%s]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

instance PPDef Env where
  ppDef = pp . envID

instance PP EnvTypes where
  pp (EnvTypes eid ts) = pp eid <> pp ts

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


data FunOther = FunOther
  { envInstantiations :: EnvInstantiations
  , functionAnnotations :: [Def.Ann]
  }
type EnvInstantiations = Map Def.EnvID (Set EnvUse)
data EnvUse = EnvUse (Maybe (Function IM)) Env

instance Eq EnvUse where
  EnvUse _ le == EnvUse _ re = le == re

instance Ord EnvUse where
  EnvUse _ le `compare` EnvUse _ re = le `compare` re

instance PP EnvUse where
  pp (EnvUse Nothing e) = pp e
  pp (EnvUse (Just fn) e) = pp fn.functionDeclaration.functionId <+> "=>" <+> pp e

