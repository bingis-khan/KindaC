{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.IncompleteMono (module AST.IncompleteMono, Def.EnvID) where
import AST.Common (Function, Type, XLVar, XReturn, XExprNode, Expr, XLamOther, XLamVar, XVarOther, XFunDef, XVar, XConOther, DataCon, XCon, DataDef, XTCon, XMem, XFunOther, XFunVar, XFunType, XEnv, XTOther, XTConOther, XTFun, XDTCon, XDataScheme, Rec, XDCon, functionDeclaration, functionId, XTVar, XOther, XInstDef, functionEnv, functionBody, MutAccess, XMutAccess, XStringInterpolation, TypeF)
import qualified AST.Def as Def
import AST.Def (Locality, PP (..), (<+>), PPDef, fmap2)
import Data.List.NonEmpty (NonEmpty)
import qualified AST.Typed as T
import qualified Data.List.NonEmpty as NonEmpty
import Data.Text (Text)
import Data.Functor ((<&>))
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Fix (Fix)
import AST.Typed (TC)

data IMono
type IM = IMono

type instance Type IM = Fix (TypeF IM)
type instance Rec IM a = a
type instance XLVar IM = Def.UniqueVar
type instance XReturn IM = Expr IM
type instance XExprNode IM = Type IM
type instance XLamOther IM = EnvDef
type instance XLamVar IM = (Def.UniqueVar, Type IM)
type instance XVarOther IM = Locality
type instance XFunDef IM = EnvInsts
type instance XVar IM = Variable
type instance XVarOther IM = Def.Locality
type instance XCon IM = DataCon IM
type instance XConOther IM = ()
type instance XTCon IM = DataDef IM
type instance XMem IM = Def.UniqueMem
type instance XFunOther IM = FunOther
type instance XFunVar IM = Def.UniqueVar
type instance XFunType IM = Type IM
type instance XEnv IM = EnvDef
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

newtype EnvInsts = EnvInsts (NonEmpty (Either EnvMod EnvInst))

data EnvInst = EnvInst
  { envDef :: Function IM

  -- this tells us which functions are not yet instantiated and should be excluded.
  , notYetInstantiated :: [Function IM]
  }

data EnvMod = EnvMod
  { assigned :: EnvAssign
  , assignee :: Function IM  -- Type IM  see AST/Mono
  }

data EnvAssign
  = LocalEnv EnvDef
  | EnvFromEnv (NonEmpty EnvAccess)

data EnvAccess = EnvAccess
  { access :: NonEmpty (Function IM, Type IM)
  , accessedEnv :: EnvDef  -- TODO: NOT NEEDED. ITS THE ENVIRONMENT OF LAST FUNCTION.
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

data EnvDef = EnvDef Def.EnvID [(Variable, Locality, Type IM)] Def.Level

data Env
  = Env EnvDef
  | RecursiveEnv Def.EnvID IsRecursive

data EnvTypes
  = EnvTypes Def.EnvID [Type IM]
  deriving (Eq, Ord)

type IsRecursive = Bool

envID :: Env -> Def.EnvID
envID = \case
  Env (EnvDef eid _ _) -> eid
  RecursiveEnv eid _ -> eid

envDefID :: EnvDef -> Def.EnvID
envDefID (EnvDef eid _ _) = eid

envDefLevel :: EnvDef -> Def.Level
envDefLevel (EnvDef _ _ lvl) = lvl

envLevel :: Env -> Def.Level
envLevel = \case
  Env (EnvDef _ _ lvl) -> lvl
  RecursiveEnv {} -> undefined

data EnvUnion = EnvUnion
  { unionID :: Def.UnionID
  , union :: NonEmpty (T.EnvDefF (Type IM))  -- TODO: maybe having a typechecked version here is already passe (due to RemoveUnused effectively happening in Typecheck). I don't want to touch this before finishing class functions, because there were no real problems with it yet and I don't want to introduce any subtle bugs (eg. creating too many env defs, too large unions)
  , oldUnion :: T.EnvUnionF (Type TC)
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

instance Eq EnvDef where
  e == e' = envDefID e == envDefID e'

instance Ord EnvDef where
  e `compare` e' = envDefID e `compare` envDefID e'


instance Eq Env where
  e == e' = envID e == envID e'

instance Ord Env where
  e `compare` e' = envID e `compare` envID e'


-----------
-- PP --
--------

instance PP EnvInsts where
  pp (EnvInsts eds) = Def.ppLines $ eds <&> \case
    Left em -> pp em
    Right ed -> pp ed

instance PP EnvInst where
  pp (EnvInst { envDef, notYetInstantiated = [] }) = pp envDef
  pp (EnvInst { envDef, notYetInstantiated }) = Def.ppBody' pp (pp envDef.functionDeclaration <+>  "|" <+> Def.encloseSepBy "" "" ", " (notYetInstantiated <&> \fn -> pp fn.functionDeclaration.functionId)) envDef.functionBody

instance PP FunOther where
  pp fo = pp fo.envInstantiations <+> pp fo.functionAnnotations

instance PP EnvMod where
  pp em =
    let envAss = "<-" <+> pp (envDefID $ functionEnv $ functionDeclaration em.assignee)
    in case em.assigned of
      LocalEnv ea -> pp (envDefID ea) <+> envAss
      EnvFromEnv eas -> Def.ppLines $ fmap ((<+> envAss) . pp) eas

instance PP EnvAccess where
  pp ea = Def.sepBy "." (NonEmpty.toList $ ea.access <&> \(fn, _) -> pp fn.functionDeclaration.functionId <> "(" <> pp (envDefID fn.functionDeclaration.functionEnv) <> ")") <> "." <> pp (envDefID ea.accessedEnv)


instance PP EnvUnion where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> NonEmpty.toList us)

instance PP EnvDef where
  pp (EnvDef eid vs level) = Def.pf "%(%)%" (pp eid) (pp level) $ Def.encloseSepBy "[" "]" ", " (fmap (\(v, l, t) -> pp l <> pp v <+> pp t) vs)

instance PP Env where
  pp = \case
    Env envdef -> pp envdef
    RecursiveEnv eid isEmpty -> Def.pf "%[REC%]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

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

instance PPDef EnvUnion where
  ppDef = pp . unionID


data FunOther = FunOther
  { envInstantiations :: EnvInstantiations
  , functionAnnotations :: [Def.Ann]
  }
type EnvInstantiations = Map Def.EnvID EnvUses

-- same function with different parameters can have the same environment!!!
-- TODO NEW: wat
newtype EnvUses = EnvUses { fromEnvUses :: Map EnvDef (Set (Function IM)) }

-- instance Eq EnvUse where
--   EnvUse _ le == EnvUse _ re = le == re

-- instance Ord EnvUse where
--   EnvUse _ le `compare` EnvUse _ re = le `compare` re

instance PP EnvUses where
  pp (EnvUses efns) = pp $ fmap (\(e, fns) -> Def.pf "% => %" e fns :: Def.Context) $ fmap2 (Def.ppDef . Set.toList) $ Map.toList efns

instance Semigroup EnvUses where
  EnvUses l <> EnvUses r = EnvUses $ Map.unionWith (<>) l r

instance Monoid EnvUses where
  mempty = EnvUses mempty
