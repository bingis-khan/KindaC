{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.Mono (module AST.Mono) where
import AST.Common (AnnStmt, Function, Type, Module, XFunDef, XLVar, XReturn, Expr, XExprNode, XMem, XCon, DataCon, XVar, XVarOther, XLamOther, XLamVar, XConOther, DataDef, XTCon, XTFun, XTConOther, XDataOther, Rec, XDCon, XEnv, XFunVar, XFunType, XFunOther, XDTCon, XOther, XTOther, functionId, functionDeclaration, XTVar, XInstDef, functionEnv, functionBody, MutAccess, XMutAccess, XStringInterpolation, TypeF)
import qualified AST.Def as Def
import AST.Def (Locality, PP (..), (<+>))
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.String (fromString)
import Data.Functor ((<&>))
import Data.Text (Text)
import Data.Fix (Fix)


data Mono
type M = Mono

type instance Type M = Fix (TypeF M)
type instance Rec M a = a
type instance Module M = Mod
type instance XFunDef M = EnvInsts
type instance XLVar M = Def.UniqueVar
type instance XReturn M = Expr M
type instance XExprNode M = Type M
type instance XMem M = Def.UniqueMem
type instance XCon M = DataCon M
type instance XVar M = Variable
type instance XVarOther M = Def.Locality
type instance XLamOther M = EnvDef
type instance XLamVar M = (Def.UniqueVar, Type M)
type instance XConOther M = ()
type instance XTCon M = DataDef M
type instance XTFun M = EnvUnion
type instance XTConOther M = ([EnvUnion], [Type M])
type instance XDataOther M = OtherDD
type instance XDCon M = Def.UniqueCon
type instance XEnv M = EnvDef
type instance XFunVar M = Def.UniqueVar
type instance XFunType M = Type M
type instance XFunOther M = [Def.Ann]
type instance XDTCon M = Def.UniqueType
type instance XTOther M = ()
type instance XTVar M = ()
type instance XOther M = ()
type instance XInstDef M = ()
type instance XMutAccess M = (MutAccess M, Type M)
type instance XStringInterpolation M = Text

newtype EnvInsts = EnvInsts (NonEmpty (Either EnvMod EnvInst))

data EnvInst = EnvInst
  { envDef :: Function M  -- multiple functions can use the same environment! so put multiple functions here later for documentation!

  -- this tells us which functions are not yet instantiated and should be excluded.
  , notYetInstantiated :: [Function M]
  }

data EnvMod = EnvMod
  { assigned :: EnvAssign
  , assignee :: Function M
  }

data EnvAssign
  = LocalEnv EnvDef
  | EnvFromEnv (NonEmpty EnvAccess)

data EnvAccess = EnvAccess
  { access :: NonEmpty (Function M, Type M)
  , accessedEnv :: EnvDef  -- TODO: NOT NEEDED. ITS THE ENVIRONMENT OF LAST FUNCTION.
  }

data Variable
  = DefinedFunction (Function M)
  | DefinedVariable Def.UniqueVar
  deriving (Eq, Ord)

type IsRecursive = Bool

data EnvDef = EnvDef Def.EnvID [(Variable, Locality, Type M)] Def.Level

data Env
  = Env EnvDef
  | RecursiveEnv Def.EnvID IsRecursive

data OtherDD = OtherDD
  { appliedTypes :: [Type M]
  -- , ogDataDef :: DataDef T
  }

envID :: Env -> Def.EnvID
envID = \case
  Env (EnvDef eid _ _) -> eid
  RecursiveEnv eid _ -> eid

envDefID :: EnvDef -> Def.EnvID
envDefID (EnvDef eid _ _) = eid

envDefLevel :: EnvDef -> Def.Level
envDefLevel (EnvDef _ _ lvl) = lvl

data EnvUnion = EnvUnion
  { unionID :: Def.UnionID
  , union :: ~(NonEmpty EnvDef)
  }

newtype Mod = Mod { topLevelStatements :: [AnnStmt M] }


---------

areAllEnvsEmpty :: EnvUnion -> Bool
areAllEnvsEmpty envUnion = all isEnvDefEmpty envUnion.union

isEnvEmpty :: Env -> Bool
isEnvEmpty = \case
  RecursiveEnv _ isEmpty -> isEmpty
  Env (EnvDef _ envs _) -> null envs

isEnvDefEmpty :: EnvDef -> Bool
isEnvDefEmpty (EnvDef _ envs _) = null envs


---------

instance Eq EnvUnion where
  u == u' = u.unionID == u'.unionID

instance Ord EnvUnion where
  u `compare` u' = u.unionID `compare` u'.unionID

instance Eq Env where
  e == e' = envID e == envID e'

instance Ord Env where
  e `compare` e' = envID e `compare` envID e'

instance Eq EnvDef where
  e == e' = envDefID e == envDefID e'

instance Ord EnvDef where
  e `compare` e' = envDefID e `compare` envDefID e'


---------
-- PP
--------

instance PP Mod where
  pp m = Def.ppLines m.topLevelStatements

instance PP EnvInsts where
  pp (EnvInsts eds) = Def.ppLines $ eds <&> \case
    Left em -> pp em
    Right ed -> pp ed

instance PP EnvInst where
  pp (EnvInst { envDef, notYetInstantiated = [] }) = pp envDef
  pp (EnvInst { envDef, notYetInstantiated }) = Def.ppBody' pp (fromString $ Def.pf "% \\\\ %" (pp envDef.functionDeclaration) (Def.encloseSepBy "{" "}" ", " $ pp . functionDeclaration <$> notYetInstantiated)) envDef.functionBody -- Def.ppBody' pp (pp envDef.functionDeclaration <+>  "|" <+> Def.encloseSepBy "" "" ", " (notYetInstantiated <&> \fn -> pp fn.functionDeclaration.functionId)) envDef.functionBody

instance PP EnvMod where
  pp em =
    let envAss = "<-" <+> pp (envDefID $ functionEnv $ functionDeclaration em.assignee)
    in case em.assigned of
      LocalEnv ea -> pp (envDefID ea) <+> envAss
      EnvFromEnv eas -> Def.sepBy "\n" $ (<+> envAss) . pp <$> NonEmpty.toList eas

instance PP EnvAccess where
  pp ea = Def.sepBy "." (NonEmpty.toList $ ea.access <&> \(fn, _) -> pp fn.functionDeclaration.functionId <> "(" <> pp (envDefID fn.functionDeclaration.functionEnv) <> ")") <> "." <> pp (envDefID ea.accessedEnv)

instance PP OtherDD where
  pp _ = mempty

instance PP EnvUnion where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> NonEmpty.toList us)

instance PP Env where
  pp = \case
    Env ed -> pp ed
    RecursiveEnv eid isEmpty -> Def.pf "%[REC%]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

instance PP EnvDef where
  pp (EnvDef eid vs _) = pp eid <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp loc <> pp v <+> pp t) vs)


instance PP Variable where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f -> pp f.functionDeclaration.functionId <> "&F"
