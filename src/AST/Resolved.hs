{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, UndecidableInstances, LambdaCase, OverloadedStrings, OverloadedRecordDot, DuplicateRecordFields, TypeOperators #-}
{-# LANGUAGE TupleSections #-}
module AST.Resolved (module AST.Resolved) where

import AST.Common (LitType, Op, Annotated, UniqueType, UniqueVar, UniqueCon, (:.)(..), Context, Annotated(..), LitType(..), Op(..), ppLines, annotate, (<+>), (<+?>), ppVar, Locality(..), ppBody, ppCon, encloseSepBy, pretty, sepBy, indent, ppTypeInfo, comment, Ann, printf, ppLines', ppMem, MemName, ppRecordMems, UniqueClass, TCon, ppUniqueClass, Binding (..), UnboundTVar (..))
import qualified AST.Typed as T

import Data.Fix (Fix(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')

import Data.Bifunctor (first)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Functor ((<&>))
import Data.String (fromString)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Text (Text)
import AST.Typed (defaultEmpty)




---------------------
-- Data Definition --
---------------------

data DataRec = DR DataDef MemName Type [Ann]  -- we don't know if the var is unique yet (I mean, here, it is... should it be a uniquevar here?)
data DataCon = DC DataDef UniqueCon [Type] [Ann]
data DataDef = DD UniqueType [TVar] (Either (NonEmpty DataRec) [DataCon]) [Ann]

instance Eq DataCon where
  DC _ uc _ _ == DC _ uc' _ _ = uc == uc'

instance Eq DataDef where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord DataDef where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'



----------
-- Type --
----------

data TVar = TV
  { fromTV :: Text
  , binding :: Binding
  , tvClasses :: Set Class
  }

instance Eq TVar where
  tv == tv' = tv.fromTV == tv'.fromTV && tv.binding == tv'.binding

instance Ord TVar where
  tv `compare` tv' = (tv.fromTV, tv.binding) `compare` (tv'.fromTV, tv'.binding)

bindTVar :: Binding -> UnboundTVar -> TVar
bindTVar b (UTV tvname) = TV tvname b mempty

data TypeF a
  = TCon Datatype [a]
  | TVar TVar
  | TFun [a] a
  deriving (Functor, Foldable, Traversable)
type Type = Fix TypeF

data ClassTypeF a
  = Self
  | NormalType (TypeF a)
  deriving (Functor, Foldable, Traversable)
type ClassType = Fix ClassTypeF


----------------
-- Expression --
----------------

newtype Env = Env { fromEnv :: [(VariableProto, Locality)]}
instance Eq Env where
  Env env == Env env' = fmap (first asPUniqueVar) env == fmap (first asPUniqueVar) env'

instance Ord Env where
  Env env `compare` Env env' = fmap (first asPUniqueVar) env `compare` fmap (first asPUniqueVar) env'


data ExprF a
  = Lit LitType
  | Var Locality Variable
  | Con Constructor

  | RecCon Datatype (NonEmpty (MemName, a))
  | RecUpdate a (NonEmpty (MemName, a))
  | MemAccess a MemName  -- TODO: should this be unique var? At this point, we don't really know which accessor it is.

  | Op a Op a
  | Call a [a]
  | As a Type
  | Lam UniqueVar Env [UniqueVar] a  -- dafuq do we need the UniqueVar in lambda for????
  deriving (Functor, Foldable, Traversable)
type Expr = Fix ExprF


-- A variable prototype.
-- the only difference is that classes don't have assigned instances.
data VariableProto
  = PDefinedVariable UniqueVar

  | PDefinedFunction Function
  | PExternalFunction T.Function  -- it's only defined as external, because it's already typed. nothing else should change.

  | PDefinedClassFunction ClassFunDec
  | PExternalClassFunction T.ClassFunDec
  deriving (Eq, Ord)


type PossibleInstances = Map Datatype Inst
type ScopeSnapshot = Map Class PossibleInstances

data Variable
  = DefinedVariable UniqueVar

  | DefinedFunction Function ScopeSnapshot
  | ExternalFunction T.Function ScopeSnapshot  -- it's only defined as external, because it's already typed. nothing else should change.

  | DefinedClassFunction ClassFunDec ScopeSnapshot  -- we have to track which instances were visible at the time of this scope.
  | ExternalClassFunction T.ClassFunDec ScopeSnapshot
  deriving (Eq, Ord)


asUniqueVar :: Variable -> UniqueVar
asUniqueVar = \case
  DefinedVariable var -> var

  DefinedFunction (Function { functionDeclaration = FD { functionId = fid } }) _ -> fid
  ExternalFunction (T.Function { T.functionDeclaration = T.FD _ uv _ _ _ _ _ }) _ -> uv

  DefinedClassFunction (CFD _ uv _ _) _ -> uv
  ExternalClassFunction (T.CFD _ uv _ _) _ -> uv

asPUniqueVar :: VariableProto -> UniqueVar
asPUniqueVar = \case
  PDefinedVariable var -> var

  PDefinedFunction (Function { functionDeclaration = FD { functionId = fid } }) -> fid
  PExternalFunction (T.Function { T.functionDeclaration = T.FD _ uv _ _ _ _ _ }) -> uv

  PDefinedClassFunction (CFD _ uv _ _) -> uv
  PExternalClassFunction (T.CFD _ uv _ _) -> uv

asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  DefinedFunction fn _ -> PDefinedFunction fn
  ExternalFunction fn _ -> PExternalFunction fn
  DefinedClassFunction cd _ -> PDefinedClassFunction cd
  ExternalClassFunction cd _ -> PExternalClassFunction cd


data Constructor
  = DefinedConstructor DataCon
  | ExternalConstructor T.DataCon

data Datatype
  = DefinedDatatype DataDef
  | ExternalDatatype T.DataDef
  deriving (Eq, Ord)

tryGetMembersFromDatatype :: Datatype -> Maybe (NonEmpty MemName)
tryGetMembersFromDatatype = \case
  DefinedDatatype (DD _ _ (Left recs) _) -> Just $ recs <&> \(DR _ mem _ _) -> mem
  ExternalDatatype (T.DD _ _ (Left recs) _) -> Just $ recs <&> \(T.DR _ mem _ _) -> mem
  _ -> Nothing


----------
-- Case --
----------

data DeconF a
  = CaseVariable UniqueVar
  | CaseConstructor Constructor [a]
  | CaseRecord Datatype (NonEmpty (MemName, a))  -- ISSUE(record-as-separate-type): ya know
  deriving (Functor)
type Decon = Fix DeconF

data Case expr a = Case
  { deconstruction :: Decon
  , caseCondition :: Maybe expr
  , body :: NonEmpty a
  } deriving (Functor, Foldable, Traversable)



---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | Mutation UniqueVar Locality expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (Case expr a))
  | ExprStmt expr
  | Return expr

  -- the place where env should be initialized.
  | EnvDef Function
  | InstDefDef InstDef
  deriving (Functor, Foldable, Traversable)

type Stmt = StmtF Expr AnnStmt
type AnnStmt = Fix (Annotated :. StmtF Expr)



--------------
-- Function --
--------------

data FunDec = FD
  { functionEnv :: Env
  , functionId :: UniqueVar
  , functionParameters :: [(Decon, Maybe Type)]
  , functionReturnType :: Maybe Type
  }

instance Eq FunDec where
  FD _ uv _ _ == FD _ uv' _ _ = uv == uv'

data Function = Function
  { functionDeclaration :: FunDec
  , functionBody :: NonEmpty AnnStmt
  }

instance Eq Function where
  Function { functionDeclaration = fd } == Function { functionDeclaration = fd' } = fd == fd'

instance Ord Function where
  fn `compare` fn' = fn.functionDeclaration.functionId `compare` fn'.functionDeclaration.functionId


------------------
-- Typeclasses --
------------------

data ClassDef = ClassDef
  { classID :: UniqueClass
  , classDependentTypes :: [DependentType]
  , classFunctions :: [ClassFunDec]
  }

data Class
  = DefinedClass ClassDef
  | ExternalClass T.ClassDef
  deriving (Eq, Ord)

data InstDef = InstDef
  { instClass :: Class
  , instType :: (Datatype, [TVar])
  , instDependentTypes :: [(DependentType, Type)]
  , instFunctions :: [InstanceFunction]
  }

data Inst
  = DefinedInst InstDef
  | ExternalInst T.InstDef
  deriving (Eq, Ord)


newtype ClassConstraints = CCs (Map TVar (Set Class))

data DependentType = Dep TCon UniqueClass

data ClassFunDec = CFD ClassDef UniqueVar [(Decon, ClassType)] ClassType

data InstanceFunction = InstanceFunction
  { classFunctionDeclaration :: FunDec
  , classFunctionPrototypeUniqueVar :: UniqueVar
  , classFunctionBody        :: NonEmpty AnnStmt
  }


instance Eq ClassDef where
  cd == cd' = cd.classID == cd'.classID

instance Ord ClassDef where
  cd `compare` cd' = cd.classID `compare` cd'.classID

instance Eq ClassFunDec where
  CFD _ uv _ _ == CFD _ uv' _ _ = uv == uv'

instance Ord ClassFunDec where
  CFD _ uv _ _ `compare` CFD _ uv' _ _ = uv `compare` uv'

instance Eq InstDef where
  instdef == instdef' = instdef.instClass == instdef'.instClass && instdef.instType == instdef'.instType

instance Ord InstDef where
  instdef `compare` instdef' = (instdef.instClass, instdef.instType) `compare` (instdef'.instClass, instdef'.instType)


asUniqueClass :: Class -> UniqueClass
asUniqueClass = \case
  DefinedClass cd -> cd.classID
  ExternalClass cd -> cd.classID


---------------
-- Module --
---------------

data Module = Mod
  { toplevel :: [AnnStmt]
  , exports :: Exports

  -- we must also typecheck functions / datatypes that were not referenced!!!
  , functions :: [Function]
  , datatypes :: [DataDef]
  , classes :: [ClassDef]
  , instances :: [InstDef]
  }

data Exports = Exports
  { variables :: [UniqueVar]
  , functions :: [Function]
  , datatypes :: [DataDef]
  , classes   :: [ClassDef]
  , instances :: [InstDef]
  }


-- Template haskell shit.
$(deriveBifunctor ''Case)
$(deriveBifoldable ''Case)
$(deriveBitraversable ''Case)

$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)
$(deriveBitraversable ''StmtF)




----------------------
-- Printing the AST --
----------------------

pModule :: Module -> Context
pModule modul = ppLines'
  [ ppLines tFunction modul.functions
  , tStmts modul.toplevel
  ]

tStmts :: [AnnStmt] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt -> Context
tAnnStmt (Fix (O (Annotated ann stmt))) = annotate ann $ tStmt stmt

tStmt :: Stmt -> Context
tStmt stmt = case first tExpr stmt of
  Print e -> "print" <+> e
  Assignment v e -> ppVar Local v <+> "=" <+> e
  Pass -> "pass"
  Mutation v loc e -> ppVar loc v <+> "<=" <+> e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> ifCond ) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  Switch switch cases ->
    ppBody tCase switch cases
  ExprStmt e -> e
  Return e -> "return" <+> e
  EnvDef fn -> fromString $ printf "[ENV]: %s" $ tEnv fn.functionDeclaration.functionEnv
  InstDefDef inst -> tInst inst

tCase :: Case Context AnnStmt -> Context
tCase kase = tBody (tDecon kase.deconstruction <+?> kase.caseCondition) kase.body

tDecon :: Decon -> Context
tDecon = cata $ \case
  CaseVariable uv -> ppVar Local uv
  CaseConstructor uc [] -> ppCon $ asUniqueCon uc
  CaseConstructor uc args@(_:_) -> ppCon (asUniqueCon uc) <> encloseSepBy "(" ")" ", " args
  CaseRecord dd args -> ppTypeInfo (asUniqueType dd) <+> ppRecordMems args

tExpr :: Expr -> Context
tExpr = cata $ \case
  Lit (LInt x) -> pretty x
  Lit (LFloat f) -> pretty $ show f
  Var l v ->
    let post = case v of
          DefinedVariable _ -> ""
          DefinedFunction _ _ -> "F"
          ExternalFunction _ _ -> "EF"
          DefinedClassFunction (CFD cd _ _ _) insts -> "C" <> tSelectedInsts (Map.elems (defaultEmpty (DefinedClass cd) insts))
          ExternalClassFunction _ insts -> "EC"
    in ppVar l (asUniqueVar v) <> post
  Con c -> ppCon (asUniqueCon c)

  
  RecCon dd inst -> ppTypeInfo (asUniqueType dd) <+> ppRecordMems inst
  RecUpdate c upd -> c <+> ppRecordMems upd
  MemAccess c mem -> c <> "." <> ppMem mem

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x at -> x <+> "as" <+> tType at
  Lam uv lenv params e -> ppVar Local uv <> tEnv lenv <+> sepBy " " (map (ppVar Local) params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="

tSelectedInsts :: [Inst] -> Context
tSelectedInsts insts = 
  let instdds = sepBy ", " $ insts <&> ppTypeInfo . asUniqueType . \case
        DefinedInst ins -> fst ins.instType
        ExternalInst ins -> ExternalDatatype $ fst ins.instType
  in fromString $ printf "[%s]" instdds


tDataDef :: DataDef -> Context
tDataDef (DD tid tvs cons _) = indent (foldl' (\x (TV y _ _) -> x <+> pretty y) (ppTypeInfo tid) tvs) $ tConRec cons

tConRec :: Either (NonEmpty DataRec) [DataCon] -> Context
tConRec (Left dr) = ppLines tRecDef dr
tConRec (Right dc) = ppLines tConDef dc

tRecDef :: DataRec -> Context
tRecDef (DR _ uv t _) = ppMem uv <+> tType t

tConDef :: DataCon -> Context
tConDef (DC _ g t anns) = annotate anns $ foldl' (<+>) (ppCon g) $ tTypes t

tFunDec :: FunDec -> Context
tFunDec (FD fenv v params retType) = comment (tEnv fenv) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> tDecon pName <+?> fmap tType pType) params) <+?> fmap tType retType

tFunction :: Function -> Context
tFunction fn = tBody (tFunDec fn.functionDeclaration) fn.functionBody

tInst :: InstDef -> Context
tInst inst =
  let
    header = "inst" <+> ppUniqueClass (asUniqueClass inst.instClass) <+> ppTypeInfo (asUniqueType (fst inst.instType)) <+> sepBy " " (ppTVar <$> snd inst.instType)
  in ppBody
    (\ifn -> tBody (tFunDec ifn.classFunctionDeclaration) ifn.classFunctionBody)
    header
    inst.instFunctions

tConstraints :: ClassConstraints -> Context
tConstraints (CCs ccs) | null ccs = ""
tConstraints (CCs ccs) = "<=" <+> sepBy ", " (map tCC $ concatMap (\(tv, klasses) -> map (,tv) $ Set.toList klasses) (Map.toList ccs))
  where
    tCC (klass, tv) = ppUniqueClass (asUniqueClass klass) <+> ppTVar tv

tTypes :: Functor t => t Type -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type -> Context
tType = cata $ \case
  TCon con params ->
    foldl' (<+>) (ppTypeInfo (asUniqueType con)) params
  TVar tv -> ppTVar tv
  TFun args ret -> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

tEnv :: Env -> Context
tEnv (Env env) = encloseSepBy "[" "]" ", " $ env <&> \(v, l) -> ppVar l $ asPUniqueVar v

tBody :: Foldable f => Context -> f AnnStmt -> Context
tBody = ppBody tAnnStmt

ppTVar :: TVar -> Context
ppTVar (TV tv b _) =
  let bindingCtx = case b of
        BindByType ut -> ppTypeInfo ut
        BindByVar uv -> ppVar Local uv
        BindByInst uc -> ppUniqueClass uc
  in pretty tv <> "<" <> bindingCtx <> ">"

asUniqueCon :: Constructor -> UniqueCon
asUniqueCon = \case
  DefinedConstructor (DC _ uc _ _) -> uc
  ExternalConstructor (T.DC _ uc _ _) -> uc

asUniqueType :: Datatype -> UniqueType
asUniqueType (DefinedDatatype (DD ut _ _ _)) = ut
asUniqueType (ExternalDatatype (T.DD ut _ _ _)) = ut
