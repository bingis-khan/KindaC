{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
module AST.Typed (module AST.Typed) where

import AST.Common (LitType (..), Op (..), Annotated (..), Ann, UniqueType, UniqueVar, UniqueCon, Locality (Local), Context, ppLines, annotate, (<+>), ppVar, (<+?>), pretty, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppBody, UnionID, EnvID, ppUnionID, ppEnvID, (:.) (..), ppLines', printf, ctx, ppSet, MemName, ppMem, ppRecordMems, UniqueClass, ppUniqueClass, Binding (..), mustOr, UniqueClassInstantiation)

import Data.Eq.Deriving
import Data.Ord.Deriving
import Data.Fix (Fix (..))
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.Functor.Classes (Eq1 (liftEq), Ord1 (..))
import Data.Biapplicative (first, bimap)
import Data.Functor.Foldable (cata, project)
import Data.Foldable ( foldl', fold )
import Data.Text (Text)
import Data.String (fromString)
import Data.Functor ((<&>))
import Data.Set (Set)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Data.Foldable (find)
import qualified AST.Common as Common
import qualified Data.Set as Set
import Data.Maybe (mapMaybe, fromMaybe)
import Data.IORef (IORef)



---------------------
-- Data Definition --
---------------------

data DataRec = DR DataDef MemName Type [Ann]
data DataCon = DC DataDef UniqueCon [Type] [Ann]
data DataDef = DD UniqueType Scheme (Either (NonEmpty DataRec) [DataCon]) [Ann]

instance Eq DataDef where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord DataDef where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'

instance Eq DataCon where
  DC _ uc _ _ == DC _ uc' _ _ = uc == (uc' :: UniqueCon)

instance Ord DataCon where
  DC _ uc _ _ `compare` DC _ uc' _ _ = uc `compare` (uc' :: UniqueCon)

instance Eq DataRec where
  DR (DD ut _ _ _) uv _ _ == DR (DD ut' _ _ _) uv' _ _ = ut == ut' && uv == (uv' :: MemName)

instance Ord DataRec where
  DR (DD ut _ _ _) uc _ _ `compare` DR (DD ut' _ _ _) uc' _ _ = (ut, uc) `compare` (ut', uc' :: MemName)


----------
-- Type --
----------

data EnvF t
  = Env EnvID [(Variable, Locality, t)] (Map VariableProto Locality) Int -- t is here, because of recursion schemes. UniqueVar, because we don't know which environments will be used in the end. We will replace it with a `Variable` equivalent AFTER we monomorphise.
  -- The last map is a HACK
  | RecursiveEnv EnvID IsEmpty  -- Recursive functions won't have access to their environment while typechecking... kinda stupid. ehh... but we're solving an actual issue here. `IsEmpty` is used in Mono to let us know if this function's environment was empty or not.
  deriving (Functor, Foldable, Traversable)
type Env = EnvF Type

type IsEmpty = Bool

envID :: EnvF t -> EnvID
envID = \case
  Env eid _ _ _ -> eid
  RecursiveEnv eid _ -> eid


instance Eq t => Eq (EnvF t) where
  Env lid lts _ _ == Env rid rts _ _ = lid == rid && (lts <&> \(_, _, x) -> x) == (rts <&> \(_, _, x) -> x)
  l == r  = envID l == envID r

instance Ord t => Ord (EnvF t) where
  Env lid lts _ _ `compare` Env rid rts _ _ = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)
  l `compare` r = envID l `compare` envID r

instance Eq1 EnvF where
  liftEq f (Env lid lts _ _) (Env rid rts _ _) = lid == rid && and (zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts)
  liftEq _ l r = envID l == envID r

instance Ord1 EnvF where
  liftCompare f (Env lid lts _ _) (Env rid rts _ _) = case lid `compare` rid of
    EQ -> mconcat $ zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts
    ord -> ord
  liftCompare _ l r = envID l `compare` envID r


data EnvUnionF t = EnvUnion
  { unionID :: UnionID
  , union :: [EnvF t]  -- List can be empty for types written by the programmer (which also don't have any other function's environment yet). This is okay, because functions are not yet monomorphised.
  } deriving (Functor, Foldable, Traversable)
type EnvUnion = EnvUnionF Type


-- TODO: wait, why did I need comparing of parameters in unions?!?!?!?!?
-- TODO later: uhhhhhhh
instance Eq1 EnvUnionF where
  liftEq f u u' = u.unionID == u'.unionID && and (zipWith (liftEq f) u.union u'.union)

instance Ord1 EnvUnionF where
  liftCompare f u u' = case u.unionID `compare` u'.unionID of
    EQ -> mconcat $ zipWith (liftCompare f) u.union u'.union
    cmp -> cmp

instance Eq t => Eq (EnvUnionF t) where
  EnvUnion { unionID = l, union = lu } == EnvUnion { unionID = r, union = ru } = l == r && lu == ru

instance Ord t => Ord (EnvUnionF t) where
  EnvUnion { unionID = l, union = lu } `compare` EnvUnion { unionID = r, union = ru } = (l, lu) `compare` (r, ru)



data TyVar = TyV { fromTyV :: Text, tyvConstraints :: [(ClassDef, PossibleInstances)] }

instance Eq TyVar where
  tyv == tyv' = tyv.fromTyV == tyv'.fromTyV

instance Ord TyVar where
  tyv `compare` tyv' = tyv.fromTyV `compare` tyv'.fromTyV

data TVar = TV
  { fromTV :: Text
  , binding :: Binding
  , tvConstraints :: Set ClassDef
  }

instance Eq TVar where
  tv == tv' = tv.fromTV == tv'.fromTV && tv.binding == tv'.binding

instance Ord TVar where
  tv `compare` tv' = (tv.fromTV, tv.binding) `compare` (tv'.fromTV, tv'.binding)

data TypeF a
  = TCon DataDef [a] [EnvUnionF a]
  | TVar TVar
  | TFun (EnvUnionF a) [a] a
  | TyVar TyVar
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type Type = Fix TypeF

-- Literally R.ClassType, but it would be a circular reference.
data ClassTypeF a
  = CTCon DataDef [a]
  | CTVar TVar
  | CTFun UnionID [a] a  -- UnionID: empty union.
  | Self
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type ClassType = Fix ClassTypeF



--------------
-- Function --
--------------

data FunDec = FD
  { functionEnv :: Env
  , functionId :: UniqueVar
  , functionParameters :: [(Decon, Type)]
  , functionReturnType :: Type
  , functionScheme :: Scheme
  , functionAssociations :: [FunctionTypeAssociation]
  , functionClassInstantiationAssociations :: ClassInstantiationAssocs
  }

-- TODO: note, "recursive" calls to instance functions redefine UCI. This is a quick fix. I'll have to rethink how all of it is structured.
type ClassInstantiationAssocs = Map UniqueClassInstantiation [(Type, ([Type], InstanceFunction), Int)]

instance Eq FunDec where
  FD _ uv _ _ _ _ _ == FD _ uv' _ _ _ _ _ = uv == uv'

data Function = Function
  { functionDeclaration :: FunDec
  , functionBody :: NonEmpty AnnStmt
  }

instance Eq Function where
  Function { functionDeclaration = fd } == Function { functionDeclaration = fd' } = fd == fd'

instance Ord Function where
  fn `compare` fn' = fn.functionDeclaration.functionId `compare` fn'.functionDeclaration.functionId

data FunctionTypeAssociation = FunctionTypeAssociation TVar Type ClassFunDec UniqueClassInstantiation
data TypeAssociation = TypeAssociation Type Type ClassFunDec UniqueClassInstantiation


------------------
-- Typeclasses --
------------------


data ClassDef = ClassDef
  { classID :: UniqueClass
  -- , classDependentTypes :: [DependentType]
  , classFunctions :: [ClassFunDec]
  }

data InstDef = InstDef
  { instClass :: ClassDef
  , instType :: (DataDef, [TVar])
  -- , instDependentTypes :: [(DependentType, Type)]
  , instFunctions :: [InstanceFunction]
  }

data InstanceFunction = InstanceFunction
  { instFunction :: Function
  , instFunctionClassUniqueVar :: UniqueVar
  , instDef :: InstDef
  }

selfType :: InstDef -> Type
selfType instdef =
  let (dd, tvs) = instdef.instType
  in Fix $ TCon dd (Fix . TVar <$> tvs) []

-- data DependentType = Dep TCon UniqueClass

data ClassConstraint = CC ClassDef TVar deriving Eq

data ClassFunDec = CFD ClassDef UniqueVar [(Decon, ClassType)] ClassType


instance Eq ClassDef where
  cd == cd' = cd.classID == cd'.classID

instance Ord ClassDef where
  cd `compare` cd' = cd.classID `compare` cd'.classID

instance Eq ClassFunDec where
  CFD _ uv _ _ == CFD _ uv' _ _ = uv == uv'

instance Ord ClassFunDec where
  CFD _ uv _ _ `compare` CFD _ uv' _ _ = uv `compare` uv'

instance Eq InstDef where
  inst == inst' = inst.instClass == inst'.instClass && fst inst.instType == fst inst'.instType

instance Ord InstDef where
  inst `compare` inst' = (inst.instClass, fst inst.instType) `compare` (inst'.instClass, fst inst'.instType)



----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality Variable
  | Con EnvID DataCon -- NOTE: EnvID is an ID of an *empty* environment. All constructors have an empty environment, so when an environment is needed, use this.

  | RecCon DataDef (NonEmpty (MemName, a))
  | RecUpdate a (NonEmpty (MemName, a))
  | MemAccess a MemName

  | Op a Op a
  | Call a [a]
  | Lam Env [(UniqueVar, Type)] a

  | As a Type
  deriving (Functor, Foldable, Traversable)

data TypedExpr a = TypedExpr Type (ExprF a) deriving (Functor, Foldable, Traversable)
type Expr = Fix TypedExpr

getType :: Expr -> Type
getType (Fix (TypedExpr t _)) = t


type PossibleInstances = Map DataDef InstDef
type ScopeSnapshot = Map ClassDef PossibleInstances

data Variable
  = DefinedVariable UniqueVar
  | DefinedFunction Function ScopeSnapshot [Type]
  | DefinedClassFunction ClassFunDec ScopeSnapshot Type UniqueClassInstantiation  -- which class function and which instances are visible at this point. 


data VariableProto
  = PDefinedVariable UniqueVar
  | PDefinedFunction Function
  | PDefinedClassFunction ClassFunDec
  deriving (Eq, Ord)


asUniqueVar :: Variable -> UniqueVar
asUniqueVar = \case
  DefinedVariable uv -> uv
  DefinedFunction fn _ _ -> fn.functionDeclaration.functionId
  DefinedClassFunction (CFD _ uv _ _) _ _ _ -> uv


asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable uv -> PDefinedVariable uv
  DefinedFunction fn _ _ -> PDefinedFunction fn
  DefinedClassFunction cd _ _ _ -> PDefinedClassFunction cd


-- scheme for both mapping tvars and unions
data Scheme = Scheme [TVar] [EnvUnion]



----------
-- Case --
----------

data DeconF a
  = CaseVariable Type UniqueVar
  | CaseConstructor Type DataCon [a]
  | CaseRecord Type DataDef (NonEmpty (MemName, a))
  deriving (Functor)
type Decon = Fix DeconF

data Case expr a = Case
  { deconstruction :: Decon
  , caseCondition :: Maybe expr
  , body :: NonEmpty a
  } deriving (Functor, Foldable, Traversable)


decon2type :: Decon -> Type
decon2type (Fix dec) = case dec of
  CaseVariable t _ -> t
  CaseConstructor t _ _ -> t
  CaseRecord t _ _ -> t



---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Mutation UniqueVar Locality expr
  | Pass

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (Case expr a))
  | ExprStmt expr
  | Return expr

  | EnvDef Function
  | InstDefDef InstDef
  deriving (Functor, Foldable, Traversable)


-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
type Stmt = StmtF Expr AnnStmt
type AnnStmt = Fix (Annotated :. StmtF Expr)

deannAnnStmt :: (Annotated :. StmtF Expr) a -> StmtF Expr a
deannAnnStmt (O (Annotated _ stmt)) = stmt

$(deriveBifunctor ''Case)
$(deriveBifoldable ''Case)
$(deriveBitraversable ''Case)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)
$(deriveBitraversable ''StmtF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)
-- $(deriveEq ''Variable)
-- $(deriveOrd ''Variable)

instance Eq Variable where
  v == v' = case (v, v') of
    (DefinedVariable uv, DefinedVariable uv') -> uv == uv'
    (DefinedFunction fn ss ts, DefinedFunction fn' ss' ts') -> (fn, ss, ts) == (fn', ss', ts')
    (DefinedClassFunction cfd pi self _, DefinedClassFunction cfd' pi' self' _) -> (cfd, pi, self) == (cfd', pi', self')
    _ -> False

instance Ord Variable where
  v `compare` v' = case (v, v') of
    (DefinedVariable uv, DefinedVariable uv') -> uv `compare` uv'
    (DefinedFunction fn ss ts, DefinedFunction fn' ss' ts') -> (fn, ss, ts) `compare` (fn', ss', ts')
    (DefinedClassFunction cfd pi self _, DefinedClassFunction cfd' pi' self' _) -> (cfd, pi, self) `compare` (cfd', pi', self')

    (DefinedVariable _, _) -> LT

    (DefinedFunction {}, DefinedVariable _) -> GT
    (DefinedFunction {}, _) -> LT

    (DefinedClassFunction {}, _) -> GT

---------------
-- Module --
---------------

data Module = Mod
  { toplevelStatements :: [AnnStmt]
  , exports :: Exports
  , classInstantiationAssociations :: ClassInstantiationAssocs  -- TODO: another reason this solution can't stay: how do we "connect" the classInstantiation associations?

  -- not needed, used for printing the AST.
  , functions :: [Function]
  , datatypes :: [DataDef]
  , classes   :: [ClassDef]
  , instances :: [InstDef]
  }

data Exports = Exports
  { variables :: [UniqueVar]
  , functions :: [Function]
  , datatypes :: [DataDef]
  , classes   :: [ClassDef]
  , instances :: [InstDef]
  }



--------------------
-- Utility

isUnionEmpty :: EnvUnionF t -> Bool
isUnionEmpty (EnvUnion _ []) = True
isUnionEmpty _ = False


-- This is currently how we extract unions from types.
-- This needs to be done, because custom types need to track which unions were used.
-- TODO: this should probably be made better. Maybe store those unions in DataDef?
extractUnionsFromDataType :: DataDef -> [EnvUnion]
extractUnionsFromDataType (DD _ _ (Right dcs) _) =
  concatMap extractUnionsFromConstructor dcs

extractUnionsFromDataType (DD _ _ (Left drs) _) =
  concatMap extractUnionsFromRecord drs

extractUnionsFromConstructor :: DataCon -> [EnvUnion]
extractUnionsFromConstructor (DC (DD ut _ _ _) _ ts _) = concatMap (mapUnion ut) ts

extractUnionsFromRecord :: DataRec -> [EnvUnion]
extractUnionsFromRecord (DR (DD ut _ _ _) _ t _) = mapUnion ut t

-- TODO: clean up all the mapUnion shit. think about proper structure.
mapUnion :: UniqueType -> Type -> [EnvUnion]
mapUnion ut (Fix t) = case t of
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  TCon (DD tut _ _ _) paramts conUnions
    -- breaks cycle with self referential datatypes.
    | tut == ut -> concatMap (mapUnion ut) paramts
    | otherwise -> conUnions <> concatMap (mapUnion ut) paramts

  TFun u args ret -> [u] <> concatMap (mapUnion ut) args <> mapUnion ut ret
  TVar _ -> []
  TyVar _ -> []


-- TODO: in the future, make it return a possible error.
selectInstanceFunction :: Map TVar (Map ClassDef InstDef) -> ClassFunDec -> Type -> PossibleInstances -> (InstanceFunction, InstDef)
selectInstanceFunction _ (CFD _ uv _ _) (Fix (TCon dd@(DD ut _ _ _) _ _)) insts =
  let inst = mustOr (printf "[COMPILER ERROR]: The instance for %s must have existed by this point! %s" (ppTypeInfo ut) (tSelectedInsts (Map.elems insts))) $ insts !? dd
  in (,inst) $ mustOr (printf "[COMPILER ERROR]: Could not select function %s bruh," (ppVar Local uv)) $ find (\fn -> fn.instFunctionClassUniqueVar == uv) inst.instFunctions

selectInstanceFunction backing (CFD cd uv _ _) (Fix (TVar tv)) _ =
  let inst = mustOr (printf "[COMPILER ERROR]: TVar %s not mapped for some reason! Content of backing:\n%s." (tTVar tv) (pBacking backing)) $ backing !? tv >>= (!? cd)
  in (,inst) $ mustOr (printf "[COMPILER ERROR]: Could not select function %s bruh," (ppVar Local uv)) $ find (\fn -> fn.instFunctionClassUniqueVar == uv) inst.instFunctions

selectInstanceFunction _ _ self _ = error $ printf "[COMPILER ERROR]: INCORRECT TYPE AYO. CANNOT SELECT INSTANCE FOR TYPE %s." (Common.sctx (tType self))


pBacking :: Map TVar (Map ClassDef InstDef) -> Context
pBacking = Common.ppMap . fmap (bimap tTVar pInsts) . Map.toList
  where pInsts = Common.ppMap . fmap (bimap tClassName tInst) . Map.toList

-- TODO: ONG ITS SO BADD
mapType :: Type -> Type -> Map TVar DataDef
mapType lpt rpt = case (project lpt, project rpt) of
  (TVar tv, TCon dd _ _)-> Map.singleton tv dd
  (TVar {}, TFun {}) -> mempty

  (TFun _ lts lt, TFun _ rts rt) -> fold (zipWith mapType lts rts) <> mapType lt rt
  (TCon _ lts _, TCon _ rts _) -> fold $ zipWith mapType lts rts

  _ -> undefined

findTVars :: Type -> Set TVar
findTVars = cata $ \case
  TVar tv -> Set.singleton tv
  TFun _ params ret -> fold params <> ret
  t -> fold t


mkInstanceSelector :: Type -> Map TVar DataDef -> ScopeSnapshot -> Map TVar (Map ClassDef InstDef)
mkInstanceSelector from tvddm snapshot =
  let
      tvars = findTVars from
  in flip Map.fromSet tvars $ \tv ->
    case tvddm !? tv of
      Just dd ->
        Map.fromList $ flip mapMaybe (Set.toList tv.tvConstraints) $ \cd -> case snapshot !? cd of
          Just pis -> case pis !? dd of
            Just instdef -> Just (cd, instdef)
            Nothing -> Nothing
          Nothing -> Nothing
      Nothing -> mempty


defaultEmpty :: (Monoid v, Ord k) => k -> Map k v -> v
defaultEmpty k m = fromMaybe mempty $ m !? k



--------------------------------------------------------------------------------------
-- Printing the AST

tModule :: Module -> Context
tModule m =
  ppLines'
    [ ppLines tDataDef m.datatypes
    -- , ppLines tFunction m.functions
    , tStmts m.toplevelStatements
    ]

tStmtsOnly :: [AnnStmt] -> String
tStmtsOnly = ctx tStmts

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
    tBody ("if" <+> ifCond) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  Switch switch cases ->
    ppBody tCase switch cases
  ExprStmt e -> e
  Return e -> "return" <+> e
  EnvDef fn -> ppLines'
    [ "$$$:" <+> tEnv fn.functionDeclaration.functionEnv
    , tFunction fn
    ]
  InstDefDef inst -> tInst inst

tCase :: Case Context AnnStmt -> Context
tCase kase = tBody (tDecon kase.deconstruction <+?> kase.caseCondition) kase.body

tDecon :: Decon -> Context
tDecon = cata $ \case
  CaseVariable _ uv -> ppVar Local uv
  CaseConstructor t (DC _ uc _ _) [] -> ppCon uc <> " :: " <> tType t
  CaseConstructor t (DC _ uc _ _) args@(_:_) -> ppCon uc <> encloseSepBy "(" ")" ", " args <> " :: " <> tType t
  CaseRecord t (DD ut _ _ _) args -> ppTypeInfo ut <+> ppRecordMems args <+> "::" <+> tType t

tExpr :: Expr -> Context
tExpr = cata $ \(TypedExpr et expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType et <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Lit (LFloat fl) -> pretty $ show fl
  Var l (DefinedVariable v) -> ppVar l v
  Var l (DefinedFunction f _ _) -> ppVar l f.functionDeclaration.functionId <> "&F"
  Var l (DefinedClassFunction (CFD cd uv _ _) insts _ uci)  -> ppVar l uv <> "&" <> fromString (show uci) <>"&C" <> tSelectedInsts (Map.elems (defaultEmpty cd insts))
  Con _ (DC _ uc _ _) -> ppCon uc

  RecCon (DD ut _ _ _) inst -> ppTypeInfo ut <+> ppRecordMems inst
  RecUpdate c upd -> c <+> ppRecordMems upd
  MemAccess c mem -> c <> "." <> ppMem mem

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  Lam lenv params e -> tEnv lenv <+> sepBy " " (map (\(v, t) -> ppVar Local v <+> tType t) params) <> ":" <+> e
  As e t -> e <+> "as" <+> tType t
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="

tSelectedInsts :: [InstDef] -> Context
tSelectedInsts insts =
  let instdds = sepBy ", " $ insts <&> \ins -> let (DD ut _ _ _) = fst ins.instType in ppTypeInfo ut
  in fromString $ printf "[%s]" instdds

tDataDef :: DataDef -> Context
tDataDef (DD tid tvs cons _) = indent (ppTypeInfo tid <+> tScheme tvs) $ tDataCons cons

tDataCons :: Either (NonEmpty DataRec) [DataCon] -> Context
tDataCons (Left recs) = ppLines (\dc@(DR _ _ _ ann) -> annotate ann (tRecDef dc)) recs
tDataCons (Right cons) = ppLines (\dc@(DC _ _ _ ann) -> annotate ann (tConDef dc)) cons

tConDef :: DataCon -> Context
tConDef (DC _ g t _) = foldl' (<+>) (ppCon g) $ tTypes t

tRecDef :: DataRec -> Context
tRecDef (DR _ uv t _) = ppMem uv <+> tType t

tFunction :: Function -> Context
tFunction fn = tBody (tFunDec fn.functionDeclaration) fn.functionBody

tInst :: InstDef -> Context
tInst inst =
  let
    header = "inst" <+> ppUniqueClass inst.instClass.classID <+> ppTypeInfo ((\(DD ut _ _ _) -> ut) (fst inst.instType)) <+> sepBy " " (tTVar <$> snd inst.instType)

    tInstFunction :: InstanceFunction -> Context
    tInstFunction fn = tBody (tFunDec fn.instFunction.functionDeclaration <+> "(" <> ppVar Local fn.instFunctionClassUniqueVar <> ")") fn.instFunction.functionBody
  in ppBody tInstFunction header inst.instFunctions

tFunDec :: FunDec -> Context
tFunDec (FD fenv v params retType scheme _ _) = comment (tEnv fenv) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> tDecon pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType <+> tScheme scheme

tScheme :: Scheme -> Context
tScheme (Scheme tvars unions) = ppSet tTVar tvars <+> ppSet (tEnvUnion . fmap tType) unions

tTypes :: Functor t => t Type -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) _ -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type -> Context
tType = cata $ \case
  TCon (DD ut _ _ _) params unions ->
    let conunion = case unions of
          [] -> []
          tunions -> "|" : (tEnvUnion <$> tunions)
    in foldl' (<+>) (ppTypeInfo ut) (params ++ conunion)
  TVar tv -> tTVar tv
  TFun fenv args ret -> tEnvUnion fenv <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret
  TyVar ty -> tTyVar ty

tTyVar :: TyVar -> Context
tTyVar (TyV t _) = "#" <> pretty t

tUnions :: [EnvUnion] -> Context
tUnions [] = mempty
tUnions unions = "|" <+> sepBy " " (tEnvUnion . fmap tType <$> unions)

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion { unionID = uid, union = us } = ppUnionID uid <> encloseSepBy "{" "}" ", " (fmap tEnv' us)

tEnv :: Env -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF Context -> Context
tEnv' = \case
  Env eid vs _ lev -> ppEnvID eid <> fromString (printf "(%s)" (show lev)) <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc (asUniqueVar v) <+> t) vs)
  RecursiveEnv eid isEmpty -> fromString $ printf "%s[REC%s]" (ppEnvID eid) (if isEmpty then "(empty)" else "(some)" :: Context)

tBody :: Foldable f => Context -> f AnnStmt -> Context
tBody = ppBody tAnnStmt

tTVar :: TVar -> Context
tTVar (TV tv b cs) =
  let bindingCtx = case b of
        BindByType ut -> ppTypeInfo ut
        BindByVar uv -> ppVar Local uv
        BindByInst uc -> ppUniqueClass uc
  in pretty tv <> "<" <> bindingCtx <> ">" <> Common.ppSet tClassName (Set.toList cs)

tClassName :: ClassDef -> Context
tClassName cd = pretty $ show cd.classID
