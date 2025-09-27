{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
module AST.Typed (module AST.Typed) where

import AST.Common (Type, Function, DataDef (..), InstDef, ClassDef (..), ClassFunDec (..), XFunVar, XEnvUnion, XEnv, XVar, TVar, InstFun, Exports, AnnStmt, Module, XExprNode, XLVar, XTCon, Expr, XReturn, XFunDef, XInstDef, XOther, XTFun, XLamOther, XDClass, Rec, DataCon (..), XDCon, XTConOther, XTOther, TypeF (..), XDTCon, XClass, XFunOther, XVarOther, XConOther, XCon, XMem, XDataScheme, XFunType, XTVar, functionDeclaration, functionId, instType, XClassConstraints, XClassFunDec, XLamVar, functionOther, MutAccess, XMutAccess, XInstExport, XStringInterpolation, XExportType, XClassFunOther)
import qualified AST.Def as Def
import Data.Map.Strict (Map)
import Data.Text (Text)
import Data.Fix (Fix (..))
import AST.Def (PP (..), (<+>), pf, PPDef (ppDef), TypeID, UnionUniID, ClassInstID)
import Data.Functor.Classes (Ord1 (..), Eq1 (..))
import Data.Functor ((<&>))
import Data.String (fromString)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique (Unique)



data ExprNode = ExprNode
  { t :: Type TC
  , loc :: Def.Location
  }



data TypedWithIndexes
type TC = TypedWithIndexes

-- index to a "subst map"


type instance Type TC = TypeID
type instance XFunVar TC = Def.UniqueVar
type instance XEnv TC = EnvDef
type instance XEnvUnion TC = EnvUnion
type instance XVar TC = Variable
type instance XVarOther TC = Def.Locality
type instance XExprNode TC = ExprNode


type instance XLVar TC = Def.UniqueVar  -- This is not that good..... probably TEMP
type instance XLamVar TC = (Def.UniqueVar, Type TC)
type instance XTCon TC = DataDef TC
type instance XReturn TC = Expr TC
type instance XFunDef TC = Function TC
type instance XInstDef TC = InstDef TC
type instance XOther TC = ()
type instance XTFun TC = UnionUniID
type instance XDClass TC = Def.UniqueClass
type instance XDCon TC = Def.UniqueCon
type instance XDTCon TC = Def.UniqueType
type instance Rec TC a = a
type instance XTConOther TC = [EnvUnion]  -- IT SEEMS LIKE WE SHOULD JUST MAKE FUNCTIONS IMPLICIT PARAMETERS!
type instance XTOther TC = TOTF TC
type instance XClass TC = ClassDef TC
type instance XClassFunDec TC = ClassFunDec TC
type instance XFunOther TC = FunOther TC
type instance XCon TC = DataCon TC
type instance XConOther TC = (Def.EnvID, Match)
type instance XMem TC = Def.MemName
type instance XDataScheme TC = Scheme TC
type instance XFunType TC = Type TC
type instance XTVar TC = TVar TC
type instance XClassConstraints TC = ()
type instance XClassFunOther TC = Scheme TC
type instance XMutAccess TC = (MutAccess TC, Type TC)
type instance XInstExport TC = InstDef TC
type instance XStringInterpolation TC = Text  -- here, we're eliminating the string interpolation completely!
type instance XExportType TC = Type TC


data LamDec phase = LamDec Def.UniqueVar (EnvDefF (Type phase))
type instance XLamOther TC = LamDec TC

data TOTF phase
  = TVar (TVar phase)
  | TyVar TyVar
  deriving (Eq, Ord)

data TyVar = TyV { actualUnique :: Unique, fromTyV :: Text, tyvConstraints :: [(ClassDef TC, PossibleInstances TC)] }

type PossibleInstances phase = Map (DataDef phase) (InstDef phase)
type ScopeSnapshot phase = Map (ClassDef phase) (PossibleInstances phase)


data VariableF t
  = DefinedVariable Def.UniqueVar
  -- scope snapshots might not be needed!
  -- Here, we need to store the instances. They must also be up for substitution. How would I represent it?
  -- TODO: Right now, we are substituting UCIs at the end of a function. What we can do right now, is we can also substitute this map. I can do this better probably - maybe we can associate function instantiations with a specific TVar?
  | DefinedFunction (Function TC) (MatchF t)
  | DefinedClassFunction (ClassFunDec TC) Def.ClassInstID  -- which class function and which instances are visible at this point. 
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type Variable = VariableF (Type TC)
type IsFromExternalModule = Bool  -- FOR OPTIMIZATION, SO WE WON'T POINTLESSLY TRY TO SUBSTITUTE FOREIGN FUNCTIONS!

data VariableProto
  = PDefinedVariable Def.UniqueVar
  | PDefinedFunction (Function TC)
  | PDefinedClassFunction (ClassFunDec TC)
  deriving (Eq, Ord)

-- type safety. used for env definitions, like in a function.
data EnvDefF t = EnvDef
  { envDefID :: Def.EnvID
  , envVars :: [(VariableF t, Def.Locality, t)]
  , envStack :: Def.EnvStack -- t is here, because of recursion schemes. UniqueVar, because we don't know which environments will be used in the end. We will replace it with a `Variable` equivalent AFTER we monomorphise.
  } deriving (Functor, Foldable, Traversable)
type EnvDef = EnvDefF (Type TC)

data EnvF t
  = Env (EnvDefF t)
  -- The last map is a HACK
  | RecursiveEnv Def.EnvID IsEmpty  -- Recursive functions won't have access to their environment while typechecking... kinda stupid. ehh... but we're solving an actual issue here. `IsEmpty` is used in Mono to let us know if this function's environment was empty or not.
  deriving (Functor, Foldable, Traversable)
type Env = EnvF (Type TC)

data UnionMemberF t
  = UnionFun (Function TC) (MatchF t)
  | UnionLam (EnvDefF t)
  | UnionConEnv Def.EnvID  -- nothing, empty environment. it's for documentation - I can just create an "EnvDef".
  deriving (Eq, Ord, Functor, Foldable, Traversable)

type UnionMember = UnionMemberF (Type TC)

data EnvUnionF t = EnvUnion
  { unionID :: Def.UnionID
  , union :: ~[UnionMemberF t]  -- (ufi, assocs, env) -- List can be empty for types written by the programmer (which also don't have any other function's environment yet). This is okay, because functions are not yet monomorphised.
  } deriving (Functor, Foldable, Traversable)
-- deriving instance (Eq ty, Eq (XFunVar phase)) => Eq (EnvUnionF phase ty)
-- deriving instance (Ord ty, Ord (XFunVar phase)) => Ord (EnvUnionF phase ty)

type EnvUnion = UnionUniID  -- changed to a REF.
type IsEmpty = Bool


data FunOther phase = FunOther
  { functionScheme :: Scheme phase
  -- , functionClassInstantiationAssocs :: ClassInstantiationAssocs  -- TODO: might not be necessary we can just map them.
  , functionAnnotations :: [Def.Ann]
  , functionLocation :: Def.Location
  }


-- `Scheme` must have the same shape as `Match`
data Scheme phase = Scheme [TVar phase] [XEnvUnion phase] [FunctionTypeAssociation phase]


-- `Match` is like an instantiated `Scheme`.
data MatchF t = Match [t] [EnvUnion] [ClassInstID]
  deriving (Functor, Foldable, Traversable)
type Match = MatchF (Type TC)

deriving instance (Eq ty) => Eq (MatchF ty)
deriving instance (Ord ty) => Ord (MatchF ty)

emptyScheme :: Scheme phase
emptyScheme = Scheme [] [] []



data FunctionTypeAssociation phase = FunctionTypeAssociation (TVar phase) (Type phase) (ClassFunDec phase) Def.ClassInstID

data TypeAssociation = TypeAssociation (Def.Location, Type TC) (Def.Location, Type TC) (ClassFunDec TC) Def.ClassInstID [Def.EnvID]  -- TODO: I think only one location is required. We can't really get location of self?


data Mod phase = Mod
  { topLevelStatements :: [AnnStmt phase]
  , exports :: Exports phase
  }
type instance Module TC = Mod TC



-------

-- toTCClassDef :: ClassDef T -> ClassDef TC
-- toTCClassDef ClassDef { classID, classFunctions } = cd where
--   cd = ClassDef { classID = classID, classFunctions = toTCClassFun <$> classFunctions }

--   toTCClassFun :: ClassFunDec T -> ClassFunDec TC
--   toTCClassFun (CFD _ v params ret) = CFD cd v (bimap toTCDecon toTCClassType <$> params) (toTCClassType ret)

--   toTCClassType :: ClassType T -> ClassType TC
--   toTCClassType = undefined

--   toTCDecon :: Decon T -> Decon TC
--   toTCDecon = undefined

-- toTCDataCon :: DataCon T -> DataCon TC
-- toTCDataCon = undefined

-- toTCDataDef :: DataDef T -> DataDef TC
-- toTCDataDef = undefined

-- toTCInstDef :: InstDef T -> InstDef TC
-- toTCInstDef = undefined

-- toTCType :: Type T -> Type TC
-- toTCType = undefined


envID :: EnvF ty -> Def.EnvID
envID = \case
  Env (EnvDef eid _ _) -> eid
  RecursiveEnv eid _ -> eid


asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  DefinedFunction fn _ -> PDefinedFunction fn
  DefinedClassFunction cd _ -> PDefinedClassFunction cd

---------


isUnionEmpty :: EnvUnionF ty -> Bool
isUnionEmpty (EnvUnion _ []) = True
isUnionEmpty _ = False



dbgSnapshot :: (PP (XDClass phase), PP (XDTCon phase)) => ScopeSnapshot phase -> Def.Context
dbgSnapshot = Def.ppLines . fmap (\(cd, insts) -> pf "% => %" (Def.ppDef cd) (Def.encloseSepBy "[" "]" ", " $ fmap (\dd -> pp dd.ddName) $ Set.toList $ Map.keysSet insts) :: Def.Context) . Map.toList



---------

instance Eq (EnvUnionF ty) where
  u == u' = u.unionID == u'.unionID

instance Ord (EnvUnionF ty) where
  u `compare` u' = u.unionID `compare` u'.unionID

instance Eq ty => Eq (EnvDefF ty) where
  EnvDef lid lts _ == EnvDef rid rts _ = lid == rid && (lts <&> \(_, _, x) -> x) == (rts <&> \(_, _, x) -> x)

instance Ord ty => Ord (EnvDefF ty) where
  EnvDef lid lts _ `compare` EnvDef rid rts _ = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)

instance Eq ty => Eq (EnvF ty) where
  Env ed == Env ed' = ed == ed'
  l == r  = envID l == envID r

instance Ord ty => Ord (EnvF ty) where
  Env (EnvDef lid lts _) `compare` Env (EnvDef rid rts _) = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)
  l `compare` r = envID l `compare` envID r

instance Eq1 (EnvF) where
  liftEq f (Env (EnvDef lid lts _)) (Env (EnvDef rid rts _)) = lid == rid && and (zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts)
  liftEq _ l r = envID l == envID r

instance Ord1 (EnvF) where
  liftCompare f (Env (EnvDef lid lts _)) (Env (EnvDef rid rts _)) = case lid `compare` rid of
    EQ -> mconcat $ zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts
    ord -> ord
  liftCompare _ l r = envID l `compare` envID r


instance Eq TyVar where
  tyv == tyv' = tyv.actualUnique == tyv'.actualUnique

instance Ord TyVar where
  tyv `compare` tyv' = tyv.fromTyV `compare` tyv'.fromTyV


-- NOTE it seems like the default comparison function is okay. Maybe modify it later if it's slow AND depending on usage?
-- instance (Eq ty, Eq (XFunVar phase)) => Eq (VariableF phase ty) where
--   l == r = case (l, r) of
--     (DefinedVariable uv, DefinedVariable uv') -> uv == uv'
--     (DefinedFunction fn match, DefinedFunction fn' match') -> (fn, match) == (fn', match')
--     (DefinedClassFunction cfd match inst, DefinedClassFunction cfd' match' inst') -> (cfd, match, inst) == (cfd', match', inst')
--     _ -> False

-- instance (Ord ty, Ord (XFunVar phase)) => Ord (VariableF phase ty) where
--   l `compare` r = case (l, r) of
--     (DefinedVariable uv, DefinedVariable uv') -> uv `compare` uv'
--     (DefinedFunction fn match, DefinedFunction fn' match') -> (fn, match) `compare` (fn', match')
--     (DefinedClassFunction cfd match inst, DefinedClassFunction cfd' match' inst') -> (cfd, match, inst) `compare` (cfd', match', inst')

--     (DefinedVariable {}, _) -> LT

--     (DefinedFunction {}, DefinedVariable {}) -> GT
--     (DefinedFunction {}, _) -> LT

--     (DefinedClassFunction {}, _) -> GT


--------

instance (PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (XTOther phase), PP (XTFun phase), PP (XExprNode phase), Def.PPDef (XTCon phase), PP (XLamVar phase), PP (XMutAccess phase), PP (XStringInterpolation phase), PP (XTConOther phase), PP (Type phase)) => PP (Mod phase) where
  pp m = Def.ppLines m.topLevelStatements

instance (PPDef (XClass phase), PP (VariableF (Type phase)), PP (Type phase), PP (XEnvUnion phase) ) => PP (FunOther phase) where
  pp fo = pf "%" fo.functionScheme

instance (PP ty, PP (VariableF ty)) => PP (EnvUnionF ty) where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> us)

instance (PP a, PP (VariableF a)) => PP (EnvF a) where
  pp = \case
    Env (EnvDef eid vs lev) -> pp eid <> fromString (Def.pf "(%)" (show lev)) <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp loc <> pp v <+> pp t) vs)
    RecursiveEnv eid isEmpty -> Def.pf "%[REC%]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

instance PPDef (XClass phase) => PP (TOTF phase) where
  pp = \case
    TVar tv -> pp tv
    TyVar tyv -> pp tyv

instance PP TyVar where
  pp (TyV _ t constraints) =
    let
      tvarClasses = if null constraints
        then ""
        else Def.ppDef $ constraints <&> \(cd, insts) -> pf "(%, %)" (Def.ppDef cd) ((fmap Def.ppDef . Set.toList . Map.keysSet) insts) :: Def.Context
    in "#" <> pp t <> tvarClasses

instance PP ExprNode where
  pp en = pp en.t <+> pp en.loc

instance (PP (Type phase), PPDef (XClass phase)) => PP (FunctionTypeAssociation phase) where
  pp (FunctionTypeAssociation tv t _ _) = Def.pf "(% => %)" (pp tv) (pp t)

instance PP TypeAssociation where
  pp (TypeAssociation from to _ _ _) = Def.pf "(% => %)" (pp (snd from)) (pp (snd to))

instance PP a => PP (VariableF a) where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f match -> pp f.functionDeclaration.functionId <> "&F" <> "(" <> pp match <> ")"
    DefinedClassFunction (CFD cd uv _ _ _) inst ->
      Def.pf "%&<%>[%]" (pp uv) (pp inst)  -- (Def.sepBy ", " $ fmap (\inst -> (pp . ddName . fst . instType) inst) (Map.elems (Def.defaultEmpty cd insts))) undefined

instance PP ty => PP (MatchF ty) where
  pp (Match ts us as) = pf "Match % % %" (pp ts) (pp us) (pp as)

instance (PP (Type phase), PP (VariableF (Type phase))) => PP (LamDec phase) where
  pp (LamDec uv env) = pp env <> pp uv

instance PP ty => PP (EnvDefF ty) where
  pp (EnvDef eid vs lev) = pp eid <> fromString (Def.pf "(%)" (show lev)) <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp loc <> pp v <+> pp t) vs)

instance PP ty => PP (UnionMemberF ty) where
  pp = \case
    UnionFun fn match -> pf "%: %" (ppDef fn) match
    UnionLam lamenv -> pp lamenv
    UnionConEnv conEnvID -> pp conEnvID  -- nothing, empty environment. it's for documentation - I can just create an "EnvDef".

instance (PP (Type phase), PPDef (XClass phase), PP (VariableF (Type phase)), PP (XEnvUnion phase) ) => PP (Scheme phase) where
  pp (Scheme tvars unions assocs) = Def.ppSet pp tvars <+> Def.ppSet pp unions <+> Def.ppSet pp assocs


-- instance {-# OVERLAPPING #-} PP ClassInstantiationAssocs where
--   pp classInstantiationAssocs = fromString $ Def.printf "CIA: %" (Def.ppMap $ fmap (bimap pp (Def.ppTup . bimap pp (Def.ppTup . bimap (Def.encloseSepBy "[" "]" ", " . fmap pp) (\ifn -> pp ifn.instFunDec.functionId)))) $ fmap (\(ufiuci, (l, r, _, _)) -> (ufiuci, (l, r))) $ Map.toList classInstantiationAssocs)
