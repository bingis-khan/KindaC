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
module AST.Typed (module AST.Typed) where

import AST.Common (Type, Function, DataDef (..), InstDef, ClassDef (..), ClassFunDec (..), XFunVar, XEnvUnion, XEnv, XVar, TVar, InstFun, Exports, AnnStmt, Module, DeconF, WithType, ExprF, XNode, XLVar, XTCon, Expr, XReturn, XFunDef, XInstDef, XOther, XTFun, XLamOther, XDClass, ClassType, Rec, Decon, DataCon (..), XDCon, XTConOther, XTOther, TypeF (..), XDTCon, XClass, XFunOther, XVarOther, XConOther, XCon, XMem, XDataScheme, XFunType, XTVar, functionDeclaration, functionId, instType, ClassConstraints, XClassFunDec, XLamVar, instFunDec, functionOther, instFuns, instClassFunDec, functionEnv)
import qualified AST.Def as Def
import Data.Map (Map)
import Data.Text (Text)
import Data.Fix (Fix (..))
import AST.Def ((:.), Annotated, PP (..), (<+>), PPDef)
import Data.Biapplicative (bimap)
import Data.Functor.Classes (Ord1 (..), Eq1 (..))
import Data.Functor ((<&>))
import Data.String (fromString)
import qualified Data.Map as Map
import Data.List.NonEmpty (NonEmpty)
import Data.Foldable (find)
import Data.Maybe (fromJust)
import qualified Data.Set as Set


-- data Typed
-- type T = Typed

-- type instance XFunVar T = Def.UniqueVar
-- type instance XFunVar T = Def.UniqueVar
-- type instance XEnv T = Env
-- type instance XEnvUnion T = EnvUnion
-- type instance XVar T = Variable
-- type instance XVarOther T = Def.Locality
-- type instance XNode T = Type T
-- type instance XLVar T = (Def.UniqueVar, Type T)  -- This is not that good..... probably TEMP
-- type instance XTCon T = DataDef T
-- type instance XReturn T = Expr T
-- type instance XFunDef T = Function T
-- type instance XInstDef T = InstDef T
-- type instance XOther T = ()
-- type instance XTFun T = EnvUnion
-- type instance XDClass T = Def.UniqueClass
-- type instance XDCon T = Def.UniqueCon
-- type instance XDTCon T = Def.UniqueType
-- type instance Rec T a = a
-- type instance XTConOther T = [EnvUnion]
-- type instance XTOther T = TOTF
-- type instance XClass T = ClassDef T
-- type instance XFunOther T = FunOther
-- type instance XCon T = DataCon T
-- type instance XConOther T = Def.EnvID
-- type instance XMem T = Def.MemName
-- type instance XDataScheme T = Scheme
-- type instance XFunType T = Type T
-- type instance XTVar T = TVar T
-- type instance Module T = Mod T


data TypedWithClasses
type TC = TypedWithClasses

type instance XFunVar TC = Def.UniqueVar
type instance XEnv TC = Env
type instance XEnvUnion TC = EnvUnion
type instance XVar TC = Variable
type instance XVarOther TC = Def.Locality
type instance XNode TC = Type TC
type instance XLVar TC = Def.UniqueVar  -- This is not that good..... probably TEMP
type instance XLamVar TC = (Def.UniqueVar, Type TC)
type instance XTCon TC = DataDef TC
type instance XReturn TC = Expr TC
type instance XFunDef TC = Function TC
type instance XInstDef TC = InstDef TC
type instance XOther TC = ()
type instance XTFun TC = EnvUnion
type instance XDClass TC = Def.UniqueClass
type instance XDCon TC = Def.UniqueCon
type instance XDTCon TC = Def.UniqueType
type instance Rec TC a = a
type instance XTConOther TC = [EnvUnion]
type instance XTOther TC = TOTF
type instance XClass TC = ClassDef TC
type instance XClassFunDec TC = ClassFunDec TC
type instance XFunOther TC = FunOther
type instance XCon TC = DataCon TC
type instance XConOther TC = Def.EnvID
type instance XMem TC = Def.MemName
type instance XDataScheme TC = Scheme
type instance XFunType TC = Type TC
type instance XTVar TC = TVar TC
type instance ClassConstraints TC = ()

data LamDec = LamDec Def.UniqueVar Env
type instance XLamOther TC = LamDec

data TOTF
  = TVar (TVar TC)
  | TyVar TyVar
  deriving (Eq, Ord)

data TyVar = TyV { fromTyV :: Text, tyvConstraints :: [(ClassDef TC, PossibleInstances)] }

type PossibleInstances = Map (DataDef TC) (InstDef TC)
type ScopeSnapshot = Map (ClassDef TC) PossibleInstances

data VariableF t
  = DefinedVariable Def.UniqueVar
  -- scope snapshots might not be needed!
  -- Here, we need to store the instances. They must also be up for substitution. How would I represent it?
  -- TODO: Right now, we are substituting UCIs at the end of a function. What we can do right now, is we can also substitute this map. I can do this better probably - maybe we can associate function instantiations with a specific TVar?
  | DefinedFunction (Function TC) [t] ScopeSnapshot Def.UniqueFunctionInstantiation
  | DefinedClassFunction (ClassFunDec TC) ScopeSnapshot t Def.UniqueClassInstantiation  -- which class function and which instances are visible at this point. 
  -- deriving (Eq, Ord)
  deriving (Functor, Foldable, Traversable)
type Variable = VariableF (Type TC)

data VariableProto
  = PDefinedVariable Def.UniqueVar
  | PDefinedFunction (Function TC)
  | PDefinedClassFunction (ClassFunDec TC)
  deriving (Eq, Ord)

data EnvF t
  = Env Def.EnvID [(VariableF t, Def.Locality, t)] (Map VariableProto Def.Locality) Def.EnvStack -- t is here, because of recursion schemes. UniqueVar, because we don't know which environments will be used in the end. We will replace it with a `Variable` equivalent AFTER we monomorphise.
  -- The last map is a HACK
  | RecursiveEnv Def.EnvID IsEmpty  -- Recursive functions won't have access to their environment while typechecking... kinda stupid. ehh... but we're solving an actual issue here. `IsEmpty` is used in Mono to let us know if this function's environment was empty or not.
  deriving (Functor, Foldable, Traversable)
type Env = EnvF (Type TC)

data EnvUnionF t = EnvUnion
  { unionID :: Def.UnionID
  , union :: [(Maybe Def.UniqueClassInstantiation, Def.UniqueFunctionInstantiation, [t], EnvF t)]  -- (ufi, assocs, env) -- List can be empty for types written by the programmer (which also don't have any other function's environment yet). This is okay, because functions are not yet monomorphised.
  } deriving (Eq, Ord, Functor, Foldable, Traversable)

type EnvUnion = EnvUnionF (Type TC)
type IsEmpty = Bool


data FunOther = FunOther
  { functionScheme :: Scheme
  , functionAssociations :: [FunctionTypeAssociation]
  -- , functionClassInstantiationAssocs :: ClassInstantiationAssocs  -- TODO: might not be necessary we can just map them.
  }

data Scheme = Scheme [TVar TC] [EnvUnion]

data FunctionTypeAssociation = FunctionTypeAssociation (TVar TC) (Type TC) (ClassFunDec TC) Def.UniqueClassInstantiation

-- I'm not sure about level. We don't need type applications now.
-- It's needed to check if we need to keep it in the environment or not.
type ClassInstantiationAssocs = Map (Maybe (Def.UniqueFunctionInstantiation, Type TC), Def.UniqueClassInstantiation) (Type TC, ([Type TC], InstFun TC), Def.EnvStack, Def.UniqueFunctionInstantiation)
data TypeAssociation = TypeAssociation (Type TC) (Type TC) (ClassFunDec TC) Def.UniqueClassInstantiation (Maybe Def.UniqueFunctionInstantiation) [Def.EnvID]


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


envID :: EnvF t -> Def.EnvID
envID = \case
  Env eid _ _ _ -> eid
  RecursiveEnv eid _ -> eid


asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  DefinedFunction fn _ _ _ -> PDefinedFunction fn
  DefinedClassFunction cd _ _ _ -> PDefinedClassFunction cd

---------


-- This is currently how we extract unions from types.
-- This needs to be done, because custom types need to track which unions were used.
-- TODO: this should probably be made better. Maybe store those unions in DataDef?
extractUnionsFromDataType :: DataDef TC -> [EnvUnion]
extractUnionsFromDataType (DD _ _ (Right dcs) _) =
  concatMap extractUnionsFromConstructor dcs

extractUnionsFromDataType dd@(DD ut _ (Left drs) _) =
  flip concatMap drs $ \(Def.Annotated _ (_, t)) -> mapUnion ut t

extractUnionsFromConstructor :: DataCon TC -> [EnvUnion]
extractUnionsFromConstructor (DC (DD ut _ _ _) _ ts _) = concatMap (mapUnion ut) ts

-- TODO: clean up all the mapUnion shit. think about proper structure.
mapUnion :: Def.UniqueType -> Type TC -> [EnvUnion]
mapUnion ut (Fix t) = case t of
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  TCon (DD tut _ _ _) paramts conUnions
    -- breaks cycle with self referential datatypes.
    | tut == ut -> concatMap (mapUnion ut) paramts
    | otherwise -> conUnions <> concatMap (mapUnion ut) paramts

  TFun u args ret -> [u] <> concatMap (mapUnion ut) args <> mapUnion ut ret
  TO _ -> []

isUnionEmpty :: EnvUnionF t -> Bool
isUnionEmpty (EnvUnion _ []) = True
isUnionEmpty _ = False



dbgSnapshot :: ScopeSnapshot -> Def.Context
dbgSnapshot = Def.ppLines (\(cd, insts) -> fromString $ Def.printf "%s => %s" (Def.ppDef cd) (Def.encloseSepBy "[" "]" ", " $ fmap (\dd -> pp dd.ddName) $ Set.toList $ Map.keysSet insts)) . Map.toList

-----------


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


instance Eq TyVar where
  tyv == tyv' = tyv.fromTyV == tyv'.fromTyV

instance Ord TyVar where
  tyv `compare` tyv' = tyv.fromTyV `compare` tyv'.fromTyV


instance Eq Variable where
  l == r = case (l, r) of
    (DefinedVariable uv, DefinedVariable uv') -> uv == uv'
    (DefinedFunction fn ts _ ufi, DefinedFunction fn' ts' _ ufi') -> (fn, ts, ufi) == (fn', ts', ufi')
    (DefinedClassFunction cfd _ t uci, DefinedClassFunction cfd' _ t' uci') -> (cfd, t, uci) == (cfd', t', uci')
    _ -> False

instance Ord Variable where
  l `compare` r = case (l, r) of
    (DefinedVariable uv, DefinedVariable uv') -> uv `compare` uv'
    (DefinedFunction fn ts _ ufi, DefinedFunction fn' ts' _ ufi') -> (fn, ts, ufi') `compare` (fn', ts', ufi')
    (DefinedClassFunction cfd _ t uci, DefinedClassFunction cfd' _ t' uci') -> (cfd, t, uci) `compare` (cfd', t', uci')

    (DefinedVariable {}, _) -> LT

    (DefinedFunction {}, DefinedVariable {}) -> GT
    (DefinedFunction {}, _) -> LT

    (DefinedClassFunction {}, _) -> GT


--------

instance (PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (XTOther phase), PP (XTFun phase), PP (XNode phase), Def.PPDef (XTCon phase), PP (XLamVar phase)) => PP (Mod phase) where
  pp m = Def.ppLines pp m.topLevelStatements

instance PP EnvUnion where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> us)

instance PP a => PP (EnvF a) where
  pp = \case
    Env eid vs _ lev -> pp eid <> fromString (Def.printf "(%s)" (show lev)) <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp loc <> pp v <+> pp t) vs)
    RecursiveEnv eid isEmpty -> fromString $ Def.printf "%s[REC%s]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

instance PP TOTF where
  pp = \case
    TVar tv -> pp tv
    TyVar tyv -> pp tyv

instance PP TyVar where
  pp (TyV t _) = "#" <> pp t

instance PP a => PP (VariableF a) where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f assocs _ ufi -> pp f.functionDeclaration.functionId <> "&F" <> pp ufi <> "(" <> Def.ppSet (\(FunctionTypeAssociation tv _ _ uci) -> pp (tv, uci)) f.functionDeclaration.functionOther.functionAssociations <> "/" <> Def.ppSet pp assocs <> ")"
    DefinedClassFunction (CFD cd uv _ _) insts self uci ->
      fromString $ Def.printf "%s&%s&C<%s>[%s]" (pp uv) (pp uci) (pp self) (Def.sepBy ", " $ fmap (\inst -> (pp . ddName . fst . instType) inst) (Map.elems (Def.defaultEmpty cd insts)))

instance PP LamDec where
  pp (LamDec uv env) = pp env <> pp uv

instance PP Scheme where
  pp (Scheme tvars unions) = Def.ppSet pp tvars <+> Def.ppSet pp unions

instance {-# OVERLAPPING #-} PP ClassInstantiationAssocs where
  pp classInstantiationAssocs = fromString $ Def.printf "CIA: %s" (Def.ppMap $ fmap (bimap pp (Def.ppTup . bimap pp (Def.ppTup . bimap (Def.encloseSepBy "[" "]" ", " . fmap pp) (\ifn -> pp ifn.instFunDec.functionId)))) $ fmap (\(ufiuci, (l, r, _, _)) -> (ufiuci, (l, r))) $ Map.toList classInstantiationAssocs)
