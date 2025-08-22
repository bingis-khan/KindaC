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

import AST.Common (Type, Function, DataDef (..), InstDef, ClassDef (..), ClassFunDec (..), XFunVar, XEnvUnion, XEnv, XVar, TVar, InstFun, Exports, AnnStmt, Module, XExprNode, XLVar, XTCon, Expr, XReturn, XFunDef, XInstDef, XOther, XTFun, XLamOther, XDClass, Rec, DataCon (..), XDCon, XTConOther, XTOther, TypeF (..), XDTCon, XClass, XFunOther, XVarOther, XConOther, XCon, XMem, XDataScheme, XFunType, XTVar, functionDeclaration, functionId, instType, XClassConstraints, XClassFunDec, XLamVar, instFunDec, functionOther, MutAccess, XMutAccess, XInstExport, XStringInterpolation, XExportType, asksNode)
import qualified AST.Def as Def
import Data.Map.Strict (Map, (!?))
import Data.Text (Text)
import Data.Fix (Fix (..))
import AST.Def (PP (..), (<+>), pf, PPDef)
import Data.Biapplicative (bimap, first)
import Data.Functor.Classes (Ord1 (..), Eq1 (..))
import Data.Functor ((<&>))
import Data.String (fromString)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique (Unique)
import Control.Monad.Trans.Class (lift)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap


data Typed
type T = Typed

type instance Type T = Fix (TypeF T)
type instance XFunVar T = Def.UniqueVar
type instance XEnv T = EnvF T (Type T)
type instance XEnvUnion T = EnvUnionF T (Type T)
type instance XVar T = VariableF T (Type T)
type instance XVarOther T = Def.Locality
type instance XExprNode T = ExprNode T

data ExprNode phase = ExprNode
  { t :: Type phase
  , loc :: Def.Location
  }



type instance XLVar T = Def.UniqueVar  -- This is not that good..... probably TEMP
type instance XLamVar T = (Def.UniqueVar, Type T)
type instance XTCon T = DataDef T
type instance XReturn T = Expr T
type instance XFunDef T = Function T
type instance XInstDef T = InstDef T
type instance XOther T = ()
type instance XTFun T = EnvUnionF T (Type T)
type instance XDClass T = Def.UniqueClass
type instance XDCon T = Def.UniqueCon
type instance XDTCon T = Def.UniqueType
type instance Rec T a = a
type instance XTConOther T = [(EnvUnionF T (Type T), [Type T], Type T)]  -- IT SEEMS LIKE WE SHOULD JUST MAKE FUNCTIONS IMPLICIT PARAMETERS!
type instance XTOther T = TOTF T
type instance XClass T = ClassDef T
type instance XClassFunDec T = ClassFunDec T
type instance XFunOther T = FunOther T
type instance XCon T = DataCon T
type instance XConOther T = Def.EnvID
type instance XMem T = Def.MemName
type instance XDataScheme T = Scheme T
type instance XFunType T = Type T
type instance XTVar T = TVar T
type instance XClassConstraints T = ()
type instance XMutAccess T = (MutAccess T, Type T)
type instance XInstExport T = InstDef T
type instance XStringInterpolation T = Text  -- here, we're eliminating the string interpolation completely!
type instance XExportType T = Type T

type instance XLamOther T = LamDec T
type instance Module T = [AnnStmt T]


data TypedWithIndexes
type TC = TypedWithIndexes

-- index to a "subst map"
newtype TypeID = TypeID { fromTypeID :: Int } deriving (Eq, Ord)
instance PP TypeID where
  pp = pp . fromTypeID

newtype UnionUniID = UnionUniID { fromUnionUniID :: Int } deriving (Eq, Ord)
instance PP UnionUniID where
  pp = pp . fromUnionUniID

instance PPDef UnionUniID where
  ppDef = pp . fromUnionUniID


type instance Type TC = TypeID
type instance XFunVar TC = Def.UniqueVar
type instance XEnv TC = Env
type instance XEnvUnion TC = EnvUnion
type instance XVar TC = Variable
type instance XVarOther TC = Def.Locality
type instance XExprNode TC = ExprNode TC


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
type instance XTConOther TC = [(EnvUnion, [Type TC], Type TC)]  -- IT SEEMS LIKE WE SHOULD JUST MAKE FUNCTIONS IMPLICIT PARAMETERS!
type instance XTOther TC = TOTF TC
type instance XClass TC = ClassDef TC
type instance XClassFunDec TC = ClassFunDec TC
type instance XFunOther TC = FunOther TC
type instance XCon TC = DataCon TC
type instance XConOther TC = Def.EnvID
type instance XMem TC = Def.MemName
type instance XDataScheme TC = Scheme TC
type instance XFunType TC = Type TC
type instance XTVar TC = TVar TC
type instance XClassConstraints TC = ()
type instance XMutAccess TC = (MutAccess TC, Type TC)
type instance XInstExport TC = InstDef TC
type instance XStringInterpolation TC = Text  -- here, we're eliminating the string interpolation completely!
type instance XExportType TC = Type TC

data LamDec phase = LamDec Def.UniqueVar (EnvF phase (Type phase))
type instance XLamOther TC = LamDec TC

data TOTF phase
  = TVar (TVar phase)
  | TyVar TyVar
  deriving (Eq, Ord)

data TyVar = TyV { actualUnique :: Unique, fromTyV :: Text, tyvConstraints :: [(ClassDef TC, PossibleInstances TC)] }

type PossibleInstances phase = Map (DataDef phase) (InstDef phase)
type ScopeSnapshot phase = Map (ClassDef phase) (PossibleInstances phase)

data VariableF phase t
  = DefinedVariable Def.UniqueVar
  -- scope snapshots might not be needed!
  -- Here, we need to store the instances. They must also be up for substitution. How would I represent it?
  -- TODO: Right now, we are substituting UCIs at the end of a function. What we can do right now, is we can also substitute this map. I can do this better probably - maybe we can associate function instantiations with a specific TVar?
  | DefinedFunction (Function phase) [t] (ScopeSnapshot phase) Def.UniqueFunctionInstantiation
  | DefinedClassFunction (ClassFunDec phase) (ScopeSnapshot phase) t Def.UniqueClassInstantiation  -- which class function and which instances are visible at this point. 
  -- deriving (Eq, Ord)
  deriving (Functor, Foldable, Traversable)
type Variable = VariableF TC (Type TC)
type TVariable = VariableF T (Type T)  -- TODO THIS IS SO BAD.
type IsFromExternalModule = Bool  -- FOR OPTIMIZATION, SO WE WON'T POINTLESSLY TRY TO SUBSTITUTE FOREIGN FUNCTIONS!

data VariableProto
  = PDefinedVariable Def.UniqueVar
  | PDefinedFunction (Function TC)
  | PDefinedClassFunction (ClassFunDec TC)
  deriving (Eq, Ord)

data EnvF phase t
  = Env Def.EnvID [(VariableF phase t, Def.Locality, t)] (Map VariableProto Def.Locality) Def.EnvStack -- t is here, because of recursion schemes. UniqueVar, because we don't know which environments will be used in the end. We will replace it with a `Variable` equivalent AFTER we monomorphise.
  -- The last map is a HACK
  | RecursiveEnv Def.EnvID IsEmpty  -- Recursive functions won't have access to their environment while typechecking... kinda stupid. ehh... but we're solving an actual issue here. `IsEmpty` is used in Mono to let us know if this function's environment was empty or not.
  deriving (Functor, Foldable, Traversable)
type Env = EnvF TC (Type TC)

data EnvUnionF phase t = EnvUnion
  { unionID :: Def.UnionID
  , union :: [(Maybe Def.UniqueClassInstantiation, Def.UniqueFunctionInstantiation, [t], EnvF phase t)]  -- (ufi, assocs, env) -- List can be empty for types written by the programmer (which also don't have any other function's environment yet). This is okay, because functions are not yet monomorphised.
  } deriving (Eq, Ord, Functor, Foldable, Traversable)

type EnvUnion = UnionUniID  -- changed to a REF.
type IsEmpty = Bool


data FunOther phase = FunOther
  { functionScheme :: Scheme phase
  , functionAssociations :: [FunctionTypeAssociation phase]
  -- , functionClassInstantiationAssocs :: ClassInstantiationAssocs  -- TODO: might not be necessary we can just map them.
  , functionAnnotations :: [Def.Ann]
  , functionLocation :: Def.Location
  }

data Scheme phase = Scheme [TVar phase] [(XEnvUnion phase, [Type phase], Type phase)]  -- type are stored with scheme ONLY FOR CONVENIENCE, SO WE WON'T HAVE TO RE-SEARCH FOR THEM.

data FunctionTypeAssociation phase = FunctionTypeAssociation (TVar phase) (Type phase) (ClassFunDec phase) Def.UniqueClassInstantiation

-- I'm not sure about level. We don't need type applications now.
-- It's needed to check if we need to keep it in the environment or not.
type ClassInstantiationAssocs = Map (Maybe (Def.UniqueFunctionInstantiation, Type TC), Def.UniqueClassInstantiation) (Type TC, ([Type TC], InstFun TC), Def.EnvStack, Def.UniqueFunctionInstantiation)
data TypeAssociation = TypeAssociation (Def.Location, Type TC) (Def.Location, Type TC) (ClassFunDec TC) Def.UniqueClassInstantiation (Maybe Def.UniqueFunctionInstantiation) [Def.EnvID]  -- TODO: I think only one location is required. We can't really get location of self?


data TypeUni = TypeUni
  { typeUni :: TypeTypeUni
  , unionUni :: UnionTypeUni
  }

type EnvAdditions = Map Def.EnvID [(Variable, Def.Locality, Type TC)]


getTypeFromUni :: TypeUni -> TypeID -> (TypeID, TypeF TC TypeID)
getTypeFromUni typeUni = getSomethingFromRefMap fromTypeID TypeID typeUni.typeUni

getUnionFromUni :: TypeUni -> UnionUniID -> (UnionUniID, EnvUnionF TC TypeID)
getUnionFromUni typeUni = getSomethingFromRefMap fromUnionUniID UnionUniID typeUni.unionUni

getSomethingFromRefMap :: (k -> Int) -> (Int -> k) -> RefMap k a -> k -> (k, a)
{-# inline getSomethingFromRefMap #-}
getSomethingFromRefMap toInt fromInt refmap = first fromInt . go . toInt where
  go x = case refmap IntMap.!? x of
    Nothing -> error "key not found. should not happen"
    Just (Right a) -> (x, a)
    Just (Left nx) -> go nx

type TypeTypeUni = RefMap TypeID (TypeF TC TypeID)
type UnionTypeUni = RefMap UnionUniID (EnvUnionF TC TypeID)
type RefMap k a = IntMap (Either Int a)  -- TODO: change it later to IntMap and observe an improvement?


data Mod phase = Mod
  { topLevelStatements :: [AnnStmt phase]
  , exports :: Exports phase
  , uni :: TypeUni
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


envID :: EnvF phase t -> Def.EnvID
envID = \case
  Env eid _ _ _ -> eid
  RecursiveEnv eid _ -> eid


asProto :: Variable -> VariableProto
asProto = \case
  DefinedVariable v -> PDefinedVariable v
  DefinedFunction fn _ _ _ -> PDefinedFunction fn
  DefinedClassFunction cd _ _ _ -> PDefinedClassFunction cd

---------


isUnionEmpty :: EnvUnionF phase t -> Bool
isUnionEmpty (EnvUnion _ []) = True
isUnionEmpty _ = False



dbgSnapshot :: (PP (XDClass phase), PP (XDTCon phase)) => ScopeSnapshot phase -> Def.Context
dbgSnapshot = Def.ppLines . fmap (\(cd, insts) -> pf "% => %" (Def.ppDef cd) (Def.encloseSepBy "[" "]" ", " $ fmap (\dd -> pp dd.ddName) $ Set.toList $ Map.keysSet insts) :: Def.Context) . Map.toList



---------


instance Eq t => Eq (EnvF phase t) where
  Env lid lts _ _ == Env rid rts _ _ = lid == rid && (lts <&> \(_, _, x) -> x) == (rts <&> \(_, _, x) -> x)
  l == r  = envID l == envID r

instance Ord t => Ord (EnvF phase t) where
  Env lid lts _ _ `compare` Env rid rts _ _ = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)
  l `compare` r = envID l `compare` envID r

instance Eq1 (EnvF phase) where
  liftEq f (Env lid lts _ _) (Env rid rts _ _) = lid == rid && and (zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts)
  liftEq _ l r = envID l == envID r

instance Ord1 (EnvF phase) where
  liftCompare f (Env lid lts _ _) (Env rid rts _ _) = case lid `compare` rid of
    EQ -> mconcat $ zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts
    ord -> ord
  liftCompare _ l r = envID l `compare` envID r


instance Eq TyVar where
  tyv == tyv' = tyv.actualUnique == tyv'.actualUnique

instance Ord TyVar where
  tyv `compare` tyv' = tyv.fromTyV `compare` tyv'.fromTyV


instance (Eq t, Eq (XFunVar phase)) => Eq (VariableF phase t) where
  l == r = case (l, r) of
    (DefinedVariable uv, DefinedVariable uv') -> uv == uv'
    (DefinedFunction fn ts _ ufi, DefinedFunction fn' ts' _ ufi') -> (fn, ts, ufi) == (fn', ts', ufi')
    (DefinedClassFunction cfd _ t uci, DefinedClassFunction cfd' _ t' uci') -> (cfd, t, uci) == (cfd', t', uci')
    _ -> False

instance (Ord t, Ord (XFunVar phase)) => Ord (VariableF phase t) where
  l `compare` r = case (l, r) of
    (DefinedVariable uv, DefinedVariable uv') -> uv `compare` uv'
    (DefinedFunction fn ts _ ufi, DefinedFunction fn' ts' _ ufi') -> (fn, ts, ufi') `compare` (fn', ts', ufi')
    (DefinedClassFunction cfd _ t uci, DefinedClassFunction cfd' _ t' uci') -> (cfd, t, uci) `compare` (cfd', t', uci')

    (DefinedVariable {}, _) -> LT

    (DefinedFunction {}, DefinedVariable {}) -> GT
    (DefinedFunction {}, _) -> LT

    (DefinedClassFunction {}, _) -> GT


--------

instance (PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (XTOther phase), PP (XTFun phase), PP (XExprNode phase), Def.PPDef (XTCon phase), PP (XLamVar phase), PP (XMutAccess phase), PP (XStringInterpolation phase), PP (XTConOther phase), PP (Type phase)) => PP (Mod phase) where
  pp m = Def.ppLines m.topLevelStatements

instance (PPDef (XClass phase), PP (VariableF phase (Type phase)), PP (Type phase), PP (XEnvUnion phase) ) => PP (FunOther phase) where
  pp fo = pf "% %" fo.functionScheme fo.functionAssociations

instance (PP t, PP (VariableF phase t)) => PP (EnvUnionF phase t) where
  pp EnvUnion { unionID = uid, union = us } = pp uid <> Def.encloseSepBy "{" "}" ", " (pp <$> us)

instance (PP a, PP (VariableF phase a)) => PP (EnvF phase a) where
  pp = \case
    Env eid vs _ lev -> pp eid <> fromString (Def.printf "(%)" (show lev)) <> Def.encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> pp loc <> pp v <+> pp t) vs)
    RecursiveEnv eid isEmpty -> fromString $ Def.printf "%[REC%]" (pp eid) (if isEmpty then "(empty)" else "(some)" :: Def.Context)

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

instance PP (Type phase) => PP (ExprNode phase) where
  pp en = pp en.t <+> pp en.loc

instance (PP (Type phase), PPDef (XClass phase)) => PP (FunctionTypeAssociation phase) where
  pp (FunctionTypeAssociation tv t _ _) = fromString $ Def.printf "(% => %)" (pp tv) (pp t)

instance PP TypeAssociation where
  pp (TypeAssociation from to _ _ _ _) = fromString $ Def.printf "(% => %)" (pp (snd from)) (pp (snd to))

instance PP a => PP (VariableF TC a) where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f assocs _ ufi -> pp f.functionDeclaration.functionId <> "&F" <> pp ufi <> "(" <> Def.ppSet (\(FunctionTypeAssociation tv t _ uci) -> pp t) f.functionDeclaration.functionOther.functionAssociations <> "/" <> Def.ppSet pp assocs <> ")"
    DefinedClassFunction (CFD cd uv _ _ _ _) insts self uci ->
      fromString $ Def.printf "%&%&C<%>[%]" (pp uv) (pp uci) (pp self) (Def.sepBy ", " $ fmap (\inst -> (pp . ddName . fst . instType) inst) (Map.elems (Def.defaultEmpty cd insts)))

-- bad duplicate instance
instance PP a => PP (VariableF T a) where
  pp = \case
    DefinedVariable v -> pp v
    DefinedFunction f assocs _ ufi -> pp f.functionDeclaration.functionId <> "&F" <> pp ufi <> "(" <> Def.ppSet (\(FunctionTypeAssociation tv t _ uci) -> pp t) f.functionDeclaration.functionOther.functionAssociations <> "/" <> Def.ppSet pp assocs <> ")"
    DefinedClassFunction (CFD cd uv _ _ _ _) insts self uci ->
      fromString $ Def.printf "%&%&C<%>[%]" (pp uv) (pp uci) (pp self) (Def.sepBy ", " $ fmap (\inst -> (pp . ddName . fst . instType) inst) (Map.elems (Def.defaultEmpty cd insts)))

instance (PP (Type phase), PP (VariableF phase (Type phase))) => PP (LamDec phase) where
  pp (LamDec uv env) = pp env <> pp uv

instance (PP (Type phase), PPDef (XClass phase), PP (VariableF phase (Type phase)), PP (XEnvUnion phase) ) => PP (Scheme phase) where
  pp (Scheme tvars unions) = Def.ppSet pp tvars <+> Def.ppSet pp (unions <&> \(u, params, ret) -> pf "%% -> %" u (pp <$> params) ret :: Def.Context)

instance PP TypeUni where
  pp tu = Def.ppLines
    [ pf "Type Uni: %" tu.typeUni :: Def.Context
    , pf "Union Uni: %" tu.unionUni
    ]

instance PPDef TypeID where
  ppDef = pp

-- instance {-# OVERLAPPING #-} PP ClassInstantiationAssocs where
--   pp classInstantiationAssocs = fromString $ Def.printf "CIA: %" (Def.ppMap $ fmap (bimap pp (Def.ppTup . bimap pp (Def.ppTup . bimap (Def.encloseSepBy "[" "]" ", " . fmap pp) (\ifn -> pp ifn.instFunDec.functionId)))) $ fmap (\(ufiuci, (l, r, _, _)) -> (ufiuci, (l, r))) $ Map.toList classInstantiationAssocs)
