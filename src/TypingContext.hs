{-# LANGUAGE OverloadedRecordDot, TemplateHaskell #-}
module TypingContext (module TypingContext) where

import qualified AST.Def as Def
import AST.Def (PP, TypeID (..), UnionUniID (..), Context, EnvID)
import Data.IntMap (IntMap)
import AST.Typed (TC, EnvUnionF)
import AST.Common (TypeF, Type, Function)
import qualified AST.Typed as T
import Data.Biapplicative (first)
import qualified Data.IntMap as IntMap
import Lens.Micro ((^.), (%~))
import Lens.Micro.TH (makeLenses)
import Data.Map (Map, (!?))



type TypeTypeUni = RefMap TypeID (TypeF TC TypeID)
type UnionTypeUni = RefMap UnionUniID (EnvUnionF T.EnvUnion TypeID)
type RefMap k a = IntMap (Either Int a)  -- TODO: change it later to IntMap and observe an improvement?

type Instances = Map Def.ClassInstID (Function TC, T.Match)

newtype TypeIDGen = TypeIDGen TypeID
newtype UnionIDGen = UnionIDGen UnionUniID


data TypeUni = TypeUni
  { _typeUni :: TypeTypeUni
  , _unionUni :: UnionTypeUni
  }
makeLenses ''TypeUni

type EnvsAdds = [(Def.EnvID, [(T.Variable, Def.Locality, Type TC)])]
type Envs = Map Def.EnvID T.EnvDef

data TypingContext = TypingContext
    { globalTypeIDGen :: TypeIDGen
    , globalUnionIDGen :: UnionIDGen
    , _globalTypeUni :: TypeUni
    , _globalEnvs :: Envs  -- TODO: for more type safety, just store vars here and make EnvID/EnvStack local.
    , _globalInsts :: Instances
    }
makeLenses ''TypingContext



-- globalEnvAddition' :: ASetter' TypingContext EnvAdditions
-- globalEnvAddition' = sets $ \set tc -> tc { globalEnvAddition = set tc.globalEnvAddition }

emptyContext :: TypingContext
emptyContext = TypingContext
  { globalTypeIDGen = TypeIDGen $ TypeID 0
  , globalUnionIDGen = UnionIDGen $ UnionUniID 0
  , _globalTypeUni = TypeUni { _typeUni = mempty, _unionUni = mempty }
  , _globalEnvs = mempty
  , _globalInsts = mempty
  }


--------------
--- TypeUni
--------------



getTypeFromUni :: TypeUni -> TypeID -> (TypeID, TypeF TC TypeID)
getTypeFromUni typeUni = getSomethingFromRefMap fromTypeID TypeID typeUni._typeUni

getUnionFromUni :: TypeUni -> UnionUniID -> (UnionUniID, EnvUnionF T.EnvUnion TypeID)
getUnionFromUni typeUni = getSomethingFromRefMap fromUnionUniID UnionUniID typeUni._unionUni

getSomethingFromRefMap :: (k -> Int) -> (Int -> k) -> RefMap k a -> k -> (k, a)
{-# inline getSomethingFromRefMap #-}
getSomethingFromRefMap toInt fromInt refmap = first fromInt . goRef . toInt where
  goRef x = case refmap IntMap.!? x of
    Nothing -> (x, error "key not found. should not happen")
    Just (Right a) -> (x, a)
    Just (Left nx) -> goRef nx

-- pp type and replaces the default.
ppTypeFromUniSafe :: TypeUni -> TypeID -> Context
ppTypeFromUniSafe tu tid =
  let go x = case tu._typeUni IntMap.!? (fromTypeID x) of
        Nothing -> Def.ppDef x
        Just (Right a) -> Def.pp $ go <$> a
        Just (Left nx) -> go (TypeID nx)
  in go tid

ppUnionFromUniSafe :: TypeUni -> UnionUniID -> Context
ppUnionFromUniSafe tu uuid =
  let go x = case tu._unionUni IntMap.!? (fromUnionUniID x) of
        Nothing -> Def.ppDef x
        Just (Right a) -> Def.pp $ ppTypeFromUniSafe tu <$> a
        Just (Left nx) -> go $ UnionUniID nx
  in go uuid

ppEnvFromUniSafe :: Envs -> EnvID -> Context
ppEnvFromUniSafe envs eid = case envs !? eid of
  Nothing -> Def.pf "%" (T.EnvDef eid [] [] :: T.EnvDef)
  Just ed -> Def.pf "%" ed

ppUnionIDFromUniSafe :: TypeUni -> UnionUniID -> Context
ppUnionIDFromUniSafe tu uuid =
  let go x = case tu._unionUni IntMap.!? (fromUnionUniID x) of
        Nothing -> Def.ppDef x
        Just (Right a) -> Def.pp a.unionID
        Just (Left nx) -> go $ UnionUniID nx
  in go uuid

insertToRefMap :: k -> a -> RefMap k a -> RefMap k a
insertToRefMap = undefined


instance PP TypeUni where
  pp tu = Def.ppLines
    [ Def.pf "Type Uni: %" tu._typeUni :: Def.Context
    , Def.pf "Union Uni: %" tu._unionUni
    ]



-- Other stuff

type TCMod = TypingContext -> TypingContext

nextTypeID :: TypingContext -> (TypeID, TypingContext)
nextTypeID tc =
  let TypeIDGen tid@(TypeID x) = tc.globalTypeIDGen
      tc' = tc { globalTypeIDGen = TypeIDGen $ TypeID $ x + 1 }
  in (tid, tc')

nextUnionUniID :: TypingContext -> (UnionUniID, TypingContext)
nextUnionUniID tc =
  let UnionIDGen uid@(UnionUniID x) = tc.globalUnionIDGen
      tc' = tc { globalUnionIDGen = UnionIDGen $ UnionUniID $ x + 1 }
  in (uid, tc')


numTypesAndUnionsDefined :: TypingContext -> (Int, Int)
numTypesAndUnionsDefined tc =
  let tu = tc ^. globalTypeUni
  in (IntMap.size tu._typeUni, IntMap.size tu._unionUni)


-- modify type unions
modifyTypeUni :: (TypeTypeUni -> TypeTypeUni) -> TCMod
modifyTypeUni f = globalTypeUni . typeUni %~ f

-- modify env unions
modifyUniUni :: (UnionTypeUni -> UnionTypeUni) -> TCMod
modifyUniUni f = globalTypeUni . unionUni %~ f


getEnv :: TypingContext -> Def.EnvID -> T.EnvDef
getEnv tc eid = case (tc ^. globalEnvs) !? eid of
  Just env -> env
  Nothing -> -- NOTE: this means that it's a Con environment, so just return a con env
    T.EnvDef eid [] []
    -- it might be a bit error prone tho. Maybe we should register constructor environments beforehand?
