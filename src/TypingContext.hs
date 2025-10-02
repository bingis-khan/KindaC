{-# LANGUAGE OverloadedRecordDot, TemplateHaskell #-}
module TypingContext (module TypingContext) where

import Data.Map (Map)
import qualified AST.Def as Def
import AST.Def (PP, TypeID (..), UnionUniID (..), Context)
import Data.IntMap (IntMap)
import AST.Typed (TC, EnvUnionF)
import AST.Common (TypeF, Type)
import qualified AST.Typed as T
import Data.Biapplicative (first)
import qualified Data.IntMap as IntMap
import Data.Fix (Fix)
import Lens.Micro (ASetter', sets, (^.), (%~), (.~), (&))
import Lens.Micro.TH (makeLenses)



type TypeTypeUni = RefMap TypeID (TypeF TC TypeID)
type UnionTypeUni = RefMap UnionUniID (EnvUnionF T.EnvUnion TypeID)
type RefMap k a = IntMap (Either Int a)  -- TODO: change it later to IntMap and observe an improvement?

newtype TypeIDGen = TypeIDGen TypeID
newtype UnionIDGen = UnionIDGen UnionUniID


data TypeUni = TypeUni
  { _typeUni :: TypeTypeUni
  , _unionUni :: UnionTypeUni
  }
makeLenses ''TypeUni

type Envs = Map Def.EnvID (T.EnvDef, T.Scheme TC)

data TypingContext = TypingContext
    { globalTypeIDGen :: TypeIDGen
    , globalUnionIDGen :: UnionIDGen
    , _globalTypeUni :: TypeUni
    , globalEnvs :: Envs
    , globalInsts :: ()
    }
makeLenses ''TypingContext



-- globalEnvAddition' :: ASetter' TypingContext EnvAdditions
-- globalEnvAddition' = sets $ \set tc -> tc { globalEnvAddition = set tc.globalEnvAddition }

emptyContext :: TypingContext
emptyContext = TypingContext
  { globalTypeIDGen = TypeIDGen $ TypeID 0
  , globalUnionIDGen = UnionIDGen $ UnionUniID 0
  , _globalTypeUni = TypeUni { _typeUni = mempty, _unionUni = mempty }
  , globalEnvs = mempty
  , globalInsts = mempty
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
getSomethingFromRefMap toInt fromInt refmap = first fromInt . go . toInt where
  go x = case refmap IntMap.!? x of
    Nothing -> (x, error "key not found. should not happen")
    Just (Right a) -> (x, a)
    Just (Left nx) -> go nx

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


