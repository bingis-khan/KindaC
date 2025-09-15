{-# LANGUAGE OverloadedRecordDot #-}
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
import Lens.Micro (ASetter', sets)



data TypingContext = TypingContext
    { globalTypeIDGen :: TypeIDGen
    , globalUnionIDGen :: UnionIDGen
    , globalTypeUni :: TypeUni
    , globalEnvAddition :: EnvAdditions
    }

globalEnvAddition' :: ASetter' TypingContext EnvAdditions
globalEnvAddition' = sets $ \set tc -> tc { globalEnvAddition = set tc.globalEnvAddition }

emptyContext :: TypingContext
emptyContext = TypingContext
  { globalTypeIDGen = TypeIDGen $ TypeID 0
  , globalUnionIDGen = UnionIDGen $ UnionUniID 0
  , globalTypeUni = TypeUni { typeUni = mempty, unionUni = mempty }
  , globalEnvAddition = mempty
  }


--------------
--- TypeUni
--------------

data TypeUni = TypeUni
  { typeUni :: TypeTypeUni
  , unionUni :: UnionTypeUni
  }

type EnvAdditions = Map Def.EnvID [(T.Variable, Def.Locality, Type TC)]


getTypeFromUni :: TypeUni -> TypeID -> (TypeID, TypeF TC TypeID)
getTypeFromUni typeUni = getSomethingFromRefMap fromTypeID TypeID typeUni.typeUni

getUnionFromUni :: TypeUni -> UnionUniID -> (UnionUniID, EnvUnionF TC TypeID)
getUnionFromUni typeUni = getSomethingFromRefMap fromUnionUniID UnionUniID typeUni.unionUni

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
  let go x = case tu.typeUni IntMap.!? (fromTypeID x) of
        Nothing -> Def.ppDef x
        Just (Right a) -> Def.pp $ go <$> a
        Just (Left nx) -> go (TypeID nx)
  in go tid

type TypeTypeUni = RefMap TypeID (TypeF TC TypeID)
type UnionTypeUni = RefMap UnionUniID (EnvUnionF TC TypeID)
type RefMap k a = IntMap (Either Int a)  -- TODO: change it later to IntMap and observe an improvement?

insertToRefMap :: k -> a -> RefMap k a -> RefMap k a
insertToRefMap = undefined


instance PP TypeUni where
  pp tu = Def.ppLines
    [ Def.pf "Type Uni: %" tu.typeUni :: Def.Context
    , Def.pf "Union Uni: %" tu.unionUni
    ]



-- Other stuff

newtype TypeIDGen = TypeIDGen TypeID
newtype UnionIDGen = UnionIDGen UnionUniID


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
  let tu = tc.globalTypeUni
  in (IntMap.size tu.typeUni, IntMap.size tu.unionUni)


-- modify type unions
-- todo: microlensify it
modifyTypeUni :: (TypeTypeUni -> TypeTypeUni) -> TCMod
modifyTypeUni f tc = 
  tc { globalTypeUni = tc.globalTypeUni { typeUni = f tc.globalTypeUni.typeUni } }

-- modify env unions
modifyUniUni :: (UnionTypeUni -> UnionTypeUni) -> TCMod
modifyUniUni f tc = tc { globalTypeUni = tc.globalTypeUni { unionUni = f tc.globalTypeUni.unionUni } }


