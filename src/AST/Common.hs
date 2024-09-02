{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
module AST.Common where

import Data.Text (Text)
import Data.Unique (Unique, hashUnique)
import qualified Data.Text as Text


-- Common type families
type family Type phase
type family Env phase
type family EnvUnion phase
type family Expr phase
type family Stmt phase
type family AnnStmt phase
type family Module phase


-- Type safety definitions
newtype TVar = TV { fromTV :: Text } deriving (Show, Eq, Ord)
newtype TCon = TC { fromTC :: Text } deriving (Show, Eq, Ord)
newtype ConName = CN { fromCN :: Text } deriving (Show, Eq, Ord)
newtype VarName = VN { fromVN :: Text } deriving (Show, Eq, Ord)

data Op
  = Plus
  | Minus
  | Times
  | Divide

  | Equals
  | NotEquals
  deriving (Eq, Ord, Show)

data LitType
  = LInt Int
  deriving (Eq, Ord, Show)


data Ann  -- or should this be a Map or something?
  = ACType Text
  | ACLit Text
  | ACStdInclude Text
  deriving (Show, Eq, Ord)
  
data Annotated a = Annotated [Ann] a deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- data AnnotatedThing f a = AnnThing [Ann] (f a) deriving (Show, Eq, Ord, Functor, Foldable, Traversable)


-- Variable uniqueness
data UniqueVar = VI
  { varID :: Unique
  , varName :: VarName
  , mutability :: Mutability
  }


data UniqueCon = CI
  { conID :: Unique
  , conName :: ConName
  -- add info about constructor for later compilation
  }

data UniqueType = TI
  { typeID :: Unique
  , typeName :: TCon
  -- add info about structure for later compilation
  }


-- type instances for the small datatypes

instance Eq UniqueVar where
  VI { varID = l } == VI { varID = r } = l == r

instance Ord UniqueVar where
  VI { varID = l } `compare` VI { varID = r } = l `compare` r

-- temporary instance
instance Show UniqueVar where
  show (VI { varID = vid, varName = vname, mutability = vt }) = "v" <> show (hashUnique vid) <> Text.unpack (fromVN vname) <> show vt


instance Show UniqueCon where
  show (CI { conID = id, conName = name }) = undefined
  
instance Eq UniqueCon where
  CI { conID = l } == CI { conID = r } = l == r

instance Ord UniqueCon where
  CI { conID = l } `compare` CI { conID = r } = l `compare` r


instance Show UniqueType where
  show (TI { typeID = tid, typeName = name }) = show name <> "@" <> show (hashUnique tid)

instance Eq UniqueType where
  TI { typeID = l } == TI { typeID = r } = l == r

instance Ord UniqueType where
  TI { typeID = l } `compare` TI { typeID = r } = l `compare` r

  
-- ...plus additional tags
data Mutability = Immutable | Mutable deriving (Show, Eq, Ord)
data Locality = Local | FromEnvironment | External deriving (Show, Eq, Ord)
