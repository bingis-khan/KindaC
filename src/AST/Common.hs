{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
module AST.Common (module AST.Common) where

import Data.Text (Text)
import Data.Unique (Unique, hashUnique)
import qualified Data.Text as Text
import Control.Monad.Trans.Reader (Reader, runReader)
import Prettyprinter (Doc)
import Data.String (IsString (..))
import qualified Prettyprinter as PP
import Data.Foldable (fold)
import Data.List (intersperse)


-- FUTURE TODO: GHC is using type families in a MUCH SMARTER WAY:
-- data Expr phase
--   | ELit (Lit phase)  -- this is also a type family

--   -- some other stuff
--   | EExtraCons (ExCons phase)  -- not enough / wrong constructors? no problem! just move them in the extra field and use a separate datatype
-- in short, more type families, but they provide a stable tree. same amount of expressiveness and type safety as separate ASTs!
-- the only problem i see is incomprehensible error messages (but much better than what I had before with a single AST...)
--   also, I can't show stuff. but it's good!! I should not use show with custom datatypes. instead, I should use custom printing functions.
--   in the near future, I'll remove all Show/Show1 instances.
-- same amount of mapping tho. it's not that big of a deal, to be honest. just, if I want to add/remove some feature, it'll take more code in my current design, but I don't really mind that now.

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
  show (CI { conID = id, conName = name }) = show name <> "@" <> show (hashUnique id)
  
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


-- simplifies printing functions - not really needed..?
newtype UnionID = UnionID { fromUnionID :: Unique } deriving (Eq, Ord)
newtype EnvID = EnvID { fromEnvID :: Unique } deriving (Eq, Ord)

instance Show UnionID where
  show = show . hashUnique . fromUnionID

instance Show EnvID where
  show = show . hashUnique . fromEnvID


---------------------

----------------
-- Useful stuff
----------------

fromResult :: Result e a -> Either e a
fromResult = \case
  Failure e -> Left e
  Success x -> Right x

toResult :: Either e a -> Result e a
toResult = \case
  Left e -> Failure e
  Right a -> Success a

data Result e a
  = Failure e
  | Success a
  deriving (Functor, Foldable, Traversable)

instance Semigroup e => Applicative (Result e) where
  Failure e <*> Failure e' = Failure $ e <> e'
  Failure e <*> _ = Failure e
  _ <*> Failure e = Failure e
  Success f <*> Success x = Success (f x)

  pure = Success


-----------------
-- Printing stuff
-----------------


-- Context that stores the pretty printer Doc + data + help with, for example, names.
type Context = Reader CtxData (Doc ())  -- I guess I can add syntax coloring or something with the annotation (the () in Doc)
data CtxData = CtxData  -- basically stuff like printing options or something (eg. don't print types)

ctx :: (a -> Context) -> a -> String
ctx f = show . flip runReader CtxData . f

ppBody :: Foldable t => (a -> Context) -> Context -> t a -> Context
ppBody f header = indent header . ppLines f


-- Technically should be something like Text for the annotation type, but I need to have access to context in annotations
comment :: Context -> Context -> Context
comment s ctx = "#" <+> s <\> ctx

annotate :: [Ann] -> Context -> Context
annotate [] ctx = ctx
annotate xs ctx = "\n" <> ppAnn xs <\> ctx

encloseSepBy :: Monoid a => a -> a -> a -> [a] -> a
encloseSepBy l r p cs = l <> sepBy p cs <> r

sepBy :: Monoid a => a -> [a] -> a
sepBy p = fold . intersperse p

indent :: Context -> Context -> Context
indent header = (header <>) . fmap (PP.nest 2) . ("\n" <>)

ppLines :: Foldable t => (a -> Context) -> t a -> Context
ppLines f = foldMap ((<>"\n") . f)

ppVar :: Locality -> UniqueVar -> Context
ppVar l v = localTag <?+> vt <> pretty (fromVN v.varName) <> "$" <> pretty (hashUnique v.varID)
  where
    vt = case v.mutability of
      Immutable -> ""
      Mutable -> "*"

    localTag = case l of
      Local -> Nothing
      FromEnvironment -> Just "^"
      External -> Just "E"

-- annotate constructors with '@'
ppCon :: UniqueCon -> Context
ppCon con = "@" <> pretty (fromCN con.conName) <> "$" <> pretty (hashUnique con.conID)

ppTypeInfo :: UniqueType -> Context
ppTypeInfo t = pretty (fromTC t.typeName) <> "$" <> pretty (hashUnique t.typeID)

ppEnvID :: EnvID -> Context
ppEnvID = pretty . hashUnique . fromEnvID

ppUnionID :: UnionID -> Context
ppUnionID = pretty . hashUnique . fromUnionID

ppUnique :: Unique -> Context
ppUnique = pretty . hashUnique

-- ppFunEnv :: FunEnv Context -> Context
-- ppFunEnv (FunEnv vts) = encloseSepBy "[" "]" " " (fmap (encloseSepBy "[" "]" ", " . fmap (\(v, t) -> rVar Local v <+> encloseSepBy "[" "]" " " t)) vts)

-- ppEnv :: Env Context -> Context
-- ppEnv (Env env) = "%" <> encloseSepBy "$[" "]" " " (NonEmpty.toList $ fmap (encloseSepBy "[" "]" " ") env)

-- ppTypedEnv :: (t -> Context) -> TypedEnv VarInfo t -> Context
-- ppTypedEnv = ppTypedEnv' (rVar Local)

-- ppTypedEnv' :: (v -> Context) -> (t -> Context) -> TypedEnv v t -> Context
-- ppTypedEnv' fv ft env =
--   let (TypedEnv vts) = fmap ft env
--   in encloseSepBy "$#[" "]" " " $ fmap (\(v, ts) -> fv v <+> encloseSepBy "[" "]" " " ts) vts

-- ppVarEnv :: VarEnv VarInfo t -> Context
-- ppVarEnv (VarEnv vs) = encloseSepBy "$[" "]" " " (fmap (rVar Local) vs)

-- ppNoEnv :: NoEnv a -> Context
-- ppNoEnv _ = "[<no env>]"


ppAnn :: [Ann] -> Context
ppAnn [] = mempty
ppAnn anns = "#[" <> sepBy ", " (map ann anns) <> "]"
  where
    ann :: Ann -> Context
    ann = \case
      ACType s -> "ctype" <+> quote s
      ACStdInclude s -> "cstdinclude" <+> quote s
      ACLit s -> "clit" <+> quote s

    quote = pure . PP.squotes . PP.pretty


infixr 6 <+>
(<+>) :: Context -> Context -> Context
x <+> y = liftA2 (PP.<+>) x y

infixr 6 <+?>
(<+?>) :: Context -> Maybe Context -> Context
x <+?> Nothing = x
x <+?> Just y = x <+> y

infixr 6 <?+>
(<?+>) :: Maybe Context -> Context -> Context
Nothing <?+> x = x
Just y <?+> x = y <+> x

infixr 5 <\>
(<\>) :: Context -> Context -> Context
x <\> y = x <> "\n" <> y



instance Semigroup Context where
  x <> y = liftA2 (<>) x y

instance Monoid Context where
  mempty = pure mempty

instance IsString Context where
  fromString = pretty

pretty :: PP.Pretty a => a -> Context
pretty = pure . PP.pretty


fromEither :: Either a a -> a
fromEither = \case
  Left x -> x
  Right x -> x
