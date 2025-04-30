{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
module AST.Common (module AST.Common) where

import Data.Text (Text)
import Data.Unique (Unique, hashUnique)
import qualified Data.Text as Text
import Control.Monad.Trans.Reader (Reader, runReader, ask)
import Prettyprinter (Doc)
import Data.String (IsString (..))
import qualified Prettyprinter as PP
import Data.Foldable (fold)
import Data.List (intersperse)
import qualified Text.Printf
import Text.Printf (PrintfArg(..), formatString)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad (unless)
import Data.Char (toUpper)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bitraversable (bitraverse)
import qualified Data.Set as Set


-- set printing config
defaultContext, debugContext, runtimeContext, showContext, dc, rc :: CtxData
defaultContext = dc

dc = debugContext
rc = runtimeContext

-- context for debugging with all messages enabled.
debugContext = CtxData
  { silent = False
  , printIdentifiers = True
  , displayTypeParameters = False
  }

-- disable debug messages for "runtime".
runtimeContext = CtxData
  { silent = True
  , printIdentifiers = False
  , displayTypeParameters = False
  }

-- show types and stuffi for the user (display types accurately to their definition, etc.)
showContext = CtxData
  { silent = False
  , printIdentifiers = False
  , displayTypeParameters = True
  }


-- General composition operator (easier Fix usage)
--  copied from TypeCompose package (I didn't need the whole thing, so I just copied the definition)
--  Now you can use type composition.
infixl 9 :.
newtype (g :. f) a = O (g (f a)) deriving (Eq, Ord, Functor, Foldable, Traversable)

unO :: (g :. f) a -> g (f a)
unO (O gfa) = gfa


-- Type safety definitions
newtype UnboundTVar = UTV { fromUTV :: Text } deriving (Show, Eq, Ord)
newtype TCon = TC { fromTC :: Text } deriving (Show, Eq, Ord)
newtype ConName = CN { fromCN :: Text } deriving (Show, Eq, Ord)
newtype VarName = VN { fromVN :: Text } deriving (Show, Eq, Ord)
newtype MemName = MN { fromMN :: Text } deriving (Show, Eq, Ord)
newtype ClassName = TCN { fromTN :: Text } deriving (Show, Eq, Ord)

data Op
  = Plus
  | Minus
  | Times
  | Divide

  | Equals
  | NotEquals
  deriving (Eq, Ord, Show)

data LitType
  -- Number types. They have infinite precision, because I don't want to lose the information and give the appropriate message.
  = LInt Integer
  | LFloat Rational

  -- | LString Text
  deriving (Eq, Ord, Show)

-- Different annotation types.
-- TODO: right now they are parsed and typed properly. But they don't really have to be.
data Ann
  = ACType Text
  | ACLit Text
  | ACStdInclude Text
  deriving (Show, Eq, Ord)

-- Annotation decorator thing.
data Annotated a = Annotated [Ann] a deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- Variable uniqueness
data UniqueVar = VI
  { varID :: Unique
  , varName :: VarName
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

data UniqueMem = MI  -- unlike the previous ones, used after (and including) Mono module.
  { memID :: Unique
  , memName :: MemName
  }

data UniqueClass = TCI
  { classID :: Unique
  , className :: ClassName
  }

-- TODO: this is kinda bad. It should probably be done in subst or something, but I want it done quick.
newtype UniqueClassInstantiation = UCI { fromUCI :: Unique } deriving (Eq, Ord)

-- I need to use classes in the same context as types.. but I use different types.
-- Q: should I just remove UniqueClass?
-- A: Nah, Resolver should decide between UniqueType and UniqueClass
uniqueClassAsTypeName :: UniqueClass -> TCon
uniqueClassAsTypeName TCI { className = cn } = TC cn.fromTN

data Binding
  = BindByType UniqueType
  | BindByVar  UniqueVar
  | BindByInst UniqueClass
  deriving (Eq, Ord)



-- type instances for the small datatypes

instance Eq UniqueVar where
  VI { varID = l } == VI { varID = r } = l == r

instance Ord UniqueVar where
  VI { varID = l } `compare` VI { varID = r } = l `compare` r

-- temporary instance
instance Show UniqueVar where
  show (VI { varID = vid, varName = vname }) = "v" <> show (hashUnique vid) <> Text.unpack (fromVN vname)


instance Show UniqueCon where
  show (CI { conID = cid, conName = name }) = show name <> "@" <> show (hashUnique cid)

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

instance Show UniqueMem where
  show (MI { memID = tid, memName = name }) = show name <> "@" <> show (hashUnique tid)

instance Eq UniqueMem where
  MI { memID = l } == MI { memID = r } = l == r

instance Ord UniqueMem where
  MI { memID = l } `compare` MI { memID = r } = l `compare` r

instance Eq UniqueClass where
  TCI { classID = l } == TCI { classID = r } = l == r

instance Ord UniqueClass where
  TCI { classID = l } `compare` TCI { classID = r } = l `compare` r

instance Show UniqueClass where
  show (TCI { className = name, classID = l }) = show name.fromTN <> "@#" <> show (hashUnique l)


instance Show UniqueClassInstantiation where
  show (UCI { fromUCI = un }) = printf "UCI%d" (hashUnique un)


-- ...plus additional tags
data Locality = Local | FromEnvironment deriving (Show, Eq, Ord)


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


------------------
-- More Useful Stuff
----------------

mustOr :: String -> Maybe a -> a
mustOr err Nothing = error err
mustOr _ (Just x) = x



-----------------
-- Printing stuff
-----------------

-- Context that stores the pretty printer Doc + data + help with, for example, names.
type Context = Reader CtxData (Doc ())  -- I guess I can add syntax coloring or something with the annotation (the () in Doc)
data CtxData = CtxData  -- basically stuff like printing options or something (eg. don't print types)
  { silent :: Bool
  , printIdentifiers :: Bool
  , displayTypeParameters :: Bool
  }

ctxPrint :: MonadIO io => (a -> Context) -> a -> io ()
ctxPrint f x = unless defaultContext.silent $ liftIO $ putStrLn $ ctx f x

ctxPrint' :: MonadIO io => String -> io ()
ctxPrint' = unless defaultContext.silent . liftIO . putStrLn

ctxPrint'' :: MonadIO io => Context -> io ()
ctxPrint'' = unless defaultContext.silent . liftIO . putStrLn . ctx id

phase :: String -> IO ()
phase text =
  let n = 10
  in ctxPrint' $ replicate n '=' <> " " <> map toUpper text <> " " <> replicate n '='

ctx :: (a -> Context) -> a -> String
ctx = ctx' defaultContext

sctx :: Context -> String
sctx = ctx' showContext id

ctx' :: CtxData -> (a -> Context) -> a -> String
ctx' c f = if c.silent
  then mempty
  else show . flip runReader c . f

ppBody :: Foldable t => (a -> Context) -> Context -> t a -> Context
ppBody f header = indent header . ppLines f

printf :: Text.Printf.PrintfType r => String -> r
printf = Text.Printf.printf

instance Text.Printf.PrintfArg Context where
  formatArg = Text.Printf.formatString . ctx id


-- Technically should be something like Text for the annotation type, but I need to have access to context in annotations
comment :: Context -> Context -> Context
comment s cctx = "#" <+> s <\> cctx

annotate :: [Ann] -> Context -> Context
annotate [] actx = actx
annotate xs actx = "\n" <> ppAnn xs <\> actx

encloseSepBy :: Monoid a => a -> a -> a -> [a] -> a
encloseSepBy l r p cs = l <> sepBy p cs <> r

sepBy :: Monoid a => a -> [a] -> a
sepBy p = fold . intersperse p

indent :: Context -> Context -> Context
indent header = (header <>) . fmap (PP.nest 2) . ("\n" <>)

ppLines :: Foldable t => (a -> Context) -> t a -> Context
ppLines f = foldMap ((<>"\n") . f)

ppLines' :: Foldable t => t Context -> Context
ppLines' = foldMap (<> "\n")


ppVar :: Locality -> UniqueVar -> Context
ppVar l v = localTag <?+> pretty (fromVN v.varName) <> ppIdent ("$" <> pretty (hashUnique v.varID))
  where
    localTag = case l of
      Local -> Nothing
      FromEnvironment -> Just "^"

ppUniqueClass :: UniqueClass -> Context
ppUniqueClass klass = fromString $ printf "%d@%s" (hashUnique klass.classID) (fromTN klass.className)

-- annotate constructors with '@'
ppTCon :: TCon -> Context
ppTCon = pretty . fromTC

ppMem :: MemName -> Context
ppMem = pretty . fromMN

ppCon :: UniqueCon -> Context
ppCon con = "@" <> pretty (fromCN con.conName) <> ppIdent ("$" <> pretty (hashUnique con.conID))

ppTypeInfo :: UniqueType -> Context
ppTypeInfo t = pretty (fromTC t.typeName) <> ppIdent ("$" <> pretty (hashUnique t.typeID))

ppUniqueMem :: UniqueMem -> Context
ppUniqueMem um = ppMem um.memName <> ppIdent ("#" <> pretty (hashUnique um.memID))


ppEnvID :: EnvID -> Context
ppEnvID = pretty . hashUnique . fromEnvID

ppUnionID :: UnionID -> Context
ppUnionID = pretty . hashUnique . fromUnionID

ppUnique :: Unique -> Context
ppUnique = pretty . hashUnique

ppMap :: [(Context, Context)] -> Context
ppMap = ppLines' . fmap (\(k, v) -> fromString $ printf "%s => %s" k v)

ppSet :: (a -> Context) -> [a] -> Context
ppSet f = encloseSepBy "{" "}" ", " . fmap f

ppList :: (a -> Context) -> [a] -> Context
ppList f = encloseSepBy "[" "]" ", " . fmap f


ppRecordMems :: NonEmpty (MemName, Context) -> Context
ppRecordMems = encloseSepBy "{" "}" ", " . fmap (\(mem, e) -> ppMem mem <> ":" <+> e) . NonEmpty.toList


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

ppIdent :: Context -> Context
ppIdent ident = do
  c <- ask
  if c.printIdentifiers
    then ident
    else ""

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

eitherToMaybe :: Either e a -> Maybe a
eitherToMaybe (Left _) = Nothing
eitherToMaybe (Right x) = Just x


fmap2 :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
fmap2 = fmap . fmap

traverse2 :: (Applicative f, Traversable t1, Traversable t2) => (a -> f b) -> t1 (t2 a) -> f (t1 (t2 b))
traverse2 = traverse . traverse

sequenceA2 :: (Applicative f, Traversable t1, Traversable t2) => t1 (t2 (f a)) -> f (t1 (t2 a))
sequenceA2 = traverse sequenceA

traverseSet :: (Applicative t, Ord b) => (a -> t b) -> Set a -> t (Set b)
traverseSet f = fmap Set.fromList . traverse f . Set.toList

bitraverseMap :: (Applicative t, Ord k') => (k -> t k') -> (a -> t b) -> Map k a -> t (Map k' b)
bitraverseMap f g = fmap Map.fromList . traverse (bitraverse f g) . Map.toList
