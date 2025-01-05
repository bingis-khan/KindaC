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
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad (when, unless)
import Data.Char (toUpper)


-- set printing config
defaultContext, debugContext, runtimeContext :: CtxData
defaultContext = runtimeContext 

debugContext = CtxData
  { silent = False
  , printIdentifiers = True
  , displayTypeParameters = False
  }

runtimeContext = CtxData
  { silent = True
  , printIdentifiers = False
  , displayTypeParameters = False
  }


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

-- General composition operator (easier Fix usage)
--  copied from TypeCompose package (I didn't need the whole thing, so I just copied the definition)
infixl 9 :.
newtype (g :. f) a = O (g (f a)) deriving (Eq, Ord, Functor, Foldable, Traversable)

unO :: (g :. f) a -> g (f a)
unO (O gfa) = gfa


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

-- Decorator thing.
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

data VariableType = IsFunction | IsVariable  -- used to preserve if the function is a variable or a function. TODO: this might not be needed and I might instead of the "Variable" type. Note the comment near `Env` - I'm not sure what I had in mind. When I'll start cleaning up, I'll see what it's about.

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

phase :: String -> IO ()
phase text =
  let n = 10
  in ctxPrint' $ replicate n '=' <> " " <> map toUpper text <> " " <> replicate n '='

ctx :: (a -> Context) -> a -> String
ctx = ctx' defaultContext

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

-- annotate constructors with '@'
ppTCon :: TCon -> Context
ppTCon = pretty . fromTC

ppCon :: UniqueCon -> Context
ppCon con = "@" <> pretty (fromCN con.conName) <> ppIdent ("$" <> pretty (hashUnique con.conID))

ppTypeInfo :: UniqueType -> Context
ppTypeInfo t = pretty (fromTC t.typeName) <> ppIdent ("$" <> pretty (hashUnique t.typeID))

ppEnvID :: EnvID -> Context
ppEnvID = pretty . hashUnique . fromEnvID

ppUnionID :: UnionID -> Context
ppUnionID = pretty . hashUnique . fromUnionID

ppUnique :: Unique -> Context
ppUnique = pretty . hashUnique

ppMap :: [(Context, Context)] -> Context
ppMap = ppLines' . fmap (\(k, v) -> fromString $ printf "%s => %s" k v)

ppVariableType :: VariableType -> Context
ppVariableType = \case
  IsFunction -> "[f]"
  IsVariable -> "[v]"


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
