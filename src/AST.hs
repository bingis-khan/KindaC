{-# LANGUAGE LambdaCase, DeriveTraversable, GeneralisedNewtypeDeriving, TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}

module AST where

import Data.Fix (Fix(Fix))
import Data.Functor.Foldable (cata, Recursive(project), Base, embed, Corecursive, cataA)
import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Ord.Deriving

import Data.List.NonEmpty (NonEmpty)
import Data.Bitraversable (Bitraversable)
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Functor ((<&>))
import Data.Coerce (coerce)
import qualified Data.Map as M
import Data.Set (Set)
import Data.Functor.Classes (Eq1)
import Data.Bimap (Bimap)


-- File structure:
--  - AST datatypes
--     - Expression
--     - Statement
--     - Type
--     - Function, Datatype, Top Level
--  - Types for phases:
--     - Untyped
--     - Resolved
--     - Typechecked
--     - Monomorphic
--  - Misc. functions
--  - Instances


--------------------------------------
-- AST
--------------------------------------

----------------
-- Expression --
----------------

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
  | LBool Bool
  deriving (Eq, Ord, Show)

data ExprF i a
  = Lit LitType
  | Var i
  | Op a Op a
  | Call a [a]
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type Expr l g = Fix (ExprF (Either g l))



---------------
-- Statement --
---------------

data StmtF l g expr a
  = Print expr
  | Assignment l expr
  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return expr
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)
$(deriveEq1 ''StmtF)

type Stmt l g expr = Fix (StmtF l g expr)



----------
-- Type --
----------

newtype TVar = TV String deriving (Show, Eq, Ord)

data TypeF t a
  = TCon t [a]
  | TVar TVar
  | TDecVar TVar  -- This is declared TVar, which ignores normal inference and essentially acts as another type.
  | TFun [a] a
  deriving (Show, Eq, Ord, Functor, Foldable)
type Type t = Fix (TypeF t)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)



--------------
-- Function --
--------------

data FunDec g l t stmt = FD g [(l, t)] t (NonEmpty stmt) deriving (Show, Functor)

-- We only take names into account when seearching for a function
-- so instances should reflect this.
instance Eq g => Eq (FunDec g l tid stmt) where
  FD name _ _ _ == FD name' _ _ _ = name == name'

instance Ord g => Ord (FunDec g l tid stmt) where
  FD name _ _ _ `compare` FD name' _ _ _ = name `compare` name'


--------------
-- Datatype --
--------------

data DataCon g tid = DC g [Type tid] deriving (Eq, Ord, Show)
data DataDec g tid con = DD tid [TVar] (NonEmpty con) deriving (Show)
-- Todo: make [TVar] into f TVar where f will change from [] to Set during resolving.
-- Unfortunately, the deriveEq instance does not seem to add an Eq1 constraint to the f parameter.
-- Might be a bug.

instance Eq tid => Eq (DataDec g tid con) where
  DD tid _ _ == DD tid' _ _ = tid == tid'

instance Ord tid => Ord (DataDec g tid con) where
  DD tid _ _ `compare` DD tid' _ _ = tid `compare` tid'


---------------
-- Top Level --
---------------

data TopLevel
  = FunDec UFunDec
  | DataDec UDataDec
  | TLStmt UStmt
  deriving Show



----------------------------------------
-- Phases
----------------------------------------

-------------
-- Untyped --
-------------

type UntypedType = Type String

type UExpr = Expr String String   -- Was: Fix (ExprF String). It's for resolving, because Resolvable needs an instance with either. Should be temporary.
                                  -- I can use this https://web.archive.org/web/20070702202021/https://www.cs.vu.nl/boilerplate/. to quickly map those things.
type UStmt = Stmt String String UExpr
type UDataCon = DataCon String String
type UDataDec = DataDec String String UDataCon
type UFunDec = FunDec String String (Maybe (Type String)) UStmt



--------------
-- Resolved --
--------------
newtype Global = Global { fromGlobal :: Int } deriving (Show, Eq, Ord, Enum)
newtype Local = Local { fromLocal :: Int } deriving (Show, Eq, Ord, Enum)
newtype TypeID = TypeID Int deriving (Show, Eq, Ord, Enum)


type TypedType = Type TypeID

intType, boolType :: TypedType
intType = Fix (TCon (TypeID 0) [])
boolType = Fix (TCon (TypeID 1) [])


type RExpr = Expr Local Global
type RStmt = Stmt Local Global RExpr
type RDataCon = DataCon Global TypeID
type RDataDec = DataDec Global TypeID RDataCon
type RFunDec = FunDec Global Local (Maybe TypedType) RStmt

-- This will be returned from Resolver.hs.
-- Uh, not the best use case for GADTs, but I still kinda want to try it.
data RModule = RModule
  { rmFunctions  :: (Set RFunDec)
  , rmDataDecs  :: (Set RDataDec)
  , rmTLStmts   :: [RStmt]
  , rmTLLocaLGlobals :: (Bimap Local Global)
  } deriving Show


-----------
-- Typed --
-----------
data ExprType t a
  = ExprType (Type t) (ExprF (Either Global Local) a)
  deriving (Show, Functor, Foldable)
$(deriveShow1 ''ExprType)


type TExpr = Fix (ExprType TypeID)
type TStmt = Stmt Local Global TExpr

type TFunDec = FunDec Global Local TypedType TStmt
type TDataCon = DataCon Global TypeID
type TDataDec = DataDec Global TypeID TDataCon


-- A bit of duplication...
data TModule = TModule (Set TFunDec) (Set TDataDec) [TStmt] deriving Show

---------------------------------------------
-- Built-in Datatypes
---------------------------------------------

builtIns :: M.Map TypeID String
builtIns = M.fromList $ zip (coerce [(0 :: Int) ..] :: [TypeID])
  [ "Int"
  , "Bool"
  ]

firstTypeID :: TypeID
firstTypeID = maximum $ M.keys builtIns



---------------------------------------------
-- Misc. functions
---------------------------------------------

bindExpr :: Applicative f => (expr -> f expr') -> Base (Stmt l g expr) stmt -> f (Base (Stmt l g expr') stmt)
bindExpr f (Print expr) = Print <$> f expr
bindExpr f (If cond ifTrue elifs ifFalse) = If <$> f cond <*> pure ifTrue <*> traverse (\(c, b) -> (,) <$> f c <*> pure b) elifs <*> pure ifFalse
bindExpr f (Assignment name expr) = Assignment name <$> f expr
bindExpr f (ExprStmt expr) = ExprStmt <$> f expr
bindExpr f (Return expr) = Return <$> f expr

-- Not needed - hoist.
mapRS :: Data.Functor.Foldable.Recursive t => (Data.Functor.Foldable.Base t (Fix f) -> f (Fix f)) -> t -> Fix f
mapRS f = cata (Fix . f)

mapARS :: (Recursive t, Corecursive b, Functor f) => (Base t (f b) -> f (Base b b)) -> t -> f b
mapARS f = cata (fmap embed . f)



--------------------------------------------
-- Instances 
--------------------------------------------

instance Bifunctor (StmtF l g) where
  first f = \case
    Print e -> Print (f e)
    Assignment name e -> Assignment name (f e)
    If e ifTrue elifs ifFalse -> If (f e) ifTrue ((map . first) f elifs) ifFalse
    ExprStmt e -> ExprStmt (f e)
    Return e -> Return (f e)
  second = fmap

instance Bifoldable (StmtF l g) where
  bifoldr f g b = \case
    ExprStmt e -> f e b
    Print a -> f a b
    Assignment l a -> f a b
    Return a -> f a b
    If cond ifTrue elifs ifFalse
      -> f cond
      $ body ifTrue
      $ sfoldr (flip (bifoldr f body)) elifs   -- What the fuck?
      $ sfoldr body ifFalse b
      where
        sfoldr g bd b = foldr g b bd
        body = sfoldr g



$(deriveBitraversable ''StmtF)

$(deriveBifoldable ''FunDec)
$(deriveBifunctor ''FunDec)
$(deriveBitraversable ''FunDec)
