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
import Data.Set (Set, (\\))
import Data.Functor.Classes (Eq1)
import Data.Bimap (Bimap)
import Data.Unique (Unique, hashUnique)
import qualified Data.Set as S
import Data.Semigroup (sconcat)
import Data.Foldable (fold)
import Data.Map (Map)
import Data.Text (Text)


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

data ExprF g l a
  = Lit LitType
  | Var (Either g l)
  | Op a Op a
  | Call a [a]
  | Lam [l] a
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type Expr l g = Fix (ExprF g l)



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

newtype TVar = TV Text deriving (Show, Eq, Ord)

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

data DataCon g t = DC g [t] deriving (Eq, Ord, Show)
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

type UntypedType = Type Text

type UExpr = Expr Text Text   -- Was: Fix (ExprF Text). It's for resolving, because Resolvable needs an instance with either. Should be temporary.
                                  -- I can use this https://web.archive.org/web/20070702202021/https://www.cs.vu.nl/boilerplate/. to quickly map those things.
type UStmt = Stmt Text Text UExpr
type UDataCon = DataCon Text (Type Text)
type UDataDec = DataDec Text Text UDataCon
type UFunDec = FunDec Text Text (Maybe (Type Text)) UStmt



--------------
-- Resolved --
--------------
newtype Global = Global { fromGlobal :: Unique } deriving (Eq, Ord)
newtype Local = Local { fromLocal :: Unique } deriving (Eq, Ord)
newtype TypeID = TypeID { fromTypeID :: Unique } deriving (Eq, Ord)

instance Show Global where
  show (Global u) = show $ hashUnique u

instance Show Local where
  show (Local u) = show $ hashUnique u

instance Show TypeID where
  show (TypeID t) = show $ hashUnique t


type TypedType = Type TypeID


type RExpr = Expr Local Global
type RStmt = Stmt Local Global RExpr
type RDataCon = DataCon Global (Type TypeID)
type RDataDec = DataDec Global TypeID RDataCon
type RFunDec = FunDec Global Local (Maybe TypedType) RStmt

-- This will be returned from Resolver.hs.
-- Uh, not the best use case for GADTs, but I still kinda want to try it.
data RModule = RModule
  { rmFunctions  :: Set RFunDec
  , rmDataDecs  :: Set RDataDec
  , rmTLStmts   :: [RStmt]
  } deriving Show


-----------
-- Typed --
-----------
data ExprType t a
  = ExprType (Type t) (ExprF Global Local a)
  deriving (Show, Functor, Foldable)
$(deriveShow1 ''ExprType)


type TExpr = Fix (ExprType TypeID)
type TStmt = Stmt Local Global TExpr

type TFunDec = FunDec Global Local TypedType TStmt
type TDataCon = DataCon Global (Type TypeID)
type TDataDec = DataDec Global TypeID TDataCon


-- A bit of duplication...
data TModule = TModule (Set TFunDec) (Set TDataDec) [TStmt] deriving Show


-----------------
-- Monomorphic --
-----------------
-- Maybe, we should create unique type IDs and then MDataCon will be DataCon Global TypeID (TypeID is instead of (Type TypeID))
data MonoDataDec = MonoDataDec TypeID [TypedType]

-- Maybe later reflect monomorphism in type (ie. impossible to have TVars rn).
data MonoFunDec = MonoFunDec Global TypedType deriving (Show, Eq, Ord)

toMonoFunDec :: TFunDec -> MonoFunDec
toMonoFunDec (FD name params ret _) = MonoFunDec name $ Fix (TFun (map snd params) ret)

data MModule = MModule [TDataDec] [Either MonoFunDec TFunDec] [TStmt] deriving Show


---------------------------------------------
-- Built-in Datatypes
---------------------------------------------
data Builtins = Builtins (Map Text TypedType) (Map TypeID Text) (Map Text (Global, TypedType)) (Map Global Text) deriving Show

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

foldStmt :: Monoid m => (expr -> m) -> Stmt l g expr -> m
foldStmt f = cata $ bifold . first f

ezFoldStmt :: Monoid m => (ExprF Global Local m -> m) -> Stmt l g (Fix (ExprType t)) -> m
ezFoldStmt f = foldStmt $ cata $ \case
  ExprType _ expr -> f expr

-- Gets all nonlocal (global) variables.
usedLocals :: TFunDec -> Set Local
usedLocals (FD name params ret body) = flip foldMap body $ ezFoldStmt $ \case
  Var (Right l) -> S.singleton l
  s -> fold s


cataBoth :: (Monoid a) => (Base (Expr Local g) a -> a) -> (Base (Stmt Local g' a) a  -> a) -> Stmt Local g' (Expr Local g) -> a
cataBoth e s = cata $ s . first (cata e)

-- Get local defs including lambdas (might be bad, but it works)
localDefs :: (Foldable f) => f (Stmt Local g (Expr Local g)) -> Set Local
localDefs = foldMap $ cataBoth e s
  where
    e = \case
      Lam params locals -> S.fromList params <> locals
      expr -> fold expr

    s = \case
      Assignment l locals -> S.singleton l <> locals
      stmt -> bifold stmt


dataDeclarationToType :: DataDec Global TypeID datacon -> TypedType
dataDeclarationToType (DD t tvs _) = Fix $ TCon t $ map (Fix . TDecVar) tvs

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
