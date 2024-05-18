{-# LANGUAGE LambdaCase, DeriveTraversable, GeneralisedNewtypeDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances, StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}

module AST where

import Data.Fix (Fix)
import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Ord.Deriving

import Data.List.NonEmpty (NonEmpty)
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Bifoldable
import Data.Text (Text)
import Data.Unique (Unique)
import Data.Functor.Foldable (Base)


-- File structure:
--  - AST datatypes
--     - Expression
--     - Statement
--     - Type
--     - Function, Datatype, Top Level
--  - Types for phases:
--     - Untyped
--     - Typechecked
--     - Monomorphic
--  - Misc. functions
--  - Instances


-- (note: everything here is declared in the order bottom-top, as type families are order dependent)


--------------------------------------
-- AST
--------------------------------------

----------------
-- Expression --
----------------

type family Expr phase

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


data ExprF t c v a
  = Lit LitType
  | Var v
  | Con c

  | Op a Op a
  | Call a [a]
  | As a t
  | Lam [v] a
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)


---------------
-- Statement --
---------------

type family Stmt phase
type family AnnStmt phase  -- For the Stmt without annotations.

data StmtF dataDef funDec c v expr a
  -- Typical statements
  = Print expr
  | Assignment v expr

  | MutDefinition v (Maybe expr)
  | MutAssignment v expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return expr

  -- Big bois
  | DataDefinition dataDef
  | FunctionDefinition funDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)

-- It's possible to annotate statements
data AnnStmtF stmt a = AnnStmt [Ann] (stmt a) deriving (Show, Eq, Ord, Functor, Foldable)
data Ann  -- or should this be a Map or something?
  = ACType Text
  | ACLit Text
  | ACStdInclude Text
  deriving (Show, Eq, Ord)
$(deriveShow1 ''AnnStmtF)


----------
-- Type --
----------

type family Type phase

newtype TVar = TV Text deriving (Show, Eq, Ord)

data TypeF t a
  = TCon t [a]
  | TVar TVar
  | TFun [a] a
  deriving (Show, Eq, Ord, Functor, Foldable)

data MonoTypeF t a
  = TType t
  | TMonoFun [a] [a]
  deriving (Show, Eq, Ord, Functor, Foldable)


$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)



--------------
-- Function --
--------------

type family FunDec phase

data GFunDec c v t = FD v [(v, t)] t deriving (Show, Functor, Eq)

-- We only take names into account when seearching for a function
-- so instances should reflect this.


--------------
-- Datatype --
--------------

type family DataCon phase
data GDataCon c t = DC c [t] [Ann] deriving (Eq, Ord, Show)

type family DataDef phase
data GDataDef tid con = DD tid [TVar] [con] deriving (Show)
-- Todo: make [TVar] into f TVar where f will change from [] to Set during resolving.
-- Unfortunately, the deriveEq instance does not seem to add an Eq1 constraint to the f parameter.
-- Might be a bug.

instance Eq tid => Eq (GDataDef tid con) where
  DD tid _ _ == DD tid' _ _ = tid == tid'

instance Ord tid => Ord (GDataDef tid con) where
  DD tid _ _ `compare` DD tid' _ _ = tid `compare` tid'


---------------
-- Module --
---------------

type family Module phase
type instance Module phase = [AnnStmt phase]  -- right now, we don't need specialised instances for Module



----------------------------------------
-- Phases
----------------------------------------

-------------
-- Untyped --
-------------
data Untyped
type instance Type Untyped = Fix (TypeF Text)
type instance Expr Untyped  = Fix (ExprF (Type Untyped) Text Text)   -- Was: Fix (ExprF Text). It's for resolving, because Resolvable needs an instance with either. Should be temporary.
                                -- I can use this https://web.archive.org/web/20070702202021/https://www.cs.vu.nl/boilerplate/. to quickly map those things.
type instance DataCon Untyped = GDataCon Text (Type Untyped)
type instance DataDef Untyped = GDataDef Text (DataCon Untyped)
type instance FunDec Untyped = GFunDec Text Text (Maybe (Type Untyped))
type instance AnnStmt Untyped = Fix (AnnStmtF (StmtF (DataDef Untyped) (FunDec Untyped) Text Text (Expr Untyped)))
type instance Stmt Untyped = StmtF (DataDef Untyped) (FunDec Untyped) Text Text (Expr Untyped) (AnnStmt Untyped)

--------------
-- Resolved --
--------------

data Resolved

type instance Type Resolved = Fix (TypeF TypeInfo)
type instance Expr Resolved = Fix (ExprF (Type Resolved) ConInfo VarInfo)
type instance AnnStmt Resolved = Fix (AnnStmtF (StmtF (DataDef Resolved) (FunDec Resolved) ConInfo VarInfo (Expr Resolved)))
type instance Stmt Resolved = StmtF (DataDef Resolved) (FunDec Resolved) ConInfo VarInfo (Expr Resolved) (AnnStmt Resolved)

type instance DataCon Resolved = GDataCon ConInfo (Type Resolved)
type instance DataDef Resolved = GDataDef TypeInfo (DataCon Resolved)
type instance FunDec Resolved = GFunDec ConInfo VarInfo (Maybe (Type Resolved))


data VarInfo = VI
  { varID :: Unique
  , varName :: Text
  , varType :: VarType
  }


data ConInfo = CI 
  { conID :: Unique
  , conName :: Text
  }

data TypeInfo = TI
  { typeID :: Unique
  , typeName :: Text
  }

data VarType = Immutable | Mutable


-- type instances for the small datatypes

instance Eq VarInfo where
  VI { varID = l } == VI { varID = r } = l == r

instance Ord VarInfo where
  VI { varID = l } `compare` VI { varID = r } = l `compare` r


instance Eq ConInfo where
  CI { conID = l } == CI { conID = r } = l == r

instance Ord ConInfo where
  CI { conID = l } `compare` CI { conID = r } = l `compare` r


instance Eq TypeInfo where
  TI { typeID = l } == TI { typeID = r } = l == r

instance Ord TypeInfo where
  TI { typeID = l } `compare` TI { typeID = r } = l `compare` r


--------------
-- Typed --  -- resolving and typechecking in one step (resolving with this grammar is pretty easy)
--------------

data Typed

type instance Type Typed = Fix (TypeF TypeInfo)
type instance Expr Typed = Fix (ExprType (Type Typed))

type instance DataCon Typed = GDataCon ConInfo (Type Typed)
type instance DataDef Typed = GDataDef TypeInfo (DataCon Typed)
type instance FunDec Typed = GFunDec ConInfo VarInfo (Type Typed)
type instance AnnStmt Typed = Fix (StmtF (DataDef Typed) (FunDec Typed) ConInfo VarInfo (Expr Typed))
type instance Stmt Typed = StmtF (DataDef Typed) (FunDec Typed) ConInfo VarInfo (Expr Typed) (AnnStmt Typed)


data ExprType t a = ExprType t (ExprF t ConInfo VarInfo a) deriving (Functor)


-- -- A bit of duplication...
-- data instance Module Typed = TModule (Set (FunDef Typed)) (Set (DataDef Typed)) [Stmt Typed] deriving Show


-- -----------------
-- -- Monomorphic --
-- -----------------
-- data Mono

-- type instance Type Mono = Fix (TypeF TypeID)
-- type instance Expr Mono = Fix (TExpr (Type Mono))
-- type instance Stmt Mono = Fix (StmtF Local Global (Expr Mono))

-- type instance FunDef Mono= GFunDef Global Local (Type Mono) (Stmt Mono)
-- type instance DataCon Mono = GDataCon Global (Type Mono)
-- type instance DataDef Mono = GDataDef Global TypeID (DataCon Mono)
-- -- This tells the compiler where to put the C data structure declaration in case of a cyclic datatype dependency.
-- -- data MonoDataDef = MonoDataDef TypeID [TypedType]

-- -- This tells the compiler where to put the function declaration in case of mutually recursive functions.
-- data FunDec = FunDec Global (Type Mono) deriving (Show, Eq, Ord)

-- -- todo: is this supposed to be FunDef Typed or Mono (is it called before or after monomorphization)
-- declaration  :: FunDef Typed -> FunDec
-- declaration (FD name params ret _) = FunDec name $ Fix (TFun (map snd params) ret)

-- data MModule = MModule [DataDef Mono] [Either FunDec (FunDef Mono)] [Stmt Mono] deriving Show


-- ---------------------------------------------
-- -- Built-in Datatypes
-- ---------------------------------------------
-- data Builtins = Builtins (Map Text (Type Typed)) (Map TypeID Text) (Map Text (Global, Type Typed)) (Map Global Text) deriving Show

-- -- they kinda suck, but they are basically required for semigroup instances
-- -- maybe I should make mempty the default?
-- -- or get the default value for builtin types?
-- -- I want the types to later be user-defined, so uhh... I dunno
-- instance Semigroup Builtins where
--   Builtins m m' m'' m''' <> Builtins n n' n'' n''' = Builtins (m <> n) (m' <> n') (m'' <> n'') (m''' <> n''')

-- instance Monoid Builtins where
--   mempty = Builtins mempty mempty mempty mempty

-- ---------------------------------------------
-- -- Misc. functions
-- ---------------------------------------------

traverseExpr :: Applicative f => (expr -> f expr') -> Base (Fix (StmtF dat (GFunDec x y z) c v expr)) stmt -> f (Base (Fix (StmtF dat (GFunDec x y z) c v expr')) stmt)
traverseExpr f = go . first f
  where
    go = \case
      Print expr -> Print <$> expr
      If cond ifTrue elifs ifFalse -> If <$> cond <*> pure ifTrue <*> traverse (\(c, b) -> (,) <$> c <*> pure b) elifs <*> pure ifFalse 
      Assignment name expr -> Assignment name <$> expr
      ExprStmt expr -> ExprStmt <$> expr
      Return expr -> Return <$> expr
      MutDefinition v mexpr -> MutDefinition v <$> sequenceA mexpr
      MutAssignment v expr -> MutAssignment v <$> expr
      DataDefinition dd -> pure $ DataDefinition dd
      FunctionDefinition def body -> pure $ FunctionDefinition def body

-- -- Not needed - hoist.
-- mapRS :: Data.Functor.Foldable.Recursive t => (Data.Functor.Foldable.Base t (Fix f) -> f (Fix f)) -> t -> Fix f
-- mapRS f = cata (Fix . f)

-- mapARS :: (Recursive t, Corecursive b, Functor f) => (Base t (f b) -> f (Base b b)) -> t -> f b
-- mapARS f = cata (fmap embed . f)

-- foldStmt :: Monoid m => (expr -> m) -> Fix (StmtF l g expr) -> m
-- foldStmt f = cata $ bifold . first f

-- ezFoldStmt :: Monoid m => (ExprF Global Local m -> m) -> Fix (StmtF l g (Fix (TExpr (Type Typed)))) -> m
-- ezFoldStmt f = foldStmt $ cata $ \case
--   TExpr _ expr -> f expr

-- -- Gets all nonlocal (global) variables.
-- usedLocals :: FunDef Typed -> Set Local
-- usedLocals (FD name params ret body) = flip foldMap body $ ezFoldStmt $ \case
--   Var (Right l) -> S.singleton l
--   s -> fold s


-- cataBoth :: (Monoid a) => (Base (Fix (ExprF g Local)) a -> a) -> (Base (Fix (StmtF Local g' a)) a  -> a) -> Fix (StmtF Local g' (Fix (ExprF g Local))) -> a
-- cataBoth e s = cata $ s . first (cata e)

-- -- Get local defs including lambdas (might be bad, but it)
-- localDefs :: (Foldable f) => f (Fix (StmtF Local g (Fix (ExprF g Local)))) -> Set Local
-- localDefs = foldMap $ cataBoth e s
--   where
--     e = \case
--       Lam params locals -> S.fromList params <> locals
--       expr -> fold expr

--     s = \case
--       Assignment l locals -> S.singleton l <> locals
--       stmt -> bifold stmt


-- dataDeclarationToType :: DataDef Typed -> Type Typed
-- dataDeclarationToType (DD t tvs _) = Fix $ TCon t $ map (Fix . TDecVar) tvs

--------------------------------------------
-- Instances 
--------------------------------------------

instance Bifunctor (StmtF dataDef funDec l g) where
  first f = \case
    Print e -> Print (f e)
    Assignment name e -> Assignment name (f e)
    MutDefinition name e -> MutDefinition name (f <$> e)
    MutAssignment name e -> MutAssignment name (f e)
    If e ifTrue elifs ifFalse -> If (f e) ifTrue ((map . first) f elifs) ifFalse
    ExprStmt e -> ExprStmt (f e)
    Return e -> Return (f e)

    DataDefinition x -> DataDefinition x
    FunctionDefinition dec body -> FunctionDefinition dec body
  second = fmap

instance Bifoldable (StmtF dataDef funDec l g) where
  bifoldr f g b = \case
    ExprStmt e -> f e b
    Print a -> f a b
    Assignment _ a -> f a b
    MutDefinition _ ma -> maybe b (\a -> f a b) ma
    MutAssignment _ a -> f a b
    Return a -> f a b
    If cond ifTrue elifs ifFalse
      -> f cond
      $ body ifTrue
      $ sfoldr (flip (bifoldr f body)) elifs   -- What the fuck?
      $ sfoldr body ifFalse b
      where
        sfoldr g' bd b' = foldr g' b' bd
        body = sfoldr g

    DataDefinition _ -> b
    FunctionDefinition _ body -> foldr g b body



$(deriveBitraversable ''StmtF)

$(deriveBifoldable ''GFunDec)
$(deriveBifunctor ''GFunDec)
$(deriveBitraversable ''GFunDec)
