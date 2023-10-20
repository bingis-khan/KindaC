{-# LANGUAGE LambdaCase, DeriveTraversable, GeneralisedNewtypeDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances, StandaloneDeriving #-}

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


data ExprF t g l a
  = Lit LitType
  | Var (Either g l)
  | Op a Op a
  | Call a [a]
  | As a t
  | Lam [l] a
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type family Expr phase

---------------
-- Statement --
---------------

data StmtF dataDef funDec l g expr a
  -- Typical statements
  = Print expr
  | Assignment l expr
  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return expr

  -- Big bois
  | DataDefinition dataDef
  | FunctionDefinition funDec (NonEmpty a)
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)
$(deriveEq1 ''StmtF)

type family Stmt phase


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

type family Type phase

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)



--------------
-- Function --
--------------
type family FunDec phase
data GFunDec g l t = FD g [(l, t)] t deriving (Show, Functor)

-- We only take names into account when seearching for a function
-- so instances should reflect this.
instance Eq g => Eq (GFunDec g l tid)  where
  FD name _ _ == FD name' _ _ = name == name'

instance Ord g => Ord (GFunDec g l tid) where
  FD name _ _ `compare` FD name' _ _ = name `compare` name'


--------------
-- Datatype --
--------------
type family DataCon phase
data GDataCon g t = DC g [t] deriving (Eq, Ord, Show)
type family DataDef phase
data GDataDef g tid con = DD tid [TVar] [con] deriving (Show)
-- Todo: make [TVar] into f TVar where f will change from [] to Set during resolving.
-- Unfortunately, the deriveEq instance does not seem to add an Eq1 constraint to the f parameter.
-- Might be a bug.

instance Eq tid => Eq (GDataDef g tid con) where
  DD tid _ _ == DD tid' _ _ = tid == tid'

instance Ord tid => Ord (GDataDef g tid con) where
  DD tid _ _ `compare` DD tid' _ _ = tid `compare` tid'


---------------
-- Top Level --
---------------
type family TopLevel phase
type instance TopLevel phase = [Stmt phase]  -- right now, we don't need specialised instances for TopLevel



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
type instance DataDef Untyped = GDataDef Text Text (DataCon Untyped)
type instance FunDec Untyped = GFunDec Text Text (Maybe (Type Untyped))
type instance Stmt Untyped = Fix (StmtF (DataDef Untyped) (FunDec Untyped) Text Text (Expr Untyped))


-- --------------
-- -- Resolved --
-- --------------
-- data Resolved
-- newtype Global = Global { fromGlobal :: Unique } deriving (Eq, Ord)
-- newtype Local = Local { fromLocal :: Unique } deriving (Eq, Ord)
-- newtype TypeID = TypeID { fromTypeID :: Unique } deriving (Eq, Ord)

-- instance Show Global where
--   show (Global u) = show $ hashUnique u

-- instance Show Local where
--   show (Local u) = show $ hashUnique u

-- instance Show TypeID where
--   show (TypeID t) = show $ hashUnique t


-- type instance Type Resolved = Fix (TypeF TypeID)
-- type instance Expr Resolved = Fix (ExprF Local Global)
-- type instance DataCon Resolved = GDataCon Global (Type Resolved)
-- type instance DataDef Resolved = GDataDef Global TypeID (DataCon Resolved)
-- type instance FunDef Resolved = GFunDef Global Local (Maybe (Type Resolved)) (Stmt Resolved)
-- type instance Stmt Resolved = Fix (StmtF (DataDef Resolved) (FunDef Resolved) Local Global (Expr Resolved))

-- -- This will be returned from Resolver.hs.
-- -- Uh, not the best use case for GADTs, but I still kinda want to try it.
-- data family Module phase
-- data instance Module Resolved = RModule
--   { functions  :: Set (FunDef Resolved)
--   , rmDataDefs :: Set (DataDef Resolved)
--   , rmTLStmts  :: [Stmt Resolved]
--   } deriving Show


-- -----------
-- -- Typed --
-- -----------
-- data Typed

-- type instance Type Typed = Fix (TypeF TypeID)

-- data TExpr t a = TExpr t (ExprF Global Local a) deriving (Show, Functor)
-- $(deriveShow1 ''TExpr)

-- type instance Expr Typed = Fix (TExpr (Type Typed))

-- type instance FunDef Typed = GFunDef Global Local (Type Typed) (Stmt Typed)
-- type instance DataCon Typed = GDataCon Global (Type Typed)
-- type instance DataDef Typed = GDataDef Global TypeID (DataCon Typed)
-- type instance Stmt Typed = Fix (StmtF (DataDef ) Local Global (Expr Typed))



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

-- bindExpr :: Applicative f => (expr -> f expr') -> Base (Fix (StmtF l g expr)) stmt -> f (Base (Fix (StmtF l g expr')) stmt)
-- bindExpr f (Print expr) = Print <$> f expr
-- bindExpr f (If cond ifTrue elifs ifFalse) = If <$> f cond <*> pure ifTrue <*> traverse (\(c, b) -> (,) <$> f c <*> pure b) elifs <*> pure ifFalse
-- bindExpr f (Assignment name expr) = Assignment name <$> f expr
-- bindExpr f (ExprStmt expr) = ExprStmt <$> f expr
-- bindExpr f (Return expr) = Return <$> f expr

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
    Return a -> f a b
    If cond ifTrue elifs ifFalse
      -> f cond
      $ body ifTrue
      $ sfoldr (flip (bifoldr f body)) elifs   -- What the fuck?
      $ sfoldr body ifFalse b
      where
        sfoldr g bd b = foldr g b bd
        body = sfoldr g

    DataDefinition _ -> b
    FunctionDefinition _ body -> foldr g b body



$(deriveBitraversable ''StmtF)

$(deriveBifoldable ''GFunDec)
$(deriveBifunctor ''GFunDec)
$(deriveBitraversable ''GFunDec)
