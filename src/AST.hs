{-# LANGUAGE LambdaCase, DeriveTraversable, GeneralisedNewtypeDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances, StandaloneDeriving, DuplicateRecordFields #-}
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
import Data.Unique (Unique, hashUnique)
import qualified Data.Text as Text
import Data.Set (Set)




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
  deriving (Eq, Ord, Show)

data Locality
  = Local
  | FromEnvironment
  deriving (Eq, Ord, Show)

data ExprF l fenv t c v a
  = Lit LitType
  | Var l v
  | Con c

  | Op a Op a
  | Call a [a]
  | As a t
  | Lam (fenv v t) [v] a
  deriving (Show, Eq, Functor, Foldable, Traversable)


---------------
-- Statement --
---------------

type family Stmt phase
type family AnnStmt phase  -- For the Stmt without annotations.

data StmtF c v expr a
  -- Typical statements
  = Print expr
  | Assignment v expr
  | Pass

  | MutDefinition v (Maybe expr)
  | MutAssignment v expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return (Maybe expr)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)

data BigStmtF datadef fundec stmt a
  = DataDefinition datadef
  | FunctionDefinition fundec (NonEmpty a)
  | NormalStmt (stmt a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveShow1 ''BigStmtF)

-- It's possible to annotate statements
data Annotated a = Annotated [Ann] a deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
data AnnStmtF stmt a = AnnStmt [Ann] (stmt a) deriving (Show, Eq, Ord, Functor, Foldable, Traversable)  -- so Fix would work

data Ann  -- or should this be a Map or something?
  = ACType Text
  | ACLit Text
  | ACStdInclude Text
  deriving (Show, Eq, Ord)
$(deriveShow1 ''Annotated)
$(deriveShow1 ''AnnStmtF)


----------
-- Type --
----------

type family Type phase

newtype TVar = TV Text deriving (Show, Eq, Ord)

-- Environment for functions
data TypeF fenv t a
  = TCon t [a]
  | TVar TVar
  | TFun (fenv a) [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)



$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)


--------------
-- Function --
--------------

type family FunDec phase

data GFunDec fenv c v t = FD v [(v, t)] (fenv v t) t deriving (Show, Functor, Eq)


-- We only take names into account when searching for a function
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



----------------------------------------
-- Phases
----------------------------------------

-------------
-- Untyped --
-------------
data Untyped

newtype NoEnv v t = NoEnv () deriving (Functor)
newtype TNoEnv t = TNoEnv () deriving Functor
instance Show (NoEnv v t) where
  show (NoEnv ()) = "<env ph>"

instance Show (TNoEnv t) where
  show (TNoEnv ()) = "<tenv ph>"

$(deriveShow1 ''NoEnv)
$(deriveShow1 ''TNoEnv)


type instance Type Untyped = Fix (TypeF TNoEnv Text)
type instance Expr Untyped  = Fix (ExprF () NoEnv (Type Untyped) Text Text)   -- Was: Fix (ExprF Text). It's for resolving, because Resolvable needs an instance with either. Should be temporary.
                                -- I can use this https://web.archive.org/web/20070702202021/https://www.cs.vu.nl/boilerplate/. to quickly map those things.
type instance DataCon Untyped = GDataCon Text (Type Untyped)
type instance DataDef Untyped = GDataDef Text (DataCon Untyped)
type instance FunDec Untyped = GFunDec NoEnv Text Text (Maybe (Type Untyped))
type instance AnnStmt Untyped = Fix (AnnStmtF (BigStmtF (DataDef Untyped) (FunDec Untyped) (StmtF Text Text (Expr Untyped))))
type instance Stmt Untyped = BigStmtF (DataDef Untyped) (FunDec Untyped) (StmtF Text Text (Expr Untyped)) (AnnStmt Untyped)

type instance Module Untyped = [AnnStmt Untyped]

--------------
-- Resolved --
--------------

data Resolved


type instance Type Resolved = Fix (TypeF TNoEnv TypeInfo)

newtype VarEnv v t = VarEnv [v] deriving Functor  -- actually, the type is supposed to be 'Set', but this requires an Ord instance in functor.
type instance Expr Resolved = Fix (ExprF Locality VarEnv (Type Resolved) ConInfo VarInfo)
type instance AnnStmt Resolved = Fix (AnnStmtF (BigStmtF (DataDef Resolved) (FunDec Resolved) (StmtF ConInfo VarInfo (Expr Resolved))))
type instance Stmt Resolved = BigStmtF (DataDef Resolved) (FunDec Resolved) (StmtF ConInfo VarInfo (Expr Resolved)) (AnnStmt Resolved)

type instance DataCon Resolved = GDataCon ConInfo (Type Resolved)
type instance DataDef Resolved = GDataDef TypeInfo (DataCon Resolved)
type instance FunDec Resolved = GFunDec VarEnv ConInfo VarInfo (Maybe (Type Resolved))


type instance Module Resolved = [AnnStmt Resolved]


data VarInfo = VI
  { varID :: Unique
  , varName :: Text
  , varType :: VarType
  }


data ConInfo = CI
  { conID :: Unique
  , conName :: Text
  -- add info about constructor for later compilation
  }

data TypeInfo = TI
  { typeID :: Unique
  , typeName :: Text
  -- add info about structure for later compilation
  }

data VarType = Immutable | Mutable deriving Show


-- type instances for the small datatypes

instance Eq VarInfo where
  VI { varID = l } == VI { varID = r } = l == r

instance Ord VarInfo where
  VI { varID = l } `compare` VI { varID = r } = l `compare` r

-- temporary instance
instance Show VarInfo where
  show (VI { varID = vid, varName = vname, varType = vt }) = "v" <> show (hashUnique vid) <> Text.unpack vname <> show vt


instance Eq ConInfo where
  CI { conID = l } == CI { conID = r } = l == r

instance Ord ConInfo where
  CI { conID = l } `compare` CI { conID = r } = l `compare` r


instance Show TypeInfo where
  show (TI { typeID = tid, typeName = name }) = show name <> "@" <> show (hashUnique tid)

instance Eq TypeInfo where
  TI { typeID = l } == TI { typeID = r } = l == r

instance Ord TypeInfo where
  TI { typeID = l } `compare` TI { typeID = r } = l `compare` r


--------------
--  Typed   --
--------------

data Typed

data EnvInfo = EI
  { envID :: Unique
  }

instance Show EnvInfo where
  show (EI { envID = tid }) = "%" <> show (hashUnique tid)

instance Eq EnvInfo where
  EI { envID = l } == EI { envID = r } = l == r

instance Ord EnvInfo where
  EI { envID = l } `compare` EI { envID = r } = l `compare` r


data FunEnv t = FunEnv EnvInfo [[(VarInfo, [t])]] deriving (Show, Eq, Ord, Functor, Foldable, Traversable)  -- TODO: This is a spiritual 'Set'. fmap does not let me add the 'Ord' constraint. Also, shitty types ong. TODO: this needs a serious refactor. but i'm kinda exploring rn
$(deriveShow1 ''FunEnv)
$(deriveEq1 ''FunEnv)
$(deriveOrd1 ''FunEnv)

type instance Type Typed = Fix (TypeF FunEnv TypeInfo)
type instance Expr Typed = Fix (ExprType Locality VarInfo ConInfo (Type Typed) (Type Typed))

type instance DataCon Typed = GDataCon ConInfo (Type Typed)
type instance DataDef Typed = GDataDef TypeInfo (DataCon Typed)

newtype TypedEnv v t = TypedEnv [(v, [t])] deriving (Functor, Foldable, Traversable)

type instance FunDec Typed = GFunDec TypedEnv ConInfo VarInfo (Type Typed)
type instance AnnStmt Typed = Fix (AnnStmtF (BigStmtF (DataDef Typed) (FunDec Typed) (StmtF ConInfo VarInfo (Expr Typed))))
type instance Stmt Typed = BigStmtF (DataDef Typed) (FunDec Typed) (StmtF ConInfo VarInfo (Expr Typed)) (AnnStmt Typed)


data ExprType l v c t texpr a = ExprType t (ExprF l TypedEnv texpr c v a) deriving (Functor)

type instance Module Typed = [AnnStmt Typed]


$(deriveBifoldable ''TypedEnv)
$(deriveBifunctor ''TypedEnv)
$(deriveBitraversable ''TypedEnv)


-----------------
-- Monomorphic --
-----------------
data Mono

data MonoVarInfo = MVI
  { varID :: Unique
  , varName :: Text
  -- , varType :: VarType
  }

data MonoEnvInfo = MEI
  { envID :: Unique
  }


data MonoConInfo = MCI
  { conID :: Unique
  , conName :: Text
  -- add info about constructor for later compilation
  }

data MonoTypeInfo = MTI
  { typeID :: Unique
  , typeName :: Text
  -- add info about structure for later compilation
  }


instance Eq MonoVarInfo where
  MVI { varID = l } == MVI { varID = r } = l == r

instance Ord MonoVarInfo where
  MVI { varID = l } `compare` MVI { varID = r } = l `compare` r

-- temporary instance
instance Show MonoVarInfo where
  show (MVI { varID = vid, varName = vname }) = "v" <> show (hashUnique vid) <> Text.unpack vname


instance Eq MonoConInfo where
  MCI { conID = l } == MCI { conID = r } = l == r

instance Ord MonoConInfo where
  MCI { conID = l } `compare` MCI { conID = r } = l `compare` r


instance Show MonoTypeInfo where
  show (MTI { typeID = tid, typeName = name }) = show name <> "@" <> show (hashUnique tid)

instance Eq MonoTypeInfo where
  MTI { typeID = l } == MTI { typeID = r } = l == r

instance Ord MonoTypeInfo where
  MTI { typeID = l } `compare` MTI { typeID = r } = l `compare` r


newtype Env a = Env (NonEmpty [a]) deriving (Show, Eq, Ord, Functor, Foldable)  -- this isn't supposed to be an ID - if Envs match, they are the same - equality implies... sameness.o
$(deriveEq1 ''Env)
$(deriveOrd1 ''Env)

newtype MonoEnvEnv v t = MonoEnv [(v, t)] deriving (Functor, Foldable)  -- can MonoEnv be empty actually? I thought we kind of check for it during monomorphization.
$(deriveBifunctor ''MonoEnvEnv)
type MonoEnv = MonoEnvEnv (Locality, MonoVarInfo) (Maybe MonoEnvInfo, Type Mono)


data MonoTypeF a
  = MTCon MonoTypeInfo -- change TypeInfo to something like MonoTypeInfo, which would encode transitions and such.
  | MTFun (Env a) [a] a
  deriving (Show, Eq, Ord, Functor, Foldable)
$(deriveEq1 ''MonoTypeF)
$(deriveOrd1 ''MonoTypeF)

data MonoEnvStmt stmt a
  = NormalMonoStmt (stmt a)
  | EnvStmt MonoEnvInfo MonoEnv  -- disgusting
  deriving (Functor)

data EnvTransform
  = NoEnvs  -- no environment literally
  | Unchanged  -- it's in the previous variable (ie: f = id; g = f) - in g = f, it should be Unchanged.
  | SameEnv MonoEnvInfo MonoEnv  -- when instantiating, same env, no operations should be performed.
  | EnvTransform MonoEnvInfo MonoEnv (Env (Type Mono))  -- when env differs at callsite. FunEnv should also include locality i think.

type instance Type Mono = Fix MonoTypeF
type instance Expr Mono = Fix (ExprType (Locality, EnvTransform) MonoVarInfo MonoConInfo (Type Mono) (Type Mono))

type instance DataCon Mono = GDataCon MonoConInfo (Type Mono)
type instance DataDef Mono = GDataDef MonoTypeInfo (DataCon Mono)
type instance FunDec Mono = GFunDec MonoEnvEnv MonoConInfo MonoVarInfo (Type Mono)
type instance AnnStmt Mono = Fix (AnnStmtF (MonoEnvStmt (StmtF MonoConInfo MonoVarInfo (Expr Mono))))
type instance Stmt Mono = MonoEnvStmt (StmtF MonoConInfo MonoVarInfo (Expr Mono)) (AnnStmt Mono)

-- -- todo: is this supposed to be FunDef Typed or Mono (is it called before or after monomorphization)
-- declaration  :: FunDef Typed -> FunDec
-- declaration (FD name params ret _) = FunDec name $ Fix (TFun (map snd params) ret)

-- data MModule = MModule [DataDef Mono] [Either FunDec (FunDef Mono)] [Stmt Mono] deriving Show


data MonoModule = MonoModule
  { functions :: [Annotated (FunDec Mono, NonEmpty (AnnStmt Mono))]
  , dataTypes :: [Annotated (DataDef Mono)]
  , main :: [AnnStmt Mono]
  }

type instance Module Mono = MonoModule


-------------
-- PRELUDE --
-------------

type Prelude = Module Typed


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

-- traverseExpr :: Applicative f => (expr -> f expr') -> Base (Fix (StmtF dat (GFunDec x y z) c v expr)) stmt -> f (Base (Fix (StmtF dat (GFunDec x y z) c v expr')) stmt)
-- traverseExpr f = go . first f
--   where
--     go = \case
--       Print expr -> Print <$> expr
--       If cond ifTrue elifs ifFalse -> If <$> cond <*> pure ifTrue <*> traverse (\(c, b) -> (,) <$> c <*> pure b) elifs <*> pure ifFalse 
--       Pass -> pure Pass
--       Assignment name expr -> Assignment name <$> expr
--       ExprStmt expr -> ExprStmt <$> expr
--       Return expr -> Return <$> expr
--       MutDefinition v mexpr -> MutDefinition v <$> sequenceA mexpr
--       MutAssignment v expr -> MutAssignment v <$> expr
--       DataDefinition dd -> pure $ DataDefinition dd
--       FunctionDefinition def body -> pure $ FunctionDefinition def body

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
-- Instances and additional mapping functions
--------------------------------------------

instance Bifunctor (StmtF l g) where
  first f = \case
    Print e -> Print (f e)
    Assignment name e -> Assignment name (f e)
    Pass -> Pass
    MutDefinition name e -> MutDefinition name (f <$> e)
    MutAssignment name e -> MutAssignment name (f e)
    If e ifTrue elifs ifFalse -> If (f e) ifTrue ((map . first) f elifs) ifFalse
    ExprStmt e -> ExprStmt (f e)
    Return e -> Return (fmap f e)
  second = fmap

instance Bifoldable (StmtF l g) where
  bifoldr f g b = \case
    ExprStmt e -> f e b
    Print a -> f a b
    Pass -> b
    Assignment _ a -> f a b
    MutDefinition _ ma -> maybe b (\a -> f a b) ma
    MutAssignment _ a -> f a b
    Return ma -> maybe b (\a -> f a b) ma
    If cond ifTrue elifs ifFalse
      -> f cond
      $ body ifTrue
      $ sfoldr (flip (bifoldr f body)) elifs   -- What the fuck?
      $ sfoldr body ifFalse b
      where
        sfoldr g' bd b' = foldr g' b' bd
        body = sfoldr g


$(deriveBitraversable ''StmtF)

$(deriveBifoldable ''GFunDec)
$(deriveBifunctor ''GFunDec)
$(deriveBitraversable ''GFunDec)


-- sad function for switching environment
mapInnerExprType :: Functor (fenv v) => (t -> t') -> ExprF l fenv t c v a -> ExprF l fenv t' c v a
mapInnerExprType f = \case
  -- real one
  As e t -> As e (f t)

  -- grunt work
  Lit lt -> Lit lt
  Var l v -> Var l v
  Con c -> Con c
  Op l op r -> Op l op r
  Call e args -> Call e args
  Lam env v e -> Lam (fmap f env) v e

mapTypeEnv :: (fenv a -> genv a) -> TypeF fenv t a -> TypeF genv t a
mapTypeEnv f = \case
  TCon t ts -> TCon t ts
  TVar tv -> TVar tv
  TFun fenv ts r -> TFun (f fenv) ts r

