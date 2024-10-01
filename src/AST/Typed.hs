{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module AST.Typed (module AST.Typed) where

import AST.Common (LitType (..), Op (..), Type, Expr, Annotated (..), TVar (..), Stmt, Ann, Module, AnnStmt, UniqueType, UniqueVar, UniqueCon, Locality (Local), VarName, Env, EnvUnion, Context, CtxData (..), ppLines, annotate, (<+>), ppVar, (<+?>), pretty, fromEither, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppBody, ppUnique, UnionID, EnvID, ppUnionID, ppEnvID)

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Fix (Fix (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor)
import Data.Unique (Unique, hashUnique)
import Data.Functor.Classes (Show1 (..), Eq1 (liftEq))
import Control.Monad.Trans.Reader (runReader)
import Data.Biapplicative (first)
import Data.Bifunctor (bimap)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')


data Typed


----------
-- Type --
----------

-- Env without this "superposition" - present when defining functions and lambdas.
-- do I need ID here?
-- reasons:
--  - always nice to have additional information?
data EnvF t = Env
  { envID :: EnvID
  , env :: [(UniqueVar, t)]  -- t is here, because of recursion schemes.
  } deriving (Functor, Foldable, Traversable)

instance Show t => Show (EnvF t) where
  show (Env { envID = envID, env = env }) = "$" <> show envID <> "(" <> show env <> ")"

instance Eq (EnvF t) where
  Env { envID = l } == Env { envID = r }  = l == r

instance Ord (EnvF t) where
  Env { envID = l } `compare` Env { envID = r } = l `compare` r

-- The Env "superposition".
-- do I need the ID here?
-- reasons:
--  - always nice to have additional information?
data EnvUnionF t = EnvUnion
  { unionID :: UnionID
  , union :: [EnvF t]  -- List can be empty for types written by the programmer (which also don't have any other function's environment yet). This is okay, because functions are not yet monomorphised.
  } deriving (Functor, Foldable, Traversable)

instance Show (EnvUnionF t) where
  show = undefined

instance Show1 EnvUnionF where
  liftShowsPrec = undefined

instance Eq1 EnvUnionF where
  liftEq = undefined


instance Eq (EnvUnionF t) where
  EnvUnion { unionID = l } == EnvUnion { unionID = r }  = l == r

instance Ord (EnvUnionF t) where
  EnvUnion { unionID = l } `compare` EnvUnion { unionID = r } = l `compare` r


data TypeF a
  = TCon UniqueType [a]
  | TVar TVar  -- should I make a unique TVar?
  | TFun (EnvUnionF a) [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type Typed = Fix TypeF
type instance Env Typed = EnvF (Type Typed)
type instance EnvUnion Typed = EnvUnionF (Type Typed)



----------------
-- Expression --
----------------

-- newtype Env = Env [UniqueVar] deriving (Show, Eq, Ord)

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | As a (Type Typed)
  | Lam (Env Typed) [(UniqueVar, Type Typed)] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExprType a = ExprType (Type Typed) (ExprF a) deriving (Show, Eq, Functor, Foldable, Traversable)


$(deriveShow1 ''ExprF)
$(deriveShow1 ''ExprType)
$(deriveEq1 ''ExprF)

type instance Expr Typed = Fix ExprType


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type Typed] deriving (Eq, Show)
data DataDef = DD UniqueType [TVar] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD (Env Typed) UniqueVar [(UniqueVar, Type Typed)] (Type Typed) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Either (Type Typed) expr)  -- additional type inserted to preserve the information we got during typechecking.
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return expr

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)

$(deriveShow1 ''StmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (StmtF (Expr Typed) a) deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''AnnotatedStmt)

type instance Stmt Typed = StmtF (Expr Typed) (AnnStmt Typed)
type instance AnnStmt Typed = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod { fromMod :: [AnnStmt Typed] } deriving Show

type instance Module Typed = Mod




--------------------------------------------------------------------------------------

-- Printing the AST


tModule :: Module Typed -> String
tModule = show . flip runReader CtxData . tStmts . fromMod

tStmts :: [AnnStmt Typed] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt Typed -> Context
tAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ tStmt stmt

tStmt :: Stmt Typed -> Context
tStmt stmt = case first tExpr stmt of
  Print e -> "print" <+> e
  Assignment v e -> ppVar Local v <+> "=" <+> e
  Pass -> "pass"
  MutDefinition v me ->  "mut" <+> ppVar Local v <+> rhs
    where
      rhs = fromEither $ bimap (\t -> "::" <+> tType t) ("<=" <+>) me
  MutAssignment v e -> ppVar Local v <+> "<=" <+> e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> ifCond ) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  ExprStmt e -> e
  Return e -> "return" <+> e

  DataDefinition dd -> tDataDef dd
  FunctionDefinition fd body -> tBody (tFunDec fd) body


tExpr :: Expr Typed -> Context
tExpr = cata $ \(ExprType t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType t <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Var l v -> ppVar l v
  Con c -> ppCon c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x at -> x <+> "as" <+> tType at
  Lam env params e -> tEnv env <+> sepBy " " (map (\(v, t) -> ppVar Local v <+> tType t) params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tDataDef :: DataDef -> Context
tDataDef (DD tid tvs cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (ppTypeInfo tid) tvs) $ ppLines (\(Annotated ann dc) -> annotate ann (tConDef dc)) cons

tConDef :: DataCon -> Context
tConDef (DC g t) = foldl' (<+>) (ppCon g) $ tTypes t

tFunDec :: FunDec -> Context
tFunDec (FD env v params retType) = comment (tEnv env) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType

tTypes :: Functor t => t (Type Typed) -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type Typed -> Context
tType = cata $ \case
  TCon con params -> foldl' (<+>) (ppTypeInfo con) params
  TVar (TV tv) -> pretty tv
  TFun env args ret -> tEnvUnion env <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion { unionID = uid, union = us } = ppUnionID uid <> encloseSepBy "{" "}" ", " (fmap tEnv' us)

tEnv :: Env Typed -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF Context -> Context
tEnv' Env { envID = eid, env = vs } = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, t) -> ppVar Local v <+> t) vs)


tBody :: Foldable f => Context -> f (AnnStmt Typed) -> Context
tBody = ppBody tAnnStmt
