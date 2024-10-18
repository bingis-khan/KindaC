{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, OverloadedStrings, OverloadedRecordDot #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
module AST.TyVared (module AST.TyVared) where

import Data.Unique (Unique, hashUnique)
import AST.Common (UniqueType, TVar (..), Type, LitType (..), Locality (..), UniqueVar, UniqueCon, Op (..), Expr, Annotated (..), Ann, AnnStmt, Stmt, Module, Env, EnvUnion, Context, ppBody, CtxData (..), ppLines, annotate, (<+>), ppVar, fromEither, pretty, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppUnique, UnionID, EnvID, ppEnvID, ppUnionID, ctx)
import Data.List.NonEmpty (NonEmpty)
import Data.Functor.Classes (Show1 (liftShowsPrec), Eq1 (liftEq))
import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.Fix (Fix (..))
import Data.Text (Text)
import Control.Monad.Trans.Reader (runReader)
import Data.Biapplicative (first, bimap)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')
import Data.List (intercalate)


data TyVared

-- Note, that a lot of instances are basically the same as Typed.
-- Right now, due to "principles", I want to ensure that TyVared and Typed ASTs are distinct.
-- In the future, however, I might make Typed just slightly more polymorphic, so I can throw out most of the code here.
--  (because I think we can just reuse TyVared IDs in Typed)


----------
-- Type --
----------

-- Env without this "superposition" - present when defining functions and lambdas.
-- do I need ID here?
-- reasons:
--  - always nice to have additional information?
data EnvF t = Env  -- right now, make Env local to "Typed" module, because the definition will change with monomorphization.
  { envID :: EnvID
  , env :: [(UniqueVar, Locality, t)]  -- t is here, because of recursion schemes.
  } deriving (Functor, Foldable, Traversable)

instance Show t => Show (EnvF t) where
  show Env { envID = envID, env = env } = show envID <> "#" <> show (fmap (\(v, locality, t) -> ctx (ppVar locality) v <> " " <> show t) env)

$(deriveShow1 ''EnvF)


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
  , union :: [EnvF t]
  } deriving (Functor, Foldable, Traversable)

instance Show t => Show (EnvUnionF t) where
  show EnvUnion { unionID = unionID, union = union } = show unionID <> "{" <> intercalate ", " (fmap show union) <> "}"

$(deriveShow1 ''EnvUnionF)

instance Eq1 EnvUnionF where
  liftEq = undefined  


instance Eq (EnvUnionF t) where
  EnvUnion { unionID = l } == EnvUnion { unionID = r }  = l == r

instance Ord (EnvUnionF t) where
  EnvUnion { unionID = l } `compare` EnvUnion { unionID = r } = l `compare` r


newtype TyVar = TyV Text deriving (Eq, Ord)

instance Show TyVar where
  show (TyV tyv) = "#" <> show tyv


data TypeF a
  = TCon UniqueType [a] [EnvUnionF a]  -- the last [EnvUnionF a] is for custom datatypes, which contain functions. what about recursive definitions?
  | TVar TVar  -- should I make a unique TVar?
  | TFun (EnvUnionF a) [a] a
  | TyVar TyVar
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)

type instance Type TyVared = Fix TypeF
type instance Env TyVared = EnvF (Type TyVared)
type instance EnvUnion TyVared = EnvUnionF (Type TyVared)

-- When we want to isolate only the data constructor.
-- MUST have the same parameters as TCon from TypeF
-- I'm not replacing the TCon parameters with this, because I don't feel like fixing all the compilation errors now.
data TypeConstructor = TypeCon UniqueType [Type TyVared] [EnvUnion TyVared] 
type2tycon :: Type TyVared -> TypeConstructor
type2tycon = undefined


----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | As a (Type TyVared)
  | Lam (EnvF (Type TyVared)) [(UniqueVar, Type TyVared)] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExprType a = ExprType (Type TyVared) (ExprF a) deriving (Show, Eq, Functor, Foldable, Traversable)


$(deriveShow1 ''ExprF)
$(deriveEq1 ''ExprF)

type instance Expr TyVared = Fix ExprType


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type TyVared] deriving (Eq, Show)
data DataDef = DD UniqueType [TVar] [EnvUnion TyVared] [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD (Env TyVared) UniqueVar [(UniqueVar, Type TyVared)] (Type TyVared) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Pass

  | MutDefinition UniqueVar (Either (Type TyVared) expr)  -- additional type inserted to preserve the information we got during typechecking.
  | MutAssignment UniqueVar expr

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt expr
  | Return expr  -- TODO: make it only an expression (this requires me to get the () constructor)

  -- Big statements
  | DataDefinition DataDef
  | FunctionDefinition FunDec (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)
$(deriveBitraversable ''StmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (StmtF (Expr TyVared) a) deriving (Functor, Foldable, Traversable)

type instance Stmt TyVared = StmtF (Expr TyVared) (AnnStmt TyVared)
type instance AnnStmt TyVared = Fix AnnotatedStmt


---------------
-- Module --
---------------

newtype Mod = Mod { fromMod :: [AnnStmt TyVared] }

type instance Module TyVared = Mod



-----------------------------------------

-- TyVared

tyModule :: Module TyVared -> String
tyModule = show . flip runReader CtxData . tStmts . fromMod

tStmts :: [AnnStmt TyVared] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt TyVared -> Context
tAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ tStmt stmt

tStmt :: Stmt TyVared -> Context
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


tExpr :: Expr TyVared -> Context
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
tDataDef (DD tid tvs _ cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (ppTypeInfo tid) tvs) $ ppLines (\(Annotated ann dc) -> annotate ann (tConDef dc)) cons

tConDef :: DataCon -> Context
tConDef (DC g t) = foldl' (<+>) (ppCon g) $ tTypes t

tFunDec :: FunDec -> Context
tFunDec (FD env v params retType) = comment (tEnv env) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType

tTypes :: Functor t => t (Type TyVared) -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon {} -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type TyVared -> Context
tType = cata $ \case
  TCon con params unions -> foldl' (<+>) (ppTypeInfo con) $ params ++ ["|"] ++ (tEnvUnion <$> unions)
  TVar (TV tv) -> pretty tv
  TFun env args ret -> tEnvUnion env <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret
  TyVar tyv -> pretty $ show tyv

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion { unionID = uid, union = us } = ppUnionID uid <> encloseSepBy "{" "}" ", " (fmap tEnv' us)

tEnv :: Env TyVared -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF Context -> Context
tEnv' Env { envID = eid, env = vs } = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc v <+> t) vs)


tBody :: Foldable f => Context -> f (AnnStmt TyVared) -> Context
tBody = ppBody tAnnStmt
