{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}


{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings, OverloadedRecordDot #-}
module AST.Mono (module AST.Mono) where

import AST.Common (LitType (..), Op (..), Type, Expr, Annotated (..), TVar (..), Stmt, Ann, Module, AnnStmt, UniqueType, UniqueVar, UniqueCon, Locality (Local), Env, EnvUnion, Context, CtxData (..), ppLines, annotate, (<+>), ppVar, pretty, fromEither, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppBody, UnionID, EnvID, ppUnionID, ppEnvID)

import Text.Show.Deriving
import Data.Eq.Deriving
import Data.Ord.Deriving
import Data.Fix (Fix (..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty ((:|)))

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor)
import Data.Functor.Classes (Show1 (..), Eq1 (liftEq))
import Control.Monad.Trans.Reader (runReader)
import Data.Biapplicative (first)
import Data.Bifunctor (bimap)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')


data Mono


----------
-- Type --
----------

-- I think I'll keep the separate-but-same-structure environments until codegen, because it might be nice information to have?
-- I'll do deduplication during the codegen phase
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

$(deriveEq1 ''EnvF)
$(deriveOrd1 ''EnvF)
$(deriveShow1 ''EnvF)


data EnvUnionF t = EnvUnion
  { unionID :: UnionID
  , union :: NonEmpty (EnvF t)
  } deriving (Functor, Foldable, Traversable)
$(deriveShow1 ''EnvUnionF)

instance Show (EnvUnionF t) where
  show = undefined

instance Eq (EnvUnionF t) where
  -- special case for generated empty env function definitions
  EnvUnion { union = (Env { env = [] } :| []) } == EnvUnion { union = (Env { env = [] } :| []) } = True

  EnvUnion { unionID = l } == EnvUnion { unionID = r }  = l == r

instance Eq1 EnvUnionF where
  liftEq _ (EnvUnion { unionID = uid }) (EnvUnion { unionID = uid' }) = uid == uid'

$(deriveOrd1 ''EnvUnionF)


instance Ord (EnvUnionF t) where
  -- special case for generated empty env function definitions
  EnvUnion { union = (Env { env = [] } :| []) } `compare` EnvUnion { union = (Env { env = [] } :| []) } = EQ

  EnvUnion { unionID = l } `compare` EnvUnion { unionID = r } = l `compare` r


data TypeF a
  = TCon UniqueType                [a]  -- this last part is not needed. It's used by Mono.mapType function to "remember" which type parameters were mapped.
  | TFun (EnvUnionF a) [a] a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

$(deriveShow1 ''TypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)

type instance Type Mono = Fix TypeF
type instance Env Mono = EnvF (Type Mono)
type instance EnvUnion Mono = EnvUnionF (Type Mono)



----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality UniqueVar  -- I'll wait until transform becomes necessary...? (ie. when I experimentally observe it)
  -- Also, TODO: change UniqueVar to UniqueMonoVar (currently I'm just reusing the UniqueVar type)
  | Con UniqueCon

  | Op a Op a
  | Call a [a]
  | Lam (Env Mono) [(UniqueVar, Type Mono)] a  -- I might actually eliminate the lambda and replace it with a function call?
  deriving (Show, Eq, Functor, Foldable, Traversable)

data ExprType a = ExprType (Type Mono) (ExprF a) deriving (Show, Eq, Functor, Foldable, Traversable)


$(deriveShow1 ''ExprF)
$(deriveShow1 ''ExprType)
$(deriveEq1 ''ExprF)

type instance Expr Mono = Fix ExprType


---------------------
-- Data Definition --
---------------------

data DataCon = DC UniqueCon [Type Mono] deriving (Eq, Show)
data DataDef = DD UniqueType [Annotated DataCon] deriving (Eq, Show)


--------------
-- Function --
--------------

data FunDec = FD (Env Mono) UniqueVar [(UniqueVar, Type Mono)] (Type Mono) deriving (Show, Eq)


---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF a
  -- Typical statements
  = Print (Expr Mono)
  | Assignment UniqueVar (Expr Mono)
  | Pass

  | MutDefinition UniqueVar (Either (Type Mono) (Expr Mono))  -- additional type inserted to preserve the information we got during typechecking.
  | MutAssignment UniqueVar (Expr Mono)

  | If (Expr Mono) (NonEmpty a) [((Expr Mono), NonEmpty a)] (Maybe (NonEmpty a))
  | ExprStmt (Expr Mono)
  | Return (Expr Mono)
  deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''StmtF)

-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
data AnnotatedStmt a = AnnStmt [Ann] (StmtF a) deriving (Show, Functor, Foldable, Traversable)
$(deriveShow1 ''AnnotatedStmt)

type instance Stmt Mono = StmtF (AnnStmt Mono)
type instance AnnStmt Mono = Fix AnnotatedStmt

data Function = Fun FunDec (NonEmpty (AnnStmt Mono)) deriving (Show)


---------------
-- Module --
---------------

data Mod = Mod
  { dataTypes :: [Annotated DataDef]
  , functions :: [Annotated Function]
  , main :: [AnnStmt Mono]
  } deriving Show

type instance Module Mono = Mod




--------------------------------------------------------------------------------------

-- Printing the AST


mModule :: Module Mono -> String
mModule mod =
  let fds = comment "Datatypes" $
              sepBy "\n" $ fmap (\(Annotated anns dd) -> annotate anns (tDataDef dd)) mod.dataTypes
      fs = comment "Functions" $
              sepBy "\n" $ fmap (\(Annotated anns fd) -> annotate anns (tFunction fd)) mod.functions
      main = comment "Main" $ tStmts mod.main
  in show $ flip runReader CtxData $ sepBy "\n" [fds, fs, main]

tStmts :: [AnnStmt Mono] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt Mono -> Context
tAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ tStmt stmt

tStmt :: Stmt Mono -> Context
tStmt stmt = case stmt of
  Print e -> "print" <+> tExpr e
  Assignment v e -> ppVar Local v <+> "=" <+> tExpr e
  Pass -> "pass"
  MutDefinition v me ->  "mut" <+> ppVar Local v <+> rhs
    where
      rhs = fromEither $ bimap (\t -> "::" <+> tType t) ("<=" <+>) (fmap tExpr me)
  MutAssignment v e -> ppVar Local v <+> "<=" <+> tExpr e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> tExpr ifCond) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> tExpr cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  ExprStmt e -> tExpr e
  Return e -> "return" <+> tExpr e


tExpr :: Expr Mono -> Context
tExpr = cata $ \(ExprType t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType t <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Var l v -> ppVar l v
  Con c -> ppCon c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  Lam env params e -> tEnv env <+> sepBy " " (map (\(v, t) -> ppVar Local v <+> tType t) params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tFunction :: Function -> Context
tFunction (Fun fd body) = tBody (tFunDec fd) body

tDataDef :: DataDef -> Context
tDataDef (DD tid cons) = indent (ppTypeInfo tid) $ ppLines (\(Annotated ann dc) -> annotate ann (tConDef dc)) cons

tConDef :: DataCon -> Context
tConDef (DC g t) = foldl' (<+>) (ppCon g) $ tTypes t

tFunDec :: FunDec -> Context
tFunDec (FD env v params retType) = comment (tEnv env) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType

tTypes :: Functor t => t (Type Mono) -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ _ -> enclose t
  TFun {} -> enclose t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type Mono -> Context
tType = cata $ \case
  TCon con _ -> ppTypeInfo con
  TFun env args ret -> tEnvUnion env <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion { unionID = uid, union = us } = ppUnionID uid <> encloseSepBy "{" "}" ", " (NonEmpty.toList $ fmap tEnv' us)

tEnv :: Env Mono -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF Context -> Context
tEnv' Env { envID = eid, env = vs } = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, t) -> ppVar Local v <+> t) vs)


tBody :: Foldable f => Context -> f (AnnStmt Mono) -> Context
tBody = ppBody tAnnStmt

