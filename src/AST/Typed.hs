{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
module AST.Typed (module AST.Typed) where

import AST.Common (LitType (..), Op (..), Annotated (..), TVar (..), Ann, UniqueType, UniqueVar, UniqueCon, Locality (Local), Context, CtxData (..), ppLines, annotate, (<+>), ppVar, (<+?>), pretty, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppBody, UnionID, EnvID, ppUnionID, ppEnvID, (:.) (..), ppLines')

import Data.Eq.Deriving
import Data.Fix (Fix (..))
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor)
import Data.Functor.Classes (Eq1 (liftEq))
import Control.Monad.Trans.Reader (runReader)
import Data.Biapplicative (first)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')
import Data.Text (Text)



---------------------
-- Data Definition --
---------------------

data DataCon = DC DataDef UniqueCon [Type] [Ann]
data DataDef = DD UniqueType [TVar] [EnvUnion] [DataCon] [Ann]

instance Eq DataDef where
  DD ut _ _ _ _ == DD ut' _ _ _ _ = ut == ut'


----------
-- Type --
----------

-- Env without this "superposition" - present when defining functions and lambdas.
-- do I need ID here?
-- reasons:
--  - always nice to have additional information?
data EnvF t = Env
  { envID :: EnvID
  , env :: [(UniqueVar, Locality, t)]  -- t is here, because of recursion schemes.
  } deriving (Functor, Foldable, Traversable)
type Env = EnvF Type

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
type EnvUnion = EnvUnionF Type

instance Eq1 EnvUnionF where
  liftEq _ u u' = u.unionID == u'.unionID

instance Eq (EnvUnionF t) where
  EnvUnion { unionID = l } == EnvUnion { unionID = r }  = l == r

instance Ord (EnvUnionF t) where
  EnvUnion { unionID = l } `compare` EnvUnion { unionID = r } = l `compare` r


newtype TyVar = TyV { fromTyV :: Text } deriving (Eq, Ord)

data TypeF a
  = TCon DataDef [a] [EnvUnionF a]
  | TVar TVar  -- TODO: make it unique per function scope. Should I use UniqueVar or something else?
  | TFun (EnvUnionF a) [a] a
  | TyVar TyVar
  deriving (Eq, Functor, Foldable, Traversable)
type Type = Fix TypeF

$(deriveEq1 ''TypeF)



----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality Variable
  | Con DataCon

  | Op a Op a
  | Call a [a]
  | As a Type
  | Lam Env [(UniqueVar, Type)] a
  deriving (Functor, Foldable, Traversable)

data TypedExpr a = TypedExpr Type (ExprF a) deriving (Functor, Foldable, Traversable)
type Expr = Fix TypedExpr

data Variable
  = DefinedVariable UniqueVar
  | DefinedFunction Function

--------------
-- Function --
--------------

data FunDec = FD
  { functionEnv :: Env
  , functionId :: UniqueVar
  , functionParameters :: [(UniqueVar, Type)]
  , functionReturnType :: Type
  }

instance Eq FunDec where
  FD _ uv _ _ == FD _ uv' _ _ = uv == uv'

data Function = Function
  { functionDeclaration :: FunDec
  , functionBody :: NonEmpty AnnStmt
  }

instance Eq Function where
  Function { functionDeclaration = fd } == Function { functionDeclaration = fd' } = fd == fd'


----------
-- Case --
----------

data DeconF a
  = CaseVariable Type UniqueVar
  | CaseConstructor Type UniqueCon [a]
  deriving (Functor)
type Decon = Fix DeconF

data Case expr a = Case
  { deconstruction :: Decon
  , caseCondition :: Maybe expr
  , body :: NonEmpty a
  } deriving (Functor, Foldable, Traversable)



---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF expr a
  -- Typical statements
  = Print expr
  | Assignment UniqueVar expr
  | Mutation UniqueVar expr
  | Pass

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (Case expr a))
  | ExprStmt expr
  | Return expr
  deriving (Functor, Foldable, Traversable)


-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
type Stmt = StmtF Expr AnnStmt
type AnnStmt = Fix (Annotated :. StmtF Expr)

$(deriveBifunctor ''Case)
$(deriveBifoldable ''Case)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)


---------------
-- Module --
---------------

data Module = Mod
  { toplevelStatements :: [AnnStmt]
  
  -- probably not needed, used for printing the AST.
  , functions :: [Function]
  , datatypes :: [DataDef]
  }


--------------------------------------------------------------------------------------
-- Printing the AST

tModule :: Module -> String
tModule m = 
  show . flip runReader CtxData $ ppLines'
    [ ppLines tDataDef m.datatypes
    , ppLines tFunction m.functions
    , tStmts m.toplevelStatements
    ]

tStmts :: [AnnStmt] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt -> Context
tAnnStmt (Fix (O (Annotated ann stmt))) = annotate ann $ tStmt stmt

tStmt :: Stmt -> Context
tStmt stmt = case first tExpr stmt of
  Print e -> "print" <+> e
  Assignment v e -> ppVar Local v <+> "=" <+> e
  Pass -> "pass"
  Mutation v e -> ppVar Local v <+> "<=" <+> e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> ifCond) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  Switch switch cases ->
    ppBody tCase switch cases
  ExprStmt e -> e
  Return e -> "return" <+> e

tCase :: Case Context AnnStmt -> Context
tCase kase = tBody (tDecon kase.deconstruction <+?> kase.caseCondition) kase.body

tDecon :: Decon -> Context
tDecon = cata $ \case
  CaseVariable _ uv -> ppVar Local uv
  CaseConstructor _ uc [] -> ppCon uc
  CaseConstructor _ uc args@(_:_) -> ppCon uc <> encloseSepBy "(" ")" ", " args

tExpr :: Expr -> Context
tExpr = cata $ \(TypedExpr et expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType et <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Var l (DefinedVariable v) -> ppVar l v
  Var l (DefinedFunction f) -> ppVar l f.functionDeclaration.functionId
  Con (DC _ uc _ _) -> ppCon uc

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x at -> x <+> "as" <+> tType at
  Lam lenv params e -> tEnv lenv <+> sepBy " " (map (\(v, t) -> ppVar Local v <+> tType t) params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tDataDef :: DataDef -> Context
tDataDef (DD tid tvs unions cons _) = indent (foldl' (\x (TV y) -> x <+> pretty y) (ppTypeInfo tid) tvs <+> tUnions unions) $ ppLines (\dc@(DC _ _ _ ann) -> annotate ann (tConDef dc)) cons

tConDef :: DataCon -> Context
tConDef (DC _ g t _) = foldl' (<+>) (ppCon g) $ tTypes t

tFunction :: Function -> Context
tFunction fn = tBody (tFunDec fn.functionDeclaration) fn.functionBody

tFunDec :: FunDec -> Context
tFunDec (FD fenv v params retType) = comment (tEnv fenv) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType

tTypes :: Functor t => t Type -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) _ -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type -> Context
tType = cata $ \case
  TCon (DD ut _ _ _ _) params unions ->
    let conunion = case unions of
          [] -> []
          tunions -> "|" : (tEnvUnion <$> tunions)
    in foldl' (<+>) (ppTypeInfo ut) (params ++ conunion)
  TVar (TV tv) -> pretty tv
  TFun fenv args ret -> tEnvUnion fenv <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret
  TyVar ty -> tTyVar ty

tTyVar :: TyVar -> Context
tTyVar (TyV t) = "#" <> pretty t

tUnions :: [EnvUnion] -> Context
tUnions [] = mempty
tUnions unions = "|" <+> sepBy " " (tEnvUnion . fmap tType <$> unions)

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion { unionID = uid, union = us } = ppUnionID uid <> encloseSepBy "{" "}" ", " (fmap tEnv' us)

tEnv :: Env -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF Context -> Context
tEnv' Env { envID = eid, env = vs } = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc v <+> t) vs)


tBody :: Foldable f => Context -> f AnnStmt -> Context
tBody = ppBody tAnnStmt
