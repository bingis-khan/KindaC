{-# LANGUAGE TemplateHaskell, DeriveTraversable, TypeFamilies, OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeOperators #-}
module AST.Typed (module AST.Typed) where

import AST.Common (LitType (..), Op (..), Annotated (..), TVar (..), Ann, UniqueType, UniqueVar, UniqueCon, Locality (Local), Context, CtxData (..), ppLines, annotate, (<+>), ppVar, (<+?>), pretty, ppCon, encloseSepBy, sepBy, indent, ppTypeInfo, comment, ppBody, UnionID, EnvID, ppUnionID, ppEnvID, (:.) (..), ppLines', printf, ppVariableType, VariableType, ctx)

import Data.Eq.Deriving
import Data.Ord.Deriving
import Data.Fix (Fix (..))
import Data.List.NonEmpty (NonEmpty)

import Data.Bifunctor.TH (deriveBifoldable, deriveBifunctor, deriveBitraversable)
import Data.Functor.Classes (Eq1 (liftEq), Ord1 (..))
import Control.Monad.Trans.Reader (runReader)
import Data.Biapplicative (first)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')
import Data.Text (Text)
import Data.String (fromString)
import Data.Functor ((<&>))



---------------------
-- Data Definition --
---------------------

data DataCon = DC DataDef UniqueCon [Type] [Ann]
data DataDef = DD UniqueType [TVar] [DataCon] [Ann]

instance Eq DataDef where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord DataDef where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'

instance Eq DataCon where
  DC _ uc _ _ == DC _ uc' _ _ = uc == (uc' :: UniqueCon)

instance Ord DataCon where
  DC _ uc _ _ `compare` DC _ uc' _ _ = uc `compare` (uc' :: UniqueCon)


----------
-- Type --
----------

-- Env without this "superposition" - present when defining functions and lambdas.
-- do I need ID here?
-- reasons:
--  - always nice to have additional information?
data EnvF t
  = Env EnvID [(Variable, Locality, t)] -- t is here, because of recursion schemes. UniqueVar, because we don't know which environments will be used in the end. We will replace it with a `Variable` equivalent AFTER we monomorphise.
  | RecursiveEnv EnvID IsEmpty  -- Recursive functions won't have access to their environment while typechecking... kinda stupid. ehh... but we're solving an actual issue here. `IsEmpty` is used in Mono to let us know if this function's environment was empty or not.
  deriving (Functor, Foldable, Traversable)
type Env = EnvF Type

type IsEmpty = Bool

envID :: EnvF t -> EnvID
envID = \case
  Env eid _ -> eid
  RecursiveEnv eid _ -> eid

instance Eq t => Eq (EnvF t) where
  Env lid lts == Env rid rts = lid == rid && (lts <&> \(_, _, x) -> x) == (rts <&> \(_, _, x) -> x)
  l == r  = envID l == envID r

instance Ord t => Ord (EnvF t) where
  Env lid lts `compare` Env rid rts = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)
  l `compare` r = envID l `compare` envID r

instance Eq1 EnvF where
  liftEq f (Env lid lts) (Env rid rts) = lid == rid && and (zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts)
  liftEq _ l r = envID l == envID r

instance Ord1 EnvF where
  liftCompare f (Env lid lts) (Env rid rts) = case lid `compare` rid of
    EQ -> mconcat $ zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts
    ord -> ord
  liftCompare _ l r = envID l `compare` envID r

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
  liftEq f u u' = u.unionID == u'.unionID && and (zipWith (liftEq f) u.union u'.union)

instance Ord1 EnvUnionF where
  liftCompare f u u' = case u.unionID `compare` u'.unionID of
    EQ -> mconcat $ zipWith (liftCompare f) u.union u'.union
    cmp -> cmp

instance Eq t => Eq (EnvUnionF t) where
  EnvUnion { unionID = l, union = lu } == EnvUnion { unionID = r, union = ru } = l == r && lu == ru

instance Ord t => Ord (EnvUnionF t) where
  EnvUnion { unionID = l, union = lu } `compare` EnvUnion { unionID = r, union = ru } = (l, lu) `compare` (r, ru)



newtype TyVar = TyV { fromTyV :: Text } deriving (Eq, Ord)

data TypeF a
  = TCon DataDef [a] [EnvUnionF a]
  | TVar TVar  -- TODO: make it unique per function scope. Should I use UniqueVar or something else?
  | TFun (EnvUnionF a) [a] a
  | TyVar TyVar
  deriving (Eq, Ord, Functor, Foldable, Traversable)
type Type = Fix TypeF


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

instance Ord Function where
  fn `compare` fn' = fn.functionDeclaration.functionId `compare` fn'.functionDeclaration.functionId


----------------
-- Expression --
----------------

data ExprF a
  = Lit LitType
  | Var Locality Variable
  | Con EnvID DataCon -- NOTE: `Env` here is supposed to be an empty environment that was generated during instantiation. It used in RemoveUnused. This is bad and not typesafe, but whatever!

  | Op a Op a
  | Call a [a]
  | Lam Env [(UniqueVar, Type)] a

  | As a Type
  deriving (Functor, Foldable, Traversable)

data TypedExpr a = TypedExpr Type (ExprF a) deriving (Functor, Foldable, Traversable)
type Expr = Fix TypedExpr

data Variable
  = DefinedVariable UniqueVar
  | DefinedFunction Function
  deriving (Eq, Ord)

asUniqueVar :: Variable -> UniqueVar
asUniqueVar = \case
  DefinedVariable uv -> uv
  DefinedFunction fn -> fn.functionDeclaration.functionId


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
  | Mutation UniqueVar Locality expr
  | Pass

  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (Case expr a))
  | ExprStmt expr
  | Return expr

  | EnvDef Env
  deriving (Functor, Foldable, Traversable)


-- not sure about this one. if using it is annoying, throw it out. (eliminates the possibility to bimap)
-- also, the style does not fit.
type Stmt = StmtF Expr AnnStmt
type AnnStmt = Fix (Annotated :. StmtF Expr)

$(deriveBifunctor ''Case)
$(deriveBifoldable ''Case)
$(deriveBitraversable ''Case)
$(deriveBifoldable ''StmtF)
$(deriveBifunctor ''StmtF)
$(deriveBitraversable ''StmtF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)


---------------
-- Module --
---------------

data Module = Mod
  { toplevelStatements :: [AnnStmt]
  , exports :: Exports
  
  -- not needed, used for printing the AST.
  , functions :: [Function]
  , datatypes :: [DataDef]
  }

data Exports = Exports
  { variables :: [UniqueVar]
  , functions :: [Function]
  , datatypes :: [DataDef]
  }



--------------------
-- Utility


extractUnionsFromDataType :: DataDef -> [EnvUnion]
extractUnionsFromDataType (DD _ _ dcs _) =
  concatMap extractUnionsFromConstructor dcs

extractUnionsFromConstructor :: DataCon -> [EnvUnion]
extractUnionsFromConstructor (DC (DD ut _ _ _) _ ts _) = concatMap (mapUnion ut) ts

-- TODO: clean up all the mapUnion shit. think about proper structure.
mapUnion :: UniqueType -> Type -> [EnvUnion]
mapUnion ut (Fix t) = case t of
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  TCon (DD tut _ _ _) paramts conUnions
    -- breaks cycle with self referential datatypes.
    | tut == ut -> concatMap (mapUnion ut) paramts
    | otherwise -> conUnions <> concatMap (mapUnion ut) paramts

  TFun u args ret -> [u] <> concatMap (mapUnion ut) args <> mapUnion ut ret
  TVar _ -> []
  TyVar _ -> []



--------------------------------------------------------------------------------------
-- Printing the AST

tModule :: Module -> Context
tModule m = 
  ppLines'
    [ ppLines tDataDef m.datatypes
    , ppLines tFunction m.functions
    , tStmts m.toplevelStatements
    ]

tStmtsOnly :: [AnnStmt] -> String
tStmtsOnly = ctx tStmts

tStmts :: [AnnStmt] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt -> Context
tAnnStmt (Fix (O (Annotated ann stmt))) = annotate ann $ tStmt stmt

tStmt :: Stmt -> Context
tStmt stmt = case first tExpr stmt of
  Print e -> "print" <+> e
  Assignment v e -> ppVar Local v <+> "=" <+> e
  Pass -> "pass"
  Mutation v loc e -> ppVar loc v <+> "<=" <+> e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> ifCond) ifTrue <>
    foldMap (\(cond, elseIf) ->
        tBody ("elif" <+> cond) elseIf) elseIfs <>
    maybe mempty (tBody "else") mElse
  Switch switch cases ->
    ppBody tCase switch cases
  ExprStmt e -> e
  Return e -> "return" <+> e
  EnvDef envDef -> "$$$:" <+> tEnv envDef

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
  Con _ (DC _ uc _ _) -> ppCon uc

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  Lam lenv params e -> tEnv lenv <+> sepBy " " (map (\(v, t) -> ppVar Local v <+> tType t) params) <> ":" <+> e
  As e t -> e <+> "as" <+> tType t
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tDataDef :: DataDef -> Context
tDataDef (DD tid tvs cons _) = indent (foldl' (\x (TV y) -> x <+> pretty y) (ppTypeInfo tid) tvs) $ ppLines (\dc@(DC _ _ _ ann) -> annotate ann (tConDef dc)) cons

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
  TCon (DD ut _ _ _) params unions ->
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
tEnv' = \case
  Env eid vs -> ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc (asUniqueVar v) <+> t) vs)
  RecursiveEnv eid isEmpty -> fromString $ printf "%s[REC%s]" (ppEnvID eid) (if isEmpty then "(empty)" else "(some)" :: Context)


tBody :: Foldable f => Context -> f AnnStmt -> Context
tBody = ppBody tAnnStmt
