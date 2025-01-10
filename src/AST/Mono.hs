{-# LANGUAGE DeriveTraversable, LambdaCase, OverloadedRecordDot, OverloadedStrings, TemplateHaskell, TypeFamilies, TypeOperators #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}


module AST.Mono (module AST.Mono) where

import AST.Common (Ann, Annotated (..), Context, CtxData (..), EnvID, LitType (..), Locality (Local), Op (..), UnionID, UniqueCon, UniqueType, UniqueVar, annotate, comment, encloseSepBy, indent, ppBody, ppCon, ppEnvID, ppLines, ppTypeInfo, ppUnionID, ppVar, pretty, printf, sepBy, (:.) (..), (<+>), (<+?>), TVar (), ppTVar, ppLines')
import Control.Monad.Trans.Reader (ask)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Eq.Deriving (deriveEq1)
import Data.Fix (Fix (..))
import Data.Foldable (foldl')
import Data.Functor.Classes (Eq1 (liftEq), Ord1 (liftCompare))
import Data.Functor.Foldable (cata)
import Data.List.NonEmpty (NonEmpty ())
import qualified Data.List.NonEmpty as NonEmpty
import Data.Ord.Deriving (deriveOrd1)
import Data.String (fromString)


--- The two stages...

data IncompleteEnv  -- when it's not over (escaped tvars in environments are not resolved. we tracked each instantiation of an environment however. next step consists of resolving those.)
data FullEnv        -- it's over...  (everything is monomorphized and flattened.)

-- both of them substitute for 'envtype'.


---------------------
-- Data Definition --
---------------------

data DataCon' envtype = DC (DataDef' envtype) UniqueCon [Type' envtype] [Ann]
type IDataCon = DataCon' IncompleteEnv
type DataCon = DataCon' FullEnv

data DataDef' envtype = DD
  { thisType :: UniqueType
  , constructors :: [DataCon' envtype]
  , annotations :: [Ann]

    -- used only for displaying type information to the USER!
  , appliedTypes :: [Type' envtype]
  }
type IDataDef = DataDef' IncompleteEnv
type DataDef = DataDef' FullEnv


instance Eq (DataDef' envtype) where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord (DataDef' envtype) where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'

instance Eq (DataCon' envtype) where
  DC _ uc _ _ == DC _ uc' _ _ = uc == (uc' :: UniqueCon)

instance Ord (DataCon' envtype) where
  DC _ uc _ _ `compare` DC _ uc' _ _ = uc `compare` (uc' :: UniqueCon)

  

----------
-- Type --
----------

type family Env' envtype
type family Type' envtype


-- I think I'll keep the separate-but-same-structure environments until codegen, because it might be nice information to have?
-- I'll do deduplication during the codegen phase
data EnvF envtype t
  = Env EnvID [(Variable' envtype, Locality, t)]
  | RecursiveEnv EnvID IsEmpty
  deriving (Functor, Foldable, Traversable)

type IEnv = EnvF IncompleteEnv IType
type instance Env' IncompleteEnv = IEnv

type Env = EnvF FullEnv Type
type instance Env' FullEnv = Env

type IsEmpty = Bool


envID :: EnvF envtype t -> EnvID
envID = \case
  Env eid _ -> eid
  RecursiveEnv eid _ -> eid


instance Eq t => Eq (EnvF et t) where
  -- Env lid lts == Env rid rts = lid == rid && (lts <&> \(_, _, x) -> x) == (rts <&> \(_, _, x) -> x)
  l == r = envID l == envID r

instance Ord t => Ord (EnvF et t) where
  -- Env lid lts `compare` Env rid rts = (lid, lts <&> \(_, _, x) -> x) `compare` (rid, rts <&> \(_, _, x) -> x)
  l `compare` r = envID l `compare` envID r

instance Eq1 (EnvF et) where
  -- liftEq f (Env lid lts) (Env rid rts) = lid == rid && and (zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts)
  liftEq _ l r = envID l == envID r

instance Ord1 (EnvF et) where
  -- liftCompare f (Env lid lts) (Env rid rts) = case lid `compare` rid of
  --   EQ -> mconcat $ zipWith (\(_, _, l) (_, _, r) -> f l r) lts rts
  --   ord -> ord
  liftCompare _ l r = envID l `compare` envID r



data EnvUnionF env = EnvUnion
  { unionID :: UnionID,
    union :: NonEmpty env
  }
  deriving (Functor, Foldable, Traversable)

type IEnvUnion = EnvUnionF (EnvF IncompleteEnv IType)
type EnvUnion = EnvUnionF (EnvF FullEnv Type)


isEnvEmpty :: EnvF envtype t -> Bool
isEnvEmpty = \case
  RecursiveEnv _ isEmpty -> isEmpty
  Env _ envs -> null envs


areAllEnvsEmpty :: EnvUnionF (EnvF envtype a) -> Bool
areAllEnvsEmpty envUnion = all isEnvEmpty envUnion.union


instance Eq (EnvUnionF t) where
  EnvUnion {unionID = l} == EnvUnion {unionID = r} = l == r

instance Eq1 EnvUnionF where
  liftEq _ (EnvUnion {unionID = uid}) (EnvUnion {unionID = uid'}) = uid == uid'

instance Ord (EnvUnionF t) where
  EnvUnion {unionID = l} `compare` EnvUnion {unionID = r} = l `compare` r

instance Ord1 EnvUnionF where
  liftCompare _ (EnvUnion {unionID = uid}) (EnvUnion {unionID = uid'}) = uid `compare` uid'



data ITypeF a
  = ITCon IDataDef [a] [EnvUnionF (EnvF IncompleteEnv a)]  -- extra type parameters are only used for type mapping and later to know how to memoize. We can probably do this better. TODO maybe just store TypeMap here?
  | ITFun (EnvUnionF (EnvF IncompleteEnv a)) [a] a
  | ITVar TVar
  deriving (Eq, Ord, Functor, Foldable, Traversable)

type IType = Fix ITypeF
type instance Type' IncompleteEnv = IType


data TypeF a
  = TCon DataDef
  | TFun (EnvUnionF (EnvF FullEnv a)) [a] a
  deriving (Eq, Ord, Functor, Foldable, Traversable)

type Type = Fix TypeF
type instance Type' FullEnv = Type



--------------
-- Function --
--------------

data FunDec' envtype = FD
  { functionEnv :: Env' envtype,
    functionId :: UniqueVar,
    functionParameters :: [(UniqueVar, Type' envtype)],
    functionReturnType :: Type' envtype,  -- actually, the function might return something with a yet unknown environment type...
    functionNeedsEnvironment :: NeedsImplicitEnvironment
  }

type IFunDec = FunDec' IncompleteEnv
type FunDec = FunDec' FullEnv


instance Eq (FunDec' envtype) where
  FD _ uv _ _ _ == FD _ uv' _ _ _ = uv == uv'

instance Ord (FunDec' envtype) where
  FD _ uv _ _ _ `compare` FD _ uv' _ _ _ = uv `compare` uv'



data Function' envtype = Function
  { functionDeclaration :: FunDec' envtype,
    functionBody :: NonEmpty (AnnStmt' envtype)
  }

type IFunction = Function' IncompleteEnv
type Function = Function' FullEnv


instance Eq (Function' envtype) where
  Function {functionDeclaration = fd} == Function {functionDeclaration = fd'} = fd == fd'

instance Ord (Function' envtype) where
  Function {functionDeclaration = fd} `compare` Function {functionDeclaration = fd'} = fd `compare` fd'

-- Depending on the union, functions must sometimes take an environment parameter despite them not needing an environment - this is some functions will have an environment.
-- However, when all functions in a union don't take an environment parameter - don't create it.
-- It's also True if only this function has a non-empty environment.
type NeedsImplicitEnvironment = Bool



----------------
-- Expression --
----------------

data ExprF envtype a
  = Lit LitType
  | Var Locality (Variable' envtype)
  | Con (DataCon' envtype)
  | Op a Op a
  | Call a [a]
  | -- NOTE: We want to leave lambda for now, because it initializes its environment immediately.
    -- just makes it simpler for now to keep it. maybe depending on other backends / optimizations we might remove it and simplify the AST.
    Lam (Env' envtype) [(UniqueVar, Type' envtype)] a
  deriving (Functor, Foldable, Traversable)

data TypedExpr envtype a = TypedExpr (Type' envtype) (ExprF envtype a) deriving (Functor, Foldable, Traversable)


type IExpr = Fix (TypedExpr IncompleteEnv)
type Expr = Fix (TypedExpr FullEnv)


expr2type :: Expr -> Type
expr2type (Fix (TypedExpr t _)) = t



data Variable' envtype
  = DefinedVariable UniqueVar
  | DefinedFunction (Function' envtype)

type IVariable = Variable' IncompleteEnv
type Variable = Variable' FullEnv


asUniqueVar :: Variable' envtype -> UniqueVar
asUniqueVar = \case
  DefinedVariable uv -> uv
  DefinedFunction fn -> fn.functionDeclaration.functionId



----------
-- Case --
----------

data DeconF envtype a
  = CaseVariable (Type' envtype) UniqueVar
  | CaseConstructor (Type' envtype) (DataCon' envtype) [a]
  deriving (Functor)

type IDecon = Fix (DeconF IncompleteEnv)
type Decon = Fix (DeconF FullEnv)


data CaseF envtype expr stmt = Case
  { deconstruction :: Fix (DeconF envtype),
    caseCondition :: Maybe expr,
    body :: NonEmpty stmt
  }
  deriving (Functor, Foldable, Traversable)

type ICase = CaseF IncompleteEnv IExpr AnnIStmt
type Case = CaseF FullEnv Expr AnnStmt



---------------
-- Statement --
---------------

-- I want to leave expr here, so we can bifold and bimap
data StmtF envtype expr a
  = -- Typical statements
    Print expr
  | Assignment UniqueVar expr
  | Pass
  | Mutation UniqueVar Locality expr
  -- TODO: we should maybe make function bodies a normal list - by then it's possible for a body to be empty.
  | If expr (NonEmpty a) [(expr, NonEmpty a)] (Maybe (NonEmpty a))
  | Switch expr (NonEmpty (CaseF envtype expr a))
  | ExprStmt expr
  | Return expr
  | EnvDef (EnvDef envtype)
  deriving (Functor, Foldable, Traversable)

type IStmt = StmtF IncompleteEnv IExpr AnnIStmt
type Stmt = StmtF FullEnv Expr AnnStmt

type AnnStmt' envtype = Fix (Annotated :. StmtF envtype (Fix (TypedExpr envtype)))
type AnnIStmt = Fix (Annotated :. StmtF IncompleteEnv IExpr)
type AnnStmt = Fix (Annotated :. StmtF FullEnv Expr)


type family EnvDef envtype
type instance EnvDef IncompleteEnv = EnvID  -- EnvDefs are being redone, so we need to keep EnvID only.
type instance EnvDef FullEnv = NonEmpty (Function, Env)  -- I think Function is not needed here, but we might as well use it here for easier debugging (printing these functions in EnvDefs).


$(deriveBifunctor ''CaseF)
$(deriveBifoldable ''CaseF)
$(deriveBitraversable ''CaseF)
$(deriveBifunctor ''StmtF)
$(deriveBifoldable ''StmtF)
$(deriveBitraversable ''StmtF)
$(deriveEq1 ''ITypeF)
$(deriveOrd1 ''ITypeF)
$(deriveEq1 ''TypeF)
$(deriveOrd1 ''TypeF)



---------------
-- Module --
---------------

newtype Module = Mod
  { toplevelStatements :: [AnnStmt]
  }




--------------------------------------------------------------------------------------
-- Printing the AST

mModule :: Module -> Context
mModule m =
  let main = comment "Main" $ tStmts m.toplevelStatements
   in sepBy "\n" [main]

tStmts :: [AnnStmt] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt -> Context
tAnnStmt (Fix (O (Annotated ann stmt))) = annotate ann $ tStmt stmt

tStmt :: Stmt -> Context
tStmt stmt = case stmt of
  Print e -> "print" <+> tExpr e
  Assignment v e -> ppVar Local v <+> "=" <+> tExpr e
  Pass -> "pass"
  Mutation v l e -> ppVar l v <+> "<=" <+> tExpr e
  If ifCond ifTrue elseIfs mElse ->
    tBody ("if" <+> tExpr ifCond) ifTrue
      <> foldMap
        ( \(cond, elseIf) ->
            tBody ("elif" <+> tExpr cond) elseIf
        )
        elseIfs
      <> maybe mempty (tBody "else") mElse
  Switch switch cases ->
    ppBody tCase (tExpr switch) cases
  ExprStmt e -> tExpr e
  Return e -> "return" <+> tExpr e
  EnvDef funEnv -> fromString $ printf "[ENV]: %s" (tEnvDef funEnv)

tEnvDef :: EnvDef FullEnv -> Context
tEnvDef envdef = ppLines' $
  (encloseSepBy "[" "]" ", " . NonEmpty.toList $ tEnv . snd <$> envdef) : NonEmpty.toList (tFunction . fst <$> envdef)

tCase :: Case -> Context
tCase kase = tBody (tDecon kase.deconstruction <+?> fmap tExpr kase.caseCondition) kase.body

tDecon :: Decon -> Context
tDecon = cata $ \case
  CaseVariable _ uv -> ppVar Local uv
  CaseConstructor _ (DC _ uc _ _) [] -> ppCon uc
  CaseConstructor _ (DC _ uc _ _) args@(_ : _) -> ppCon uc <> encloseSepBy "(" ")" ", " args

tExpr :: Expr -> Context
tExpr = cata $ \(TypedExpr t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType t <> ")"
   in encloseInType $ case expr of
        Lit (LInt x) -> pretty x
        Lit (LFloat f) -> pretty $ show f
        Var l (DefinedVariable v) -> ppVar l v
        Var l (DefinedFunction f) -> ppVar l f.functionDeclaration.functionId
        Con (DC _ uc _ _) -> ppCon uc
        Op l op r -> l <+> ppOp op <+> r
        Call f args -> f <> encloseSepBy "(" ")" ", " args
        Lam lenv params e -> fromString $ printf "%s %s:%s" (tEnv lenv) (sepBy " " (map (\(v, vt) -> ppVar Local v <+> tType vt) params)) e
  where
    ppOp = \case
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="

tFunction :: Function -> Context
tFunction (Function fd funBody) = tBody (tFunDec fd) funBody

tDataDef :: DataDef -> Context
tDataDef (DD tid cons ann _) = annotate ann $ indent (ppTypeInfo tid) $ ppLines tConDef cons

tConDef :: DataCon -> Context
tConDef (DC _ g t ann) = annotate ann $ foldl' (<+>) (ppCon g) $ tTypes t

tFunDec :: FunDec -> Context
tFunDec (FD funEnv v params retType needsEnv) = comment (tEnv funEnv) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" " <>) . tType) pType) params) <> ((" " <>) . tType) retType <> (if needsEnv then " +ENV" else " -ENV")

tTypes :: (Functor t) => t Type -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon (DD _ _ _ []) -> tType t
  TCon _ -> enclose t
  TFun {} -> enclose t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type -> Context
tType = cata $ \case
  TCon (DD tid _ _ ts) -> do
    c <- ask
    if c.displayTypeParameters && not (null ts)
      then ppTypeInfo tid <+> sepBy " " (tTypes ts)
      else ppTypeInfo tid
  TFun funUnion args ret -> tEnvUnion (tEnv' <$> funUnion) <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

tEnvUnion :: EnvUnionF Context -> Context
tEnvUnion EnvUnion {unionID = uid, union = us} = ppUnionID uid <> encloseSepBy "{" "}" ", " (NonEmpty.toList us)

tEnvUnion' :: EnvUnionF Type -> Context
tEnvUnion' = tEnvUnion . fmap tType

tEnv :: EnvF FullEnv Type -> Context
tEnv = tEnv' . fmap tType

tEnv' :: EnvF FullEnv Context -> Context
tEnv' (RecursiveEnv eid isEmpty) = fromString $ printf "%s[REC%s]" (ppEnvID eid) (if isEmpty then "(empty)" else "(some)" :: Context)
tEnv' (Env eid vs) = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc (asUniqueVar v) <+> t) vs)

tBody :: (Foldable f) => Context -> f AnnStmt -> Context
tBody = ppBody tAnnStmt



--------------------------------------------------------------------------------------
-- Printing the AST (cucked version)

mtStmts :: [AnnIStmt] -> Context
mtStmts = ppLines mtAnnStmt

mtAnnStmt :: AnnIStmt -> Context
mtAnnStmt (Fix (O (Annotated ann stmt))) = annotate ann $ mtStmt stmt

mtStmt :: IStmt -> Context
mtStmt stmt = case stmt of
  Print e -> "print" <+> mtExpr e
  Assignment v e -> ppVar Local v <+> "=" <+> mtExpr e
  Pass -> "pass"
  Mutation v l e -> ppVar l v <+> "<=" <+> mtExpr e
  If ifCond ifTrue elseIfs mElse ->
    mtBody ("if" <+> mtExpr ifCond) ifTrue
      <> foldMap
        ( \(cond, elseIf) ->
            mtBody ("elif" <+> mtExpr cond) elseIf
        )
        elseIfs
      <> maybe mempty (mtBody "else") mElse
  Switch switch cases ->
    ppBody mtCase (mtExpr switch) cases
  ExprStmt e -> mtExpr e
  Return e -> "return" <+> mtExpr e
  EnvDef funEnv -> fromString $ printf "[ENV]: %s" (mtEnvDef funEnv)

mtEnvDef :: EnvDef IncompleteEnv -> Context
mtEnvDef = ppEnvID

mtCase :: ICase -> Context
mtCase kase = mtBody (mtDecon kase.deconstruction <+?> fmap mtExpr kase.caseCondition) kase.body

mtDecon :: IDecon -> Context
mtDecon = cata $ \case
  CaseVariable _ uv -> ppVar Local uv
  CaseConstructor _ (DC _ uc _ _) [] -> ppCon uc
  CaseConstructor _ (DC _ uc _ _) args@(_ : _) -> ppCon uc <> encloseSepBy "(" ")" ", " args

mtExpr :: IExpr -> Context
mtExpr = cata $ \(TypedExpr t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> mtType t <> ")"
   in encloseInType $ case expr of
        Lit (LInt x) -> pretty x
        Lit (LFloat f) -> pretty $ show f
        Var l (DefinedVariable v) -> ppVar l v
        Var l (DefinedFunction f) -> ppVar l f.functionDeclaration.functionId
        Con (DC _ uc _ _) -> ppCon uc
        Op l op r -> l <+> ppOp op <+> r
        Call f args -> f <> encloseSepBy "(" ")" ", " args
        Lam lenv params e -> fromString $ printf "%s %s:%s" (mtEnv lenv) (sepBy " " (map (\(v, vt) -> ppVar Local v <+> mtType vt) params)) e
  where
    ppOp = \case
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="

mtFunction :: IFunction -> Context
mtFunction (Function fd funBody) = mtBody (mtFunDec fd) funBody

mtDataDef :: DataDef -> Context
mtDataDef (DD tid cons ann _) = annotate ann $ indent (ppTypeInfo tid) $ ppLines tConDef cons

mtConDef :: DataCon -> Context
mtConDef (DC _ g t ann) = annotate ann $ foldl' (<+>) (ppCon g) $ tTypes t

mtFunDec :: IFunDec -> Context
mtFunDec (FD funEnv v params retType needsEnv) = comment (mtEnv funEnv) $ ppVar Local v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppVar Local pName <> ((" " <>) . mtType) pType) params) <> ((" " <>) . mtType) retType <> (if needsEnv then " +ENV" else " -ENV")

mtTypes :: (Functor t) => t IType -> t Context
mtTypes = fmap $ \t@(Fix t') -> case t' of
  ITCon {} -> enclose t
  ITFun {} -> enclose t
  _ -> mtType t
  where
    enclose x = "(" <> mtType x <> ")"

mtType :: IType -> Context
mtType = cata $ \case
  ITCon (DD tid _ _ _) _ _ -> ppTypeInfo tid
  ITFun funUnion args ret -> tEnvUnion (mtEnv' <$> funUnion) <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret
  ITVar tv -> ppTVar tv

mtEnv :: EnvF IncompleteEnv IType -> Context
mtEnv = mtEnv' . fmap mtType

mtEnv' :: EnvF IncompleteEnv Context -> Context
mtEnv' (RecursiveEnv eid isEmpty) = fromString $ printf "%s[REC%s]" (ppEnvID eid) (if isEmpty then "(empty)" else "(some)" :: Context)
mtEnv' (Env eid vs) = ppEnvID eid <> encloseSepBy "[" "]" ", " (fmap (\(v, loc, t) -> ppVar loc (asUniqueVar v) <+> t) vs)

mtBody :: (Foldable f) => Context -> f AnnIStmt -> Context
mtBody = ppBody mtAnnStmt
