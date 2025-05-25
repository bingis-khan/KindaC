{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module AST.Common (module AST.Common) where

import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import Data.Fix (Fix (..))
import AST.Def ((:.) (..), Annotated, PP (..), (<+>), Op (..), (<+?>))
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')
import Data.Bifunctor.TH (deriveBifunctor)
import Data.Bifunctor (first)
import qualified Data.List.NonEmpty as NonEmpty


type family XTCon phase
type family XTVar phase

data TypeF phase a
  = TCon (XTCon phase) [a]
  | TVar (XTVar phase)
  | TFun [a] a
  deriving (Functor, Foldable, Traversable)
type Type phase = Fix (TypeF phase)


type family XVar phase
type family XCon phase
type family XMem phase

data ExprF phase a
  = Lit Def.LitType  -- NOTE: all these types are not set in stone. If I need to change it later (to be dependent on phase) then I should do it.
  | Var (XVar phase)
  | Con (XCon phase)

  | RecCon (XTCon phase) (NonEmpty (XMem phase, a))
  | RecUpdate a (NonEmpty (XMem phase, a))
  | MemAccess a (XMem phase)

  | Op a Def.Op a
  | Call a [a]
  | As a (Type phase)
  | Lam [XVar phase] a
  deriving (Functor, Foldable, Traversable)
type Expr phase = Fix (ExprF phase)


---------------
-- Data Defs --
---------------

data DataCon phase = DC
  { con :: XCon phase
  , conTypes :: [Type phase]
  }

data DataDef phase = DD
  { ddName :: XTCon phase
  , tvars  :: [XTVar phase]
  , cons   :: [Annotated (DataCon phase)]
  }


data DataRec phase = DR
  { drName :: XTCon phase
  , tvars :: [XTVar phase]
  , members :: NonEmpty (Annotated (XMem phase, Type phase))
  }



----------
-- Case --
----------

data DeconF phase a
  = CaseVariable (XVar phase)
  | CaseConstructor (XCon phase) [a]
  | CaseRecord (XTCon phase) (NonEmpty (XMem phase, a))
  deriving Functor
type Decon phase = Fix (DeconF phase)

data CaseF phase expr stmt = Case
  { deconstruction :: Decon phase
  , caseCondition :: Maybe expr
  , caseBody :: NonEmpty stmt
  } deriving (Functor, Foldable, Traversable)
type Case phase = CaseF phase (Expr phase) (AnnStmt phase)



----------
-- Stmt --
----------

data IfStmt phase expr a = IfStmt  -- it's own datatype, because it's quite complicated.
  { condition :: expr
  , ifTrue    :: NonEmpty a
  , elifs     :: [(expr, NonEmpty a)]
  , mElse     :: Maybe (NonEmpty a)
  } deriving (Functor, Foldable, Traversable)


type family XFunDef phase
type family XInstDef phase
type family XReturn phase
type family XOther phase

data StmtF phase expr a
  = Pass

  | Print expr
  | Assignment (XVar phase) expr
  | Mutation (XVar phase) expr

  | If (IfStmt phase expr a)
  | Switch expr (NonEmpty (CaseF phase expr a))
  | ExprStmt expr  -- NOTE: in the future add typing to distinguish available expressions.
  | Return (XReturn phase)  -- NOTE: kinda bad... this is the only part which does not use "expr" tvar.

  | Fun (XFunDef phase)
  | Inst (XInstDef phase)

  | Other (XOther phase)
  deriving (Functor, Foldable, Traversable)
type Stmt phase = StmtF phase (Expr phase) (AnnStmt phase)
type AnnStmt phase = Fix (Annotated :. StmtF phase (Expr phase))

$(deriveBifunctor ''IfStmt)
$(deriveBifunctor ''CaseF)
$(deriveBifunctor ''StmtF)


--------------
-- Function --
--------------

type family XEnv phase

data FunDec phase = FD
  { functionEnv :: XEnv phase
  , functionId :: XVar phase
  , functionParameters :: [(Decon phase, Maybe (Type phase))]
  , functionReturnType :: Maybe (Type phase)
  }


-----------------
-- Typeclasses --
-----------------

type family XClass phase

data ClassDef phase = ClassDef
  { classID :: XClass phase
  -- , classDependentTypes :: [Dependent]
  , classFunctions :: [ClassFunDec phase]
  }

data ClassFunDec phase = CFD (XVar phase) [(Decon phase, ClassType phase)] (ClassType phase)

data ClassTypeF phase a
  = Self
  | NormalType (TypeF phase a)
  deriving (Functor, Foldable, Traversable)
type ClassType phase = Fix (ClassTypeF phase)



data InstDef phase = InstDef
  { instClassName :: XClass phase
  , instType :: (XTCon phase, [XTVar phase])
  , instFuns :: [InstFun phase]
  }

data InstFun phase = InstFun
  { instFunDec :: FunDec phase
  , instFunBody :: NonEmpty (AnnStmt phase)
  }


type family Module phase


--------------------
-- Printing stuff --
--------------------

instance (PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase)) => PP (AnnStmt phase) where
  pp (Fix (O (Def.Annotated ann stmt))) = Def.annotate ann $ pp stmt

instance (PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XTVar phase), PP (XVar phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase)) => PP (Stmt phase) where
  pp stmt = case first pp stmt of
    Print e -> "print" <+> e
    Assignment v e -> pp v <+> "=" <+> e
    Pass -> "pass"
    Mutation v e -> pp v <+> "<=" <+> e
    If ifs ->
      Def.ppBody' pp ("if" <+> ifs.condition) ifs.ifTrue <>
      foldMap (\(cond, elseIf) ->
          Def.ppBody' pp ("elif" <+> cond) elseIf) ifs.elifs <>
      maybe mempty (Def.ppBody' pp "else") ifs.mElse
    Switch switch cases ->
      Def.ppBody' pp switch cases
    ExprStmt e -> e
    Return e -> "return" <+> pp e
    Fun fd -> pp fd
    Inst idef -> pp idef
    Other other -> pp other
    -- EnvDef fn -> fromString $ printf "[ENV]: %s" $ tEnv fn.functionDeclaration.functionEnv
    -- InstDefDef inst -> tInst inst

instance (PP (XTVar phase), PP (XCon phase), PP (XVar phase), PP (XTCon phase), PP (XMem phase)) => PP (Expr phase) where
  pp = cata $ \case
    Lit l -> pp l
    Var v -> pp v
    Con c -> pp c

  
    RecCon dd inst -> pp dd <+> ppRecordMems inst
    RecUpdate c upd -> c <+> ppRecordMems upd
    MemAccess c mem -> c <> "." <> pp mem

    Op l op r -> l <+> ppOp op <+> r
    Call f args -> f <> Def.encloseSepBy "(" ")" ", " args
    As x at -> x <+> "as" <+> pp at
    Lam params e -> Def.encloseSepBy "(" ")" ", " (map pp params) <> ":" <+> e
    where
      ppOp op = case op of
        Plus -> "+"
        Minus -> "-"
        Times -> "*"
        Divide -> "/"
        Equals -> "=="
        NotEquals -> "/="

ppRecordMems :: PP mem => NonEmpty (mem, Def.Context) -> Def.Context
ppRecordMems = Def.encloseSepBy "{" "}" ", " . fmap (\(mem, e) -> pp mem <> ":" <+> e) . NonEmpty.toList

instance
  (PP expr, PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase))
  => PP (CaseF phase expr (AnnStmt phase)) where
  pp kase = Def.ppBody' pp (pp kase.deconstruction <+?> fmap pp kase.caseCondition) kase.caseBody

instance
  (PP (XMem phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase))
  => PP (Decon phase) where
  pp = cata $ \case
    CaseVariable uv -> pp uv
    CaseConstructor uc [] -> pp uc
    CaseConstructor uc args@(_:_) -> pp uc <> Def.encloseSepBy "(" ")" ", " args
    CaseRecord dd args -> pp dd <+> ppRecordMems args

instance (PP a, PP (XTVar phase), PP (XTCon phase)) => PP (TypeF phase a) where
  pp = \case
    TCon tcon params ->
      foldl' (<+>) (pp tcon) (pp <$> params)
    TVar x -> pp x
    TFun args ret -> Def.encloseSepBy "(" ")" ", " (pp <$> args) <+> "->" <+> pp ret

instance (PP (XTVar phase), PP (XTCon phase)) => PP (Type phase) where
  pp = cata pp

instance (PP (XTVar phase), PP (XTCon phase)) => PP (ClassType phase) where
  pp = cata $ \case
    Self -> "_"
    NormalType nt -> pp nt

instance (PP (XEnv phase), PP (XVar phase), PP (XMem phase), PP (XCon phase), PP (XTVar phase), PP (XTCon phase)) => PP (FunDec phase) where
  pp (FD fenv v params retType) = do
    pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> pp pName <+?> fmap pp pType) params) <+?> fmap pp retType

instance
  (PP (XVar phase), PP (XCon phase), PP (XEnv phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XTVar phase), PP (XClass phase), PP (XTCon phase))
  => PP (InstDef phase) where
  pp inst =
    let
      header = "inst" <+> pp inst.instClassName <+> pp (fst inst.instType) <+> Def.sepBy " " (pp <$> snd inst.instType)
    in Def.ppBody
      (\ifn -> Def.ppBody' pp (pp ifn.instFunDec) ifn.instFunBody)
      header
      inst.instFuns


instance (PP (XTVar phase), PP (XTCon phase), PP (XCon phase)) => PP (DataDef phase) where
  pp (DD tid tvs dcons) = Def.ppBody pp (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) dcons

instance (PP (XTVar phase), PP (XTCon phase), PP (XCon phase)) => PP (DataCon phase) where
  pp (DC g t) = foldl' (<+>) (pp g) $ tTypes t

tTypes :: (PP (XTVar phase), PP (XTCon phase), Functor t) => t (Type phase) -> t Def.Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> pp t
  where
    enclose x = "(" <> pp x <> ")"


instance (PP (XTVar phase), PP (XTCon phase), PP (XMem phase)) => PP (DataRec phase) where
  pp (DR tid tvs recs) = Def.ppBody' tRec (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) recs
    where
      tRec (Def.Annotated ann (mem, t)) = Def.annotate ann (pp mem <+> pp t)


instance (PP (XClass phase), PP (XVar phase), PP (XMem phase), PP (XTVar phase), PP (XCon phase), PP (XTCon phase)) => PP (ClassDef phase) where
  pp c = Def.ppBody pp (pp c.classID) c.classFunctions

instance (PP (XVar phase), PP (XMem phase), PP (XTVar phase), PP (XCon phase), PP (XTCon phase)) => PP (ClassFunDec phase) where
  pp (CFD v params ret) = pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pDecon, pType) -> pp pDecon <+> pp pType) params) <+> pp ret
