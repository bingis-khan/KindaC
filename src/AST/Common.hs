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
import AST.Def ((:.) (..), Annotated (..), PP (..), (<+>), Op (..), (<+?>), UniqueVar)
import Data.Functor.Foldable (cata)
import Data.Foldable (foldl')
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable)
import Data.Bifunctor (first)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Text (Text)
import Data.Set (Set)


-- Naming scheme:
-- X<name>  <- reference to actual datatype
-- XD<name> <- ID of that datatype


type family XTCon phase
type family XTVar phase

data TypeF phase a
  = TCon (XTCon phase) [a]
  | TVar (XTVar phase)
  | TFun [a] a
  deriving (Functor, Foldable, Traversable)
type Type phase = Fix (TypeF phase)


type family XVar phase
type family XVarOther phase
type family XCon phase
type family XMem phase
type family XLamOther phase

data ExprF phase a
  = Lit Def.LitType  -- NOTE: all these types are not set in stone. If I need to change it later (to be dependent on phase) then I should do it.
  | Var (XVar phase) (XVarOther phase)
  | Con (XCon phase)

  | RecCon (XTCon phase) (NonEmpty (XMem phase, a))
  | RecUpdate a (NonEmpty (XMem phase, a))
  | MemAccess a (XMem phase)

  | Op a Def.Op a
  | Call a [a]
  | As a (Type phase)
  | Lam (XLamOther phase) [XLVar phase] a
  deriving (Functor, Foldable, Traversable)
type Expr phase = Fix (ExprF phase)


---------------
-- Data Defs --
---------------

type family Rec phase a
type family XDCon phase

data DataCon phase = DC
  { conDataDef :: Rec phase (DataDef phase)
  , conID :: XDCon phase
  , conTypes :: [Type phase]
  , conAnns :: [Def.Ann]
  }


type family XDTCon phase
type Mem phase = Annotated (XMem phase, Type phase)

data DataDef phase = DD
  { ddName :: XDTCon phase
  , ddTVars  :: [XTVar phase]
  , ddCons   :: Either (NonEmpty (Mem phase)) [DataCon phase]
  , ddAnns   :: [Def.Ann]  -- TEMP: not very typesafe in Untyped, but should be okay. Might later change it to "extra".
  }



----------
-- Case --
----------

data DeconF phase a
  = CaseVariable (XLVar phase)
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
type family XLVar phase

data StmtF phase expr a
  = Pass

  | Print expr
  | Assignment (XLVar phase) expr
  | Mutation (XLVar phase) expr  -- TEMP: RIGHT NOW WE CAN ONLY ASSIGN TO LOCAL VARIABLES.

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

$(deriveBifoldable ''IfStmt)
$(deriveBifoldable ''CaseF)
$(deriveBifoldable ''StmtF)

--------------
-- Function --
--------------

type family XEnv phase
type family XFunVar phase

data FunDec phase = FD
  { functionEnv :: XEnv phase
  , functionId :: XFunVar phase
  , functionParameters :: [(Decon phase, Maybe (Type phase))]
  , functionReturnType :: Maybe (Type phase)
  }

data Function phase = Function
  { functionDeclaration :: FunDec phase
  , functionBody :: NonEmpty (AnnStmt phase)
  }




-----------------
-- Typeclasses --
-----------------

type family XClass phase
type family XDClass phase

data ClassDef phase = ClassDef
  { classID :: XDClass phase
  -- , classDependentTypes :: [Dependent]
  , classFunctions :: [ClassFunDec phase]
  }

data ClassFunDec phase = CFD (Rec phase (ClassDef phase)) (XFunVar phase) [(Decon phase, ClassType phase)] (ClassType phase)

data ClassTypeF phase a
  = Self
  | NormalType (TypeF phase a)
  deriving (Functor, Foldable, Traversable)
type ClassType phase = Fix (ClassTypeF phase)


type family ClassConstraints phase

data InstDef phase = InstDef
  { instClass :: XClass phase
  , instType :: (XTCon phase, [XTVar phase])
  , instFuns :: [InstFun phase]
  , instConstraints :: ClassConstraints phase
  }

data InstFun phase = InstFun
  { instFunDec :: FunDec phase
  , instFunBody :: NonEmpty (AnnStmt phase)
  }


data Exports phase = Exports
  { variables :: [UniqueVar]
  , functions :: [Function phase]
  , datatypes :: [DataDef phase]
  , classes :: [ClassDef phase]
  , instances :: [InstDef phase]
  }

type family Module phase


-- For Resolved and Typed
data TVar phase = TV
  { fromTV :: Text
  , binding :: Def.Binding
  , tvClasses :: Set (XClass phase)
  }



---------------
-- Instances --
---------------

instance Eq (XFunVar phase) => Eq (Function phase) where
  Function { functionDeclaration = fd } == Function { functionDeclaration = fd' } = fd.functionId == fd'.functionId

instance Ord (XFunVar phase) => Ord (Function phase) where
  fn `compare` fn' = fn.functionDeclaration.functionId `compare` fn'.functionDeclaration.functionId


instance Eq (XDClass phase) => Eq (ClassDef phase) where
  cd == cd' = cd.classID == cd'.classID

instance Ord (XDClass phase) => Ord (ClassDef phase) where
  cd `compare` cd' = cd.classID `compare` cd'.classID


instance Eq (XFunVar phase) => Eq (ClassFunDec phase) where
  CFD _ uv _ _ == CFD _ uv' _ _ = uv == uv'

instance Ord (XFunVar phase) => Ord (ClassFunDec phase) where
  CFD _ uv _ _ `compare` CFD _ uv' _ _ = uv `compare` uv'


instance (Eq (XClass phase), Eq (XTCon phase)) => Eq (InstDef phase) where
  instdef == instdef' = instdef.instClass == instdef'.instClass && fst instdef.instType == fst instdef'.instType

instance (Ord (XClass phase), Ord (XTCon phase)) => Ord (InstDef phase) where
  instdef `compare` instdef' = (instdef.instClass, fst instdef.instType) `compare` (instdef'.instClass, fst instdef'.instType)


instance Eq (TVar phase) where
  tv == tv' = tv.fromTV == tv'.fromTV && tv.binding == tv'.binding

instance Ord (TVar phase) where
  tv `compare` tv' = (tv.fromTV, tv.binding) `compare` (tv'.fromTV, tv'.binding)

instance Eq (XDCon phase) => Eq (DataCon phase) where
  DC _ uc _ _ == DC _ uc' _ _ = uc == uc'

instance Eq (XDTCon phase) => Eq (DataDef phase) where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord (XDTCon phase) => Ord (DataDef phase) where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'



--------------------
-- Printing stuff --
--------------------

instance (PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase)) => PP (AnnStmt phase) where
  pp (Fix (O (Def.Annotated ann stmt))) = Def.annotate ann $ pp stmt

instance (PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XTVar phase), PP (XVar phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase)) => PP (Stmt phase) where
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

instance (PP (XTVar phase), PP (XCon phase), PP (XVar phase), PP (XLVar phase), PP (XTCon phase), PP (XMem phase), PP (XVarOther phase), PP (XLamOther phase)) => PP (Expr phase) where
  pp = cata $ \case
    Lit l -> pp l
    Var v other -> pp other <> pp v  -- HACK (other is probably only going to be "Locality")
    Con c -> pp c

  
    RecCon recordDD inst -> pp recordDD <+> ppRecordMems inst
    RecUpdate c upd -> c <+> ppRecordMems upd
    MemAccess c mem -> c <> "." <> pp mem

    Op l op r -> l <+> ppOp op <+> r
    Call f args -> f <> Def.encloseSepBy "(" ")" ", " args
    As x at -> x <+> "as" <+> pp at
    Lam extra params e -> pp extra <+> Def.encloseSepBy "(" ")" ", " (map pp params) <> ":" <+> e
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
  (PP expr, PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase))
  => PP (CaseF phase expr (AnnStmt phase)) where
  pp kase = Def.ppBody' pp (pp kase.deconstruction <+?> fmap pp kase.caseCondition) kase.caseBody

instance
  (PP (XMem phase), PP (XLVar phase), PP (XCon phase), PP (XTCon phase))
  => PP (Decon phase) where
  pp = cata $ \case
    CaseVariable uv -> pp uv
    CaseConstructor uc [] -> pp uc
    CaseConstructor uc args@(_:_) -> pp uc <> Def.encloseSepBy "(" ")" ", " args
    CaseRecord recordDD args -> pp recordDD <+> ppRecordMems args

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

instance (PP (XEnv phase), PP (XFunVar phase), PP (XLVar phase), PP (XMem phase), PP (XCon phase), PP (XTVar phase), PP (XTCon phase)) => PP (FunDec phase) where
  pp (FD fenv v params retType) = do
    pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> pp pName <+?> fmap pp pType) params) <+?> fmap pp retType

instance
  (PP (XVar phase), PP (XLVar phase), PP (XFunVar phase), PP (XCon phase), PP (XEnv phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XTVar phase), PP (XClass phase), PP (XTCon phase), PP (XVarOther phase), PP (XLamOther phase))
  => PP (InstDef phase) where
  pp inst =
    let
      header = "inst" <+> pp inst.instClass <+> pp (fst inst.instType) <+> Def.sepBy " " (pp <$> snd inst.instType)
    in Def.ppBody
      (\ifn -> Def.ppBody' pp (pp ifn.instFunDec) ifn.instFunBody)
      header
      inst.instFuns


instance (PP (XTVar phase), PP (XTCon phase), PP (XMem phase), PP (XDCon phase), PP (XCon phase), PP (XDTCon phase)) => PP (DataDef phase) where
  pp (DD tid tvs (Right dcons) _) = Def.ppBody pp (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) dcons
  pp (DD tid tvs (Left mems) _) = Def.ppBody (\(Annotated _ (mem, t)) -> pp mem <+> pp t) (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) $ NonEmpty.toList mems

instance (PP (XTVar phase), PP (XDCon phase), PP (XTCon phase), PP (XCon phase)) => PP (DataCon phase) where
  pp (DC _ g t _) = foldl' (<+>) (pp g) $ tTypes t

tTypes :: (PP (XTVar phase), PP (XTCon phase), Functor t) => t (Type phase) -> t Def.Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> pp t
  where
    enclose x = "(" <> pp x <> ")"


-- instance (PP (XTVar phase), PP (XTCon phase), PP (XMem phase)) => PP (DataRec phase) where
--   pp (DR tid tvs recs _) = Def.ppBody' tRec (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) recs
--     where
--       tRec (Def.Annotated ann (mem, t)) = Def.annotate ann (pp mem <+> pp t)

instance PP (TVar phase) where
  pp tv =
    let bindingCtx = case tv.binding of
          Def.BindByType ut -> pp ut.typeName
          Def.BindByVar uv -> pp uv.varName
          Def.BindByInst uc -> pp uc.className
    in pp tv.fromTV <> "<" <> bindingCtx <> ">"

instance (PP (XClass phase), PP (XDClass phase), PP (XFunVar phase), PP (XLVar phase), PP (XMem phase), PP (XTVar phase), PP (XCon phase), PP (XTCon phase)) => PP (ClassDef phase) where
  pp c = Def.ppBody pp (pp c.classID) c.classFunctions

instance (PP (XLVar phase), PP (XFunVar phase), PP (XMem phase), PP (XTVar phase), PP (XCon phase), PP (XTCon phase)) => PP (ClassFunDec phase) where
  pp (CFD _ v params ret) = pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pDecon, pType) -> pp pDecon <+> pp pType) params) <+> pp ret

instance (PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XTVar phase), PP (XVar phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (XEnv phase), PP (XFunVar phase)) => PP (Function phase) where
  pp fn = Def.ppBody' pp (pp fn.functionDeclaration) fn.functionBody
