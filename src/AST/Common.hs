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
{-# LANGUAGE StandaloneDeriving #-}
module AST.Common (module AST.Common) where

import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import Data.Fix (Fix (..))
import AST.Def ((:.) (..), Annotated (..), PP (..), (<+>), Op (..), (<+?>), UniqueVar, PPDef (..))
import Data.Functor.Foldable (cata, Recursive (..))
import Data.Foldable (foldl')
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Eq.Deriving (makeLiftEq)
import Data.Ord.Deriving (makeLiftCompare)
import Data.Bifunctor (first)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Text (Text)
import Data.Set (Set)
import Data.Map (Map, (!?))
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Functor.Classes (Eq1 (..), Ord1 (..))


type family Rec phase a

-- Naming scheme:
-- X<name>  <- reference to actual datatype
-- XD<name> <- ID of that datatype


type family XTCon phase
type family XTVar phase
type family XTOther phase
type family XTFun phase
type family XTConOther phase

data TypeF phase a
  = TFun (XTFun phase) [a] a
  | TCon (XTCon phase) [a] (XTConOther phase)
  | TO (XTOther phase)  -- BAD, becuase in Mono it makes it less typesafe, but it's kinda easier. I just won't ever construct it in Mono.
  deriving (Functor, Foldable, Traversable)

pure []  -- NOTE: TH shit
instance (Eq (XTFun phase), Eq (XTCon phase), Eq (XTConOther phase), Eq (XTOther phase)) => Eq1 (TypeF phase) where
  liftEq = $(makeLiftEq ''TypeF)

instance (Ord (XTFun phase), Ord (XTCon phase), Ord (XTConOther phase), Ord (XTOther phase)) => Ord1 (TypeF phase) where
  liftCompare = $(makeLiftCompare ''TypeF)

deriving instance (Eq a, Eq (XTFun phase), Eq (XTCon phase), Eq (XTConOther phase), Eq (XTOther phase)) => Eq (TypeF phase a)
deriving instance (Ord a, Ord (XTFun phase), Ord (XTCon phase), Ord (XTConOther phase), Ord (XTOther phase)) => Ord (TypeF phase a)


type Type phase = Fix (TypeF phase)


-- Used only in Typecheck and beyond.
data WithType phase a = Typed (Type phase) a


type IsEmpty = Bool

type family XEnv phase
type family XEnvUnion phase

type family XVar phase
type family XVarOther phase
type family XCon phase
type family XConOther phase
type family XMem phase
type family XLamVar phase
type family XLamOther phase

type family XNode phase
data Node phase nodeF a = N (XNode phase) (nodeF phase a) deriving (Functor, Foldable, Traversable)

-- Basically, get extra information in node.
-- I only have plans for a type in node, so i can call this function that way if I want.
typeOfNode :: Fix (Node phase nodeF) -> XNode phase
typeOfNode (Fix (N t _)) = t


data ExprF phase a
  = Lit Def.LitType  -- NOTE: all these types are not set in stone. If I need to change it later (to be dependent on phase) then I should do it.
  | Var (XVar phase) (XVarOther phase)
  | Con (XCon phase) (XConOther phase)

  | RecCon (XTCon phase) (NonEmpty (XMem phase, a))
  | RecUpdate a (NonEmpty (XMem phase, a))
  | MemAccess a (XMem phase)

  | Op a Def.Op a
  | Call a [a]
  | As a (Type phase)
  | Lam (XLamOther phase) [XLamVar phase] a
  deriving (Functor, Foldable, Traversable)
type Expr phase = Fix (Node phase ExprF)


---------------
-- Data Defs --
---------------

type family XDCon phase

data DataCon phase = DC
  { conDataDef :: Rec phase (DataDef phase)
  , conID :: XDCon phase
  , conTypes :: [Type phase]
  , conAnns :: [Def.Ann]
  }


type family XDTCon phase
type family XDataScheme phase
type Mem phase = Annotated (XMem phase, Type phase)

data DataDef phase = DD
  { ddName :: XDTCon phase
  , ddScheme  :: XDataScheme phase
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
type Decon phase = Fix (Node phase DeconF)

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
  , ifElifs     :: [(expr, NonEmpty a)]
  , ifElse     :: Maybe (NonEmpty a)
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

$(deriveBitraversable ''IfStmt)
$(deriveBitraversable ''CaseF)
$(deriveBitraversable ''StmtF)

--------------
-- Function --
--------------

type family XFunVar phase
type family XFunOther phase

type family XFunType phase
data DeclaredType phase  -- a separate datatype to basically allow easy pretty printing
  = TypeNotDeclared
  | DeclaredType (Type phase)

data FunDec phase = FD
  { functionEnv :: XEnv phase
  , functionId :: XFunVar phase
  , functionParameters :: [(Decon phase, XFunType phase)]
  , functionReturnType :: XFunType phase
  , functionOther :: XFunOther phase
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
type family XClassFunDec phase

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
  , instClassFunDec :: Rec phase (XClassFunDec phase)
  , instDef :: Rec phase (InstDef phase)
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


-----------
-- Extra --
-----------

isTypeDeclared :: DeclaredType phase -> Bool
isTypeDeclared = \case
  TypeNotDeclared -> False
  DeclaredType _ -> True

fromMaybeToDeclaredType :: Maybe (Type phase) -> DeclaredType phase
fromMaybeToDeclaredType = \case
  Nothing -> TypeNotDeclared
  Just t -> DeclaredType t

fromDeclaredTypeToMaybe :: DeclaredType phase -> Maybe (Type phase)
fromDeclaredTypeToMaybe = \case
  TypeNotDeclared -> Nothing
  DeclaredType t -> Just t

catNotDeclared :: [DeclaredType phase] -> [Type phase]
catNotDeclared = mapMaybe fromDeclaredTypeToMaybe

defaultEmpty :: (Monoid v, Ord k) => k -> Map k v -> v
defaultEmpty k m = fromMaybe mempty $ m !? k

instanceToFunction :: InstFun a -> Function a
instanceToFunction instdef = Function instdef.instFunDec instdef.instFunBody

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

instance Ord (XDCon phase) => Ord (DataCon phase) where
  DC _ uc _ _ `compare` DC _ uc' _ _ = uc `compare` uc'

instance Eq (XDTCon phase) => Eq (DataDef phase) where
  DD ut _ _ _ == DD ut' _ _ _ = ut == ut'

instance Ord (XDTCon phase) => Ord (DataDef phase) where
  DD ut _ _ _ `compare` DD ut' _ _ _ = ut `compare` ut'



--------------------
-- Printing stuff --
--------------------

-- instance (PP (XLVar phase), PP (XTVar phase), PP (XVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (Type phase), PP expr, PP (CaseF phase Def.Context (Fix (Annotated :. StmtF phase expr)))) => PP (Fix (Annotated :. StmtF phase expr)) where
--   pp (Fix (O (Def.Annotated ann stmt))) = Def.annotate ann $ pp stmt

instance (PP a, PP expr, PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XNode phase)) => PP (StmtF phase expr a) where
  pp stmt = case first pp stmt of
    Print e -> "print" <+> e
    Assignment v e -> pp v <+> "=" <+> e
    Pass -> "pass"
    Mutation v e -> pp v <+> "<=" <+> e
    If ifs ->
      Def.ppBody' pp ("if" <+> ifs.condition) ifs.ifTrue <>
      foldMap (\(cond, elseIf) ->
          Def.ppBody' pp ("elif" <+> cond) elseIf) ifs.ifElifs <>
      maybe mempty (Def.ppBody' pp "else") ifs.ifElse
    Switch switch cases ->
      Def.ppBody' pp switch cases
    ExprStmt e -> e
    Return e -> "return" <+> pp e
    Fun fd -> pp fd
    Inst idef -> pp idef
    Other other -> pp other
    -- EnvDef fn -> fromString $ printf "[ENV]: %s" $ tEnv fn.functionDeclaration.functionEnv
    -- InstDefDef inst -> tInst inst

instance (PP a, PP (XCon phase), PP (XVar phase), PP (XTCon phase), PP (XMem phase), PP (XVarOther phase), PP (XLamOther phase), PP (Type phase), PP (XLamVar phase)) => PP (ExprF phase a) where
  pp expr = case pp <$> expr of
    Lit l -> pp l
    Var v other -> pp other <> pp v  -- HACK (other is probably only going to be "Locality")
    Con c _ -> pp c


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
  (PP a, PP expr, PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XNode phase)) => PP (CaseF phase expr a) where
  pp kase = Def.ppBody' pp (pp kase.deconstruction <+?> fmap pp kase.caseCondition) kase.caseBody

instance (PP (XMem phase), PP (XLVar phase), PP (XCon phase), PP (XTCon phase)) => PPDef (Decon phase) where
  ppDef = cata ppDef

instance (PP (nodeF phase a), PP (XNode phase)) => PP (Node phase nodeF a) where
  pp (N xn n) = "(" <> pp n <+> "::" <+> pp xn <> ")"

instance (PP (nodeF phase a)) => PPDef (Node phase nodeF a) where
  ppDef (N _ n) = pp n

instance
  (PP (XMem phase), PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP a)
  => PP (DeconF phase a) where
  pp = \case
    CaseVariable uv -> pp uv
    CaseConstructor uc [] -> pp uc
    CaseConstructor uc args@(_:_) -> pp uc <> Def.encloseSepBy "(" ")" ", " (pp <$> args)
    CaseRecord recordDD args -> pp recordDD <+> ppRecordMems  (Def.fmap2 pp args)

instance (PPDef (XTCon phase), PP (XTOther phase), PP (XTFun phase)) => PP (Type phase) where
  pp = para $ \case
    TCon tcon params _ ->
      foldl' (<+>) (ppDef tcon) (ppEnclosable <$> params)
    TO x -> pp x
    TFun tfOther args ret -> pp tfOther <> Def.encloseSepBy "(" ")" ", " (snd <$> args) <+> "->" <+> snd ret
    where
      -- ppEnclosable :: (Type phase, Def.Context) -> Def.Context
      ppEnclosable (t, c) = case project t of
        TCon _ (_:_) _ -> "(" <> c <> ")"
        TFun {} -> "(" <> c <> ")"
        _ -> c

-- it shit
instance (PPDef (XTCon phase), PP (XTOther phase), PP (XTFun phase)) => PP (ClassType phase) where
  pp = para $ \case
    Self -> "_"
    NormalType nt -> case nt of
      TCon tcon params _ ->
        foldl' (<+>) (ppDef tcon) (ppEnclosable <$> params)
      TO x -> pp x
      TFun tfOther args ret -> pp tfOther <> Def.encloseSepBy "(" ")" ", " (pp <$> args) <+> "->" <+> pp ret
      where
        ppEnclosable (t, c) = case project t of
          NormalType (TCon _ (_:_) _) -> "(" <> c <> ")"
          NormalType (TFun {}) -> "(" <> c <> ")"
          _ -> c

instance (PP (XEnv phase), PP (XFunVar phase), PP (XLVar phase), PP (XMem phase), PP (XCon phase), PP (XTCon phase), PP (XFunType phase)) => PP (FunDec phase) where
  pp (FD fenv v params retType _) = do
    pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> ppDef pName <+> pp pType) params) <+> pp retType <+> pp fenv

instance
  (PP (XVar phase), PP (XLVar phase), PP (XFunVar phase), PP (XCon phase), PP (XEnv phase), PP (XMem phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XTVar phase), PP (XTCon phase), PP (XVarOther phase), PP (XLamOther phase), PP (Type phase), PP (XNode phase), PP (XFunType phase), PPDef (XClass phase), PPDef (XTCon phase), PP (XLamVar phase)) => PP (InstDef phase) where
  pp inst =
    let
      header = "inst" <+> ppDef inst.instClass <+> ppDef (fst inst.instType) <+> Def.sepBy " " (pp <$> snd inst.instType)
    in Def.ppBody
      (\ifn -> Def.ppBody' pp (pp ifn.instFunDec) ifn.instFunBody)
      header
      inst.instFuns


instance (PP (XMem phase), PP (XDCon phase), PP (XDTCon phase), PP (Type phase), PP (XDataScheme phase)) => PP (DataDef phase) where
  pp (DD tid tvs (Right dcons) _) = Def.ppBody pp (pp tid <+> pp tvs) dcons
  pp (DD tid tvs (Left mems) _) = Def.ppBody (\(Annotated _ (mem, t)) -> pp mem <+> pp t) (pp tid <+> pp tvs) $ NonEmpty.toList mems

instance PP (XDTCon phase) => PPDef (DataDef phase) where
  ppDef dd = pp dd.ddName

instance (PP (XDCon phase), PP (Type phase)) => PP (DataCon phase) where
  pp (DC _ g t _) = foldl' (<+>) (pp g) $ pp <$> t

-- tTypes :: (PP (XTVar phase), PP (XTCon phase), Functor t) => t (Type phase) -> t Def.Context
-- tTypes = fmap $ \t@(Fix t') -> case t' of
--   TCon _ (_:_) -> enclose t
--   TFun {} -> enclose t
--   _ -> pp t
--   where
--     enclose x = "(" <> pp x <> ")"


-- instance (PP (XTVar phase), PP (XTCon phase), PP (XMem phase)) => PP (DataRec phase) where
--   pp (DR tid tvs recs _) = Def.ppBody' tRec (foldl' (\x tv -> x <+> pp tv) (pp tid) tvs) recs
--     where
--       tRec (Def.Annotated ann (mem, t)) = Def.annotate ann (pp mem <+> pp t)

instance PP (TVar phase) where
  pp tv =
    let bindingCtx = case tv.binding of
          Def.BindByType ut -> pp ut
          Def.BindByVar uv -> pp uv
          Def.BindByInst uc -> pp uc
    in pp tv.fromTV <> "<" <> bindingCtx <> ">"

instance (PP (XDClass phase), PP (XFunVar phase), PP (XLVar phase), PP (XMem phase), PP (XCon phase), PP (XTCon phase), PP (XNode phase), PPDef (XTCon phase), PP (XTOther phase), PP (XTFun phase)) => PP (ClassDef phase) where
  pp c = Def.ppBody pp (pp c.classID) c.classFunctions

instance (PP (XLVar phase), PP (XFunVar phase), PP (XMem phase), PP (XCon phase), PP (XTCon phase), PP (XNode phase), PPDef (XTCon phase), PP (XTOther phase), PP (XTFun phase)) => PP (ClassFunDec phase) where
  pp (CFD _ v params ret) = pp v <+> Def.encloseSepBy "(" ")" ", " (fmap (\(pDecon, pType) -> pp pDecon <+> pp pType) params) <+> pp ret

instance (PP (XLVar phase), PP (XCon phase), PP (XTCon phase), PP (XMem phase), PP (XVar phase), PP (XReturn phase), PP (XOther phase), PP (XFunDef phase), PP (XInstDef phase), PP (XVarOther phase), PP (XLamOther phase), PP (XEnv phase), PP (XFunVar phase), PP (Type phase), PP (XNode phase), PP (XFunType phase), PP (XLamVar phase)) => PP (Function phase) where
  pp fn = Def.ppBody' pp (pp fn.functionDeclaration) fn.functionBody

instance (PP (XMem phase), PP (XLVar phase), PP (XCon phase), PP (XTCon phase)) => PP (Fix (DeconF phase)) where
  pp = cata pp

instance (PP (XTOther phase), PP (XTFun phase), PPDef (XTCon phase)) => PP (DeclaredType phase) where
  pp = \case
    TypeNotDeclared -> ""
    DeclaredType t -> " " <> pp t  -- HACK: we know the context it's used in, so we add a space whenever there is a type.

instance PP (XDClass phase) => PPDef (ClassDef phase) where
  ppDef cd = pp cd.classID
