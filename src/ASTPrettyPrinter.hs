{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}

module ASTPrettyPrinter (utModule, rModule, tyModule, tModule) where

import Prettyprinter (Doc)
import qualified Prettyprinter as PP
import AST

import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (cata)
import Data.Bifunctor (first)
import Control.Monad.Trans.Reader (Reader, runReader)
import Data.String (IsString, fromString)
import Data.Foldable (fold, foldl')
import Data.List (intersperse)
import Data.Unique (hashUnique)
import Typecheck.Types (TyVared, TypeF' (..), TyVar (..), TyFunEnv, TyFunEnv' (..))


-- Notes: I have changed my strategy to this.
--  Reason: Cannot use type families with typeclasses.
--    Ex.
-- • Illegal type synonym family application ‘Stmt
--                                              Untyped’ in instance:
--     PrettyPrintable (Stmt Untyped)
-- • In the instance declaration for ‘PrettyPrintable (Stmt Untyped)’

--  Solution:
--   I'll just make functions with normal type definitions.
--   For harder/shared type definitions, I'll just leave the type to be autogenerated/leave it out.
--   Not very good, but better than nothing....


-- Module contents:
-- - Main definitions
-- - Phase printers
--   - Untyped (including non-generic instances)
-- - Generic functions
-- - Generic instances

-- Context that stores the pretty printer Doc + data + help with, for example, names.
type Context = Reader CtxData (Doc ())  -- I guess I can add syntax coloring or something with the annotation (the () in Doc)
data CtxData = CtxData  -- basically stuff like printing options or something (eg. don't print types)


-----------
-- Typed --
-----------

tModule :: Module Typed -> String
tModule = show . flip runReader CtxData . tStmts

tStmts :: [AnnStmt Typed] -> Context
tStmts = ppLines tAnnStmt

tAnnStmt :: AnnStmt Typed -> Context
tAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ tStmt stmt

tStmt :: Stmt Typed -> Context
tStmt = \case
  NormalStmt s -> case first tExpr s of
    Print e -> "print" <+> e
    Assignment v e -> rVar v <+> "=" <+> e
    Pass -> "pass"
    MutDefinition v me ->  "mut" <+> rVar v <+?> rhs
      where
        rhs = fmap ("<=" <+>) me
    MutAssignment v e -> rVar v <+> "<=" <+> e
    If ifCond ifTrue elseIfs mElse ->
      tBody ("if" <+> ifCond ) ifTrue <>
      foldMap (\(cond, elseIf) ->
          tBody ("elif" <+> cond) elseIf) elseIfs <>
      maybe mempty (tBody "else") mElse
    ExprStmt e -> e
    Return e -> "return" <+?> e

  DataDefinition dd -> tDataDef dd
  FunctionDefinition fd body -> tBody (tFunDec fd) body


tExpr :: Expr Typed -> Context
tExpr = cata $ \(ExprType t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tType t <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Var v -> rVar v
  Con c -> rCon c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x at -> x <+> "as" <+> tType at
  Lam env params e -> ppVarEnv env <+> sepBy " " (map rVar params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tDataDef :: DataDef Typed -> Context
tDataDef (DD tid tvs cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (rTypeInfo tid) tvs) $ ppLines tConDef cons

tConDef :: DataCon Typed -> Context
tConDef (DC g t ann) = annotate ann $ foldl' (<+>) (rCon g) $ tTypes t

tFunDec :: FunDec Typed -> Context
tFunDec (FD v params env retType) = comment (ppVarEnv env) $ rVar v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> rVar pName <> ((" "<>) . tType) pType) params) <> ((" "<>) . tType) retType


tTypes :: Functor t => t (Type Typed) -> t Context
tTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> tType t
  where
    enclose x = "(" <> tType x <> ")"

tType :: Type Typed -> Context
tType = cata $ \case
  TCon con params -> foldl' (<+>) (rTypeInfo con) params
  TVar (TV tv) -> pretty tv
  TFun env args ret -> ppFunEnv env <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret


tBody :: Foldable f => Context -> f (AnnStmt Typed) -> Context
tBody = ppBody tAnnStmt


-----------
-- Typed Vared --
-----------

tyModule :: Module TyVared -> String
tyModule = show . flip runReader CtxData . tyStmts

tyStmts :: [AnnStmt TyVared] -> Context
tyStmts = ppLines tyAnnStmt

tyAnnStmt :: AnnStmt TyVared -> Context
tyAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ tyStmt stmt

tyStmt :: Stmt TyVared -> Context
tyStmt = \case
  NormalStmt s -> case first tyExpr s of
    Print e -> "print" <+> e
    Assignment v e -> rVar v <+> "=" <+> e
    Pass -> "pass"
    MutDefinition v me ->  "mut" <+> rVar v <+?> rhs
      where
        rhs = fmap ("<=" <+>) me
    MutAssignment v e -> rVar v <+> "<=" <+> e
    If ifCond ifTrue elseIfs mElse ->
      tyBody ("if" <+> ifCond ) ifTrue <>
      foldMap (\(cond, elseIf) ->
          tyBody ("elif" <+> cond) elseIf) elseIfs <>
      maybe mempty (tyBody "else") mElse
    ExprStmt e -> e
    Return e -> "return" <+?> e

  DataDefinition dd -> tyDataDef dd
  FunctionDefinition fd body -> tyBody (tyFunDec fd) body


tyExpr :: Expr TyVared -> Context
tyExpr = cata $ \(ExprType t expr) ->
  let encloseInType c = "(" <> c <+> "::" <+> tyType t <> ")"
  in encloseInType $ case expr of
  Lit (LInt x) -> pretty x
  Var v -> rVar v
  Con c -> rCon c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x at -> x <+> "as" <+> tType at
  Lam env params e -> ppVarEnv env <+> sepBy " " (map rVar params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


tyDataDef :: DataDef TyVared -> Context
tyDataDef (DD tid tvs cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (rTypeInfo tid) tvs) $ ppLines tConDef cons

tyConDef :: DataCon TyVared -> Context
tyConDef (DC g t ann) = annotate ann $ foldl' (<+>) (rCon g) $ tTypes t

tyFunDec :: FunDec TyVared -> Context
tyFunDec (FD v params env retType) = comment (ppVarEnv env) $ rVar v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> rVar pName <> ((" "<>) . tyType) pType) params) <> ((" "<>) . tyType) retType


tyTypes :: Functor t => t (Type TyVared) -> t Context
tyTypes = fmap $ \t@(Fix t') -> case t' of
  TF' (Left _) -> tyType t
  TF' (Right x) -> case x of
        TCon _ (_:_) -> enclose t
        TFun {} -> enclose t
        _ -> tyType t
  where
    enclose x = "(" <> tyType x <> ")"

tyType :: Type TyVared -> Context
tyType = cata $ \case
  TF' (Left tv) -> ppTyVar tv
  TF' (Right x) -> case x of
      TCon con params -> foldl' (<+>) (rTypeInfo con) params
      TVar (TV tv) -> pretty tv
      TFun env args ret -> ppTyFunEnv env <> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

ppTyFunEnv :: TyFunEnv' Context -> Context
ppTyFunEnv (TyFunEnv envid funenv) = ppTyVar envid <> ppFunEnv funenv

ppTyVar :: TyVar -> Context
ppTyVar (TyVar tv) = "#" <> pretty tv

tyBody :: Foldable f => Context -> f (AnnStmt TyVared) -> Context
tyBody = ppBody tyAnnStmt


--------------
-- Resolved --
--------------

rModule :: Module Resolved -> String
rModule = show . flip runReader CtxData . rStmts

rStmts :: [AnnStmt Resolved] -> Context
rStmts = ppLines rAnnStmt


rAnnStmt :: AnnStmt Resolved -> Context
rAnnStmt (Fix (AnnStmt ann stmt)) = annotate ann $ rStmt stmt

-- I'll specify resolved variables as this:
--  (x$idhash:type) 
rStmt :: Stmt Resolved -> Context
rStmt = \case
  NormalStmt s -> case first rExpr s of
    Print e -> "print" <+> e
    Assignment v e -> rVar v <+> "=" <+> e
    Pass -> "pass"
    MutDefinition v me ->  "mut" <+> rVar v <+?> rhs
      where
        rhs = fmap ("<=" <+>) me
    MutAssignment v e -> rVar v <+> "<=" <+> e
    If ifCond ifTrue elseIfs mElse ->
      rBody ("if" <+> ifCond ) ifTrue <>
      foldMap (\(cond, elseIf) ->
          rBody ("elif" <+> cond) elseIf) elseIfs <>
      maybe mempty (rBody "else") mElse
    ExprStmt e -> e
    Return e -> "return" <+?> e

  DataDefinition dd -> rDataDef dd
  FunctionDefinition fd body -> rBody (rFunDec fd) body


rExpr :: Expr Resolved -> Context
rExpr = cata $ \case
  Lit (LInt x) -> pretty x
  Var v -> rVar v
  Con c -> rCon c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x t -> x <+> "as" <+> rType t
  Lam env params e -> ppVarEnv env <+> sepBy " " (map rVar params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="


rDataDef :: DataDef Resolved -> Context
rDataDef (DD tid tvs cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (rTypeInfo tid) tvs) $ ppLines rConDef cons

rConDef :: DataCon Resolved -> Context
rConDef (DC g t ann) = annotate ann $ foldl' (<+>) (rCon g) $ rTypes t

rFunDec :: FunDec Resolved -> Context
rFunDec (FD v params env retType) = comment (ppVarEnv env) $ rVar v <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> rVar pName <> maybe "" ((" "<>) . rType) pType) params) <> maybe "" ((" "<>) . rType) retType


rTypes :: Functor t => t (Type Resolved) -> t Context
rTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> rType t
  where
    enclose x = "(" <> rType x <> ")"

rType :: Type Resolved -> Context
rType = cata $ \case
  TCon con params -> foldl' (<+>) (rTypeInfo con) params
  TVar (TV tv) -> pretty tv
  TFun _ args ret -> encloseSepBy "(" ")" ", " args <+> "->" <+> ret


rVar :: VarInfo -> Context
rVar v = vt <> pretty v.varName <> "$" <> pretty (hashUnique v.varID)
  where
    vt = case v.varType of
      Immutable -> ""
      Mutable -> "*"

-- annotate constructors with '@'
rCon :: ConInfo -> Context
rCon con = "@" <> pretty con.conName <> "$" <> pretty (hashUnique con.conID)

rTypeInfo :: TypeInfo -> Context
rTypeInfo t = pretty t.typeName <> "$" <> pretty (hashUnique t.typeID)


rBody :: Foldable t => Context -> t (AnnStmt Resolved) -> Context
rBody = ppBody rAnnStmt

-------------
-- Untyped --
-------------

utModule :: Module Untyped -> String
utModule = show . flip runReader CtxData . utStmts

utStmts :: [AnnStmt Untyped] -> Context
utStmts = ppLines utAnnStmt

utAnnStmt :: AnnStmt Untyped -> Context
utAnnStmt (Fix (AnnStmt ann stmt)) = ppLines id [ppAnn ann, utStmt stmt]

utStmt :: Stmt Untyped -> Context
utStmt = \case
  NormalStmt s -> case first utExpr s of
    Print e -> "print" <+> e
    Assignment name e -> pretty name <+> "=" <+> e
    Pass -> "pass"
    MutDefinition name me -> "mut" <+> pretty name <+?> rhs
      where
        rhs = fmap ("<=" <+>) me
    MutAssignment name e -> pretty name <+> "<=" <+> e
    If ifCond ifTrue elseIfs mElse ->
      utBody ("if" <+> ifCond ) ifTrue <>
      foldMap (\(cond, elseIf) ->
          utBody ("elif" <+> cond) elseIf) elseIfs <>
      maybe mempty (utBody "else") mElse

    ExprStmt e -> e
    Return e -> "return" <+?> e

  -- Newlines are added to make the special "structures" more visible.
  DataDefinition dd -> utDataDef dd <> "\n"
  FunctionDefinition fd body -> utBody (utFunDec fd) body <> "\n"


utExpr :: Expr Untyped -> Context
utExpr = cata $ \case
  Lit (LInt x) -> pretty x
  Var v -> pretty v
  Con c -> pretty c

  Op l op r -> l <+> ppOp op <+> r
  Call f args -> f <> encloseSepBy "(" ")" ", " args
  As x t -> x <+> "as" <+> utType t
  Lam _ params e -> pretty (sepBy " " params) <> ":" <+> e
  where
    ppOp op = case op of
      Plus -> "+"
      Minus -> "-"
      Times -> "*"
      Divide -> "/"
      Equals -> "=="
      NotEquals -> "/="

utType :: Type Untyped -> Context
utType = cata $ \case
  TCon con params -> foldl' (<+>) (pretty con) params
  TVar (TV tv) -> pretty tv
  TFun _ args ret -> encloseSepBy "(" ")" ", " args <+> "->" <+> ret

-- For printing types in a sequence (in this case, TCons and Functions need parenthesis to distinguish them, that's why)
utTypes :: Functor t => t (Type Untyped) -> t Context
utTypes = fmap $ \t@(Fix t') -> case t' of
  TCon _ (_:_) -> enclose t
  TFun {} -> enclose t
  _ -> utType t
  where
    enclose x = "(" <> utType x <> ")"


utDataDef :: DataDef Untyped -> Context
utDataDef (DD tid tvs cons) = indent (foldl' (\x (TV y) -> x <+> pretty y) (pretty tid) tvs) $ ppLines utConDef cons

utConDef :: DataCon Untyped -> Context
utConDef (DC g t anns) = annotate anns $ foldl' (<+>) (pretty g) $ utTypes t

utFunDec :: FunDec Untyped -> Context
utFunDec (FD name params _ retType) = pretty name <+> encloseSepBy "(" ")" ", " (fmap (\(pName, pType) -> pretty pName <> maybe "" ((" "<>) . utType) pType) params) <> maybe "" ((" "<>) . utType) retType



utBody :: Foldable t => Context -> t (AnnStmt Untyped) -> Context
utBody = ppBody utAnnStmt


ppBody :: Foldable t => (a -> Context) -> Context -> t a -> Context
ppBody f header = indent header . ppLines f


-- Technically should be something like Text for the annotation type, but I need to have access to context in annotations
comment :: Context -> Context -> Context
comment s ctx = "#" <+> s <\> ctx

annotate :: [Ann] -> Context -> Context
annotate [] ctx = ctx
annotate xs ctx = "\n" <> ppAnn xs <\> ctx

encloseSepBy :: Monoid a => a -> a -> a -> [a] -> a
encloseSepBy l r p cs = l <> sepBy p cs <> r

sepBy :: Monoid a => a -> [a] -> a
sepBy p = fold . intersperse p

indent :: Context -> Context -> Context
indent header = (header <>) . fmap (PP.nest 2) . ("\n" <>)

ppLines :: Foldable t => (a -> Context) -> t a -> Context
ppLines f = foldMap ((<>"\n") . f)

ppFunEnv :: FunEnv Context -> Context
ppFunEnv (FunEnv vts) = encloseSepBy "[" "]" " " (fmap (encloseSepBy "[" "]" ", " . fmap (\(v, t) -> rVar v <+> t)) vts)

ppVarEnv :: VarEnv VarInfo -> Context
ppVarEnv (VarEnv vs) = encloseSepBy "$[" "]" " " (fmap rVar vs)

-- ppNoEnv :: NoEnv a -> Context
-- ppNoEnv _ = "[<no env>]"


ppAnn :: [Ann] -> Context
ppAnn [] = mempty
ppAnn anns = "#[" <> sepBy ", " (map ann anns) <> "]"
  where
    ann :: Ann -> Context
    ann = \case
      ACType s -> "ctype" <+> quote s
      ACStdInclude s -> "cstdinclude" <+> quote s
      ACLit s -> "clit" <+> quote s

    quote = pure . PP.squotes . PP.pretty


infixr 6 <+>
(<+>) :: Context -> Context -> Context
x <+> y = liftA2 (PP.<+>) x y

infixr 6 <+?>
(<+?>) :: Context -> Maybe Context -> Context
x <+?> Nothing = x
x <+?> Just y = x <+> y

infixr 5 <\>
(<\>) :: Context -> Context -> Context
x <\> y = x <> "\n" <> y



instance Semigroup Context where
  x <> y = liftA2 (<>) x y

instance Monoid Context where
  mempty = pure mempty

instance IsString Context where
  fromString = pretty

pretty :: PP.Pretty a => a -> Context
pretty = pure . PP.pretty


-- Reminisce about the old, bygone era.

-- class PrettyPrintable a where
--   pp :: a -> Context

--   default pp :: Show a => a -> Context
--   pp = pure . pretty . show


-- instance Semigroup Context where
--   l <> r = do
--     l' <- l
--     r' <- r
--     pure $ l' <> r'

-- instance Monoid Context where
--   mempty = pure mempty

-- class PrettyPrintable a where
--   pp :: a -> Context

--   default pp :: Show a => a -> Context
--   pp = pure . pretty . show

-- instance PrettyPrintable Global where
--   pp g = pure $ "G" <> pretty (show g)

-- instance PrettyPrintable Local where
--   pp l = pure $ "L" <> pretty (show l)

-- instance PrettyPrintable TypeID where
--   pp t = pure $ "T" <> pretty (show t)

-- instance PrettyPrintable Text where
--   pp = pure . pretty

-- instance PrettyPrintable Context where
--   pp = id


-- instance PrettyPrintable a => PrettyPrintable [a] where
--   pp = fmap vsep . traverse pp

-- instance PrettyPrintable a => PrettyPrintable (Set a) where
--   pp = pp . S.toList

-- instance PrettyPrintable a => PrettyPrintable (NonEmpty a) where
--   pp = pp . NE.toList

-- instance PrettyPrintable a => PrettyPrintable (Maybe a) where
--   pp (Just x) = pp x
--   pp Nothing = mempty

-- instance (PrettyPrintable e, PrettyPrintable a) => PrettyPrintable (Either e a) where
--   pp (Left e) = ("Left" <+>) <$> pp e
--   pp (Right a) = ("Right" <+>) <$> pp a

-- instance (PrettyPrintable e, PrettyPrintable a) => PrettyPrintable (e, a) where
--   pp (e, a) = liftA2 (\e a -> "(" <> e <> "," <+> a <> ")") (pp e) (pp a)

-- nest' :: Context -> Context -> Context
-- nest' header = (header <>) . fmap (nest 4 . (line <>))

-- ppNest :: PrettyPrintable a => Context -> a -> Context
-- ppNest header = nest' header . pp


-- instance PrettyPrintable t => PrettyPrintable (Type t) where
--   pp = cata $ \case
--     TCon con [] -> pp con
--     TCon con ts -> liftA2 (\con ts -> "(" <> con <+> hsep ts <> ")") (pp con) (sequenceA ts)
--     TVar (TV tv) -> pure $ pretty tv
--     TFun args ret -> liftA2 (\args ret -> enclose "<" ">" (hsep (punctuate "," args)) <+> "->" <+> ret) (sequenceA args) ret
--     TDecVar (TV tv) -> pure $ pretty tv

-- instance PrettyPrintable TExpr where
--   pp = cata $ \(ExprType t expr) -> (\t expr -> hsep ["(", expr, "::", t,  ")"]) <$> pp t <*> ppExpr expr

-- instance (PrettyPrintable g, PrettyPrintable tid)
--   => PrettyPrintable (DataCon g tid) where
--     pp (DC g ts) = (\g ts -> "ctor '" <> g <> "':" <+> hsep ts) <$> pp g <*> traverse pp ts

-- instance (PrettyPrintable g, PrettyPrintable tid, PrettyPrintable con)
--   => PrettyPrintable (DataDec g tid con) where
--   pp (DD tid tvs cons) = flip ppNest cons $
--       (\tid tvs -> "data" <+> tid <+> hsep tvs) <$> pp tid <*> traverse (\(TV tv) -> pure $ pretty tv) tvs

-- instance PrettyPrintable MonoDataDec where
--   pp (MonoDataDec g apps) = (\g apps -> "data" <+> "dec" <+> g <+> apps) <$> pp g <*> pp apps


-- instance PrettyPrintable Op where
--   pp = pure . \case
--     Plus -> "+"
--     Minus -> "-"
--     Times -> "*"
--     Divide -> "/"

--     Equals -> "=="
--     NotEquals -> "/="


-- instance (PrettyPrintable g, PrettyPrintable l) => PrettyPrintable (Expr l g) where
--   pp = cata ppExpr

-- ppExpr :: (PrettyPrintable g, PrettyPrintable l) => ExprF g l Context -> Context
-- ppExpr = \case
--     Lit lt -> case lt of
--       LBool x -> pure $ pretty x
--       LInt x -> pure $ pretty x

--     Var egl -> either pp pp egl
--     Op l op r -> (\l op r -> hsep ["(", l, op, r, ")"]) <$> l <*> pp op <*> r
--     Call c args -> (\c args -> c <+> encloseSep "(" ")" "," args) <$> c <*> sequenceA args
--     Lam params expr -> fmap (hsep . punctuate comma) (traverse pp params) <> pure (colon <> space) <> expr


-- instance (PrettyPrintable expr, PrettyPrintable l, PrettyPrintable g) => PrettyPrintable (Stmt l g expr) where
--   pp = cata $ go . first pp
--     where
--       go :: (PrettyPrintable l, PrettyPrintable g) => Base (Stmt l g Context) Context -> Context
--       go = \case
--         ExprStmt expr -> expr
--         Print expr -> ("print" <+>) <$> expr
--         Assignment name expr -> (\name expr -> name <+> "=" <+> expr) <$> pp name <*> expr
--         If cond ifTrue elseIfs ifFalse -> do
--           cond' <- cond
--           ifTrue' <- nest' (("if" <+>) <$> cond) (vsep . NE.toList <$> sequenceA ifTrue)
--           elseIfs' <- vsep <$> traverse (\(c, b) -> nest' (("elif" <+>) <$> c) (vsep . NE.toList <$> sequenceA b)) elseIfs
--           ifFalse' <- maybe (pure "") (nest' (pure "else") . fmap (vsep . NE.toList) . sequenceA) ifFalse
--           return $ vsep
--             [ ifTrue'
--             , elseIfs'
--             , ifFalse'
--             ]
--         Return expr -> ("return" <+>) <$> expr


-- instance PrettyPrintable MonoFunDec

-- instance (PrettyPrintable g, PrettyPrintable l, PrettyPrintable t, PrettyPrintable stmt)
--   => PrettyPrintable (FunDec g l t stmt) where
--   pp (FD name params ret stmts) = do
--     name <- pp name
--     params <- traverse (\(param, pType) -> (\p t -> p <> ":" <+> t) <$> pp param <*> pp pType) params
--     ret <- pp ret
--     flip ppNest stmts $ pure $
--       name <+> encloseSep "(" ")" "," params <+> "->" <+> ret

-- instance PrettyPrintable RModule where
--   pp (RModule { rmFunctions, rmDataDecs, rmTLStmts }) = do
--     funs <- pp (fmap (<> line) . pp <$> S.toList rmFunctions)
--     dds <- pp rmDataDecs
--     stmts <- pp rmTLStmts
--     return $ vsep [funs, dds, stmts]

-- instance PrettyPrintable TModule where
--   pp (TModule funs dds stmts) = do
--     funs <- pp (fmap (<> line) . pp <$> S.toList funs)
--     dds <- pp dds
--     stmts <- pp stmts
--     return $ vsep [funs, dds, stmts]

-- instance PrettyPrintable MModule where
--   pp (MModule dds funs stmts) = do
--     funs <- pp (fmap (<> line) . pp <$> funs)
--     dds <- pp dds
--     stmts <- pp stmts
--     return $ vsep [funs, dds, stmts]

-- -- Additional line when printing a list of TopLevels.
-- instance PrettyPrintable TopLevel where
--   pp (FunDec fd) = pp fd
--   pp (DataDec dd) = pp dd
--   pp (TLStmt stmt) = pp stmt

-- ppModule :: Context' -> RModule -> String
-- ppModule ctx = show . flip runReader ctx . pp

-- ppShow :: PrettyPrintable a => Context' -> a -> String
-- ppShow ctx = show . flip runReader ctx . pp
