{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module ASTPrettyPrinter (ppModule, ppShow) where

import Prettyprinter
import AST

import Data.Set (Set)
import qualified Data.Set as S
import Data.Fix (Fix (Fix))
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Functor.Foldable (cata, Base)
import Data.Bifunctor (first)
import Control.Monad.Trans.Reader (ReaderT, Reader, runReader)
import Control.Monad.Trans.Class (lift)
import Control.Applicative (liftA2)
import Data.Functor ((<&>))
import Data.Bitraversable (Bitraversable(bitraverse))
import Data.Text (Text)


data Context' = Context
type Context = Reader Context' (Doc ())  -- Annotaion is, for now, '()'. This will be used for stuff like syntax coloring,

instance Semigroup Context where
  l <> r = do
    l' <- l
    r' <- r
    pure $ l' <> r'

instance Monoid Context where
  mempty = pure mempty

class PrettyPrintable a where
  pp :: a -> Context

  default pp :: Show a => a -> Context
  pp = pure . pretty . show

instance PrettyPrintable Global where
  pp g = pure $ "G" <> pretty (show g)

instance PrettyPrintable Local where
  pp l = pure $ "L" <> pretty (show l)

instance PrettyPrintable TypeID where
  pp t = pure $ "T" <> pretty (show t)

instance PrettyPrintable Text where
  pp = pure . pretty

instance PrettyPrintable Context where
  pp = id


instance PrettyPrintable a => PrettyPrintable [a] where
  pp = fmap vsep . traverse pp

instance PrettyPrintable a => PrettyPrintable (Set a) where
  pp = pp . S.toList

instance PrettyPrintable a => PrettyPrintable (NonEmpty a) where
  pp = pp . NE.toList

instance PrettyPrintable a => PrettyPrintable (Maybe a) where
  pp (Just x) = pp x
  pp Nothing = mempty

instance (PrettyPrintable e, PrettyPrintable a) => PrettyPrintable (Either e a) where
  pp (Left e) = ("Left" <+>) <$> pp e
  pp (Right a) = ("Right" <+>) <$> pp a

instance (PrettyPrintable e, PrettyPrintable a) => PrettyPrintable (e, a) where
  pp (e, a) = liftA2 (\e a -> "(" <> e <> "," <+> a <> ")") (pp e) (pp a)

nest' :: Context -> Context -> Context
nest' header = (header <>) . fmap (nest 4 . (line <>))

ppNest :: PrettyPrintable a => Context -> a -> Context
ppNest header = nest' header . pp


instance PrettyPrintable t => PrettyPrintable (Type t) where
  pp = cata $ \case
    TCon con [] -> pp con
    TCon con ts -> liftA2 (\con ts -> "(" <> con <+> hsep ts <> ")") (pp con) (sequenceA ts)
    TVar (TV tv) -> pure $ pretty tv
    TFun args ret -> liftA2 (\args ret -> enclose "<" ">" (hsep (punctuate "," args)) <+> "->" <+> ret) (sequenceA args) ret
    TDecVar (TV tv) -> pure $ pretty tv

instance PrettyPrintable TExpr where
  pp = cata $ \(ExprType t expr) -> (\t expr -> hsep ["(", expr, "::", t,  ")"]) <$> pp t <*> ppExpr expr

instance (PrettyPrintable g, PrettyPrintable tid)
  => PrettyPrintable (DataCon g tid) where
    pp (DC g ts) = (\g ts -> "ctor '" <> g <> "':" <+> hsep ts) <$> pp g <*> traverse pp ts

instance (PrettyPrintable g, PrettyPrintable tid, PrettyPrintable con)
  => PrettyPrintable (DataDec g tid con) where
  pp (DD tid tvs cons) = flip ppNest cons $
      (\tid tvs -> "data" <+> tid <+> hsep tvs) <$> pp tid <*> traverse (\(TV tv) -> pure $ pretty tv) tvs

instance PrettyPrintable MonoDataDec where
  pp (MonoDataDec g apps) = (\g apps -> "data" <+> "dec" <+> g <+> apps) <$> pp g <*> pp apps


instance PrettyPrintable Op where
  pp = pure . \case
    Plus -> "+"
    Minus -> "-"
    Times -> "*"
    Divide -> "/"

    Equals -> "=="
    NotEquals -> "/="


instance (PrettyPrintable g, PrettyPrintable l) => PrettyPrintable (Expr l g) where
  pp = cata ppExpr

ppExpr :: (PrettyPrintable g, PrettyPrintable l) => ExprF g l Context -> Context
ppExpr = \case
    Lit lt -> case lt of
      LBool x -> pure $ pretty x
      LInt x -> pure $ pretty x

    Var egl -> either pp pp egl
    Op l op r -> (\l op r -> hsep ["(", l, op, r, ")"]) <$> l <*> pp op <*> r
    Call c args -> (\c args -> c <+> encloseSep "(" ")" "," args) <$> c <*> sequenceA args
    Lam params expr -> fmap (hsep . punctuate comma) (traverse pp params) <> pure (colon <> space) <> expr


instance (PrettyPrintable expr, PrettyPrintable l, PrettyPrintable g) => PrettyPrintable (Stmt l g expr) where
  pp = cata $ go . first pp
    where
      go :: (PrettyPrintable l, PrettyPrintable g) => Base (Stmt l g Context) Context -> Context
      go = \case
        ExprStmt expr -> expr
        Print expr -> ("print" <+>) <$> expr
        Assignment name expr -> (\name expr -> name <+> "=" <+> expr) <$> pp name <*> expr
        If cond ifTrue elseIfs ifFalse -> do
          cond' <- cond
          ifTrue' <- nest' (("if" <+>) <$> cond) (vsep . NE.toList <$> sequenceA ifTrue)
          elseIfs' <- vsep <$> traverse (\(c, b) -> nest' (("elif" <+>) <$> c) (vsep . NE.toList <$> sequenceA b)) elseIfs
          ifFalse' <- maybe (pure "") (nest' (pure "else") . fmap (vsep . NE.toList) . sequenceA) ifFalse
          return $ vsep
            [ ifTrue'
            , elseIfs'
            , ifFalse'
            ]
        Return expr -> ("return" <+>) <$> expr


instance PrettyPrintable MonoFunDec

instance (PrettyPrintable g, PrettyPrintable l, PrettyPrintable t, PrettyPrintable stmt)
  => PrettyPrintable (FunDec g l t stmt) where
  pp (FD name params ret stmts) = do
    name <- pp name
    params <- traverse (\(param, pType) -> (\p t -> p <> ":" <+> t) <$> pp param <*> pp pType) params
    ret <- pp ret
    flip ppNest stmts $ pure $
      name <+> encloseSep "(" ")" "," params <+> "->" <+> ret

instance PrettyPrintable RModule where
  pp (RModule { rmFunctions, rmDataDecs, rmTLStmts }) = do
    funs <- pp (fmap (<> line) . pp <$> S.toList rmFunctions)
    dds <- pp rmDataDecs
    stmts <- pp rmTLStmts
    return $ vsep [funs, dds, stmts]

instance PrettyPrintable TModule where
  pp (TModule funs dds stmts) = do
    funs <- pp (fmap (<> line) . pp <$> S.toList funs)
    dds <- pp dds
    stmts <- pp stmts
    return $ vsep [funs, dds, stmts]
  
instance PrettyPrintable MModule where
  pp (MModule dds funs stmts) = do
    funs <- pp (fmap (<> line) . pp <$> funs)
    dds <- pp dds
    stmts <- pp stmts
    return $ vsep [funs, dds, stmts]

-- Additional line when printing a list of TopLevels.
instance PrettyPrintable TopLevel where
  pp (FunDec fd) = pp fd
  pp (DataDec dd) = pp dd
  pp (TLStmt stmt) = pp stmt

ppModule :: Context' -> RModule -> String
ppModule ctx = show . flip runReader ctx . pp

ppShow :: PrettyPrintable a => Context' -> a -> String
ppShow ctx = show . flip runReader ctx . pp
