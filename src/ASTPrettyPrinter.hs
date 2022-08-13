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


class PrettyPrintable a where
  pp :: a -> Doc String

  default pp :: Show a => a -> Doc String
  pp = pretty . show

instance PrettyPrintable Global where
  pp g = "G" <> pretty (show g)

instance PrettyPrintable Local where
  pp l = "L" <> pretty (show l)

instance PrettyPrintable TypeID where
  pp (TypeID t) = "T" <> pretty t


instance PrettyPrintable a => PrettyPrintable [a] where
  pp = vsep . fmap pp

instance PrettyPrintable a => PrettyPrintable (Set a) where
  pp = pp . S.toList

instance PrettyPrintable a => PrettyPrintable (NonEmpty a) where
  pp = pp . NE.toList

instance PrettyPrintable a => PrettyPrintable (Maybe a) where
  pp (Just x) = pp x
  pp Nothing = mempty

nest' :: Doc ann -> Doc ann -> Doc ann
nest' header = (header <>) . nest 4 . (line <>)

ppNest :: PrettyPrintable a => Doc String -> a -> Doc String
ppNest header = nest' header . pp


instance PrettyPrintable t => PrettyPrintable (Type t) where
  pp = cata $ \case
    TCon con [] -> pp con
    TCon con ts -> "(" <> pp con <+> hsep ts <> ")"
    TVar (TV tv) -> pretty tv
    TFun args ret -> "(" <> hsep (punctuate "," args) <+> "->" <+> ret <> ")"

instance PrettyPrintable TExpr where
  pp = cata $ \(ExprType t expr) -> hsep ["(", pp t <> ":", ppExpr expr, ")"]

instance (PrettyPrintable g, PrettyPrintable tid)
  => PrettyPrintable (DataCon g tid) where
    pp (DC g ts) = "ctor '" <> pp g <> "':" <+> hsep (fmap pp ts)

instance (PrettyPrintable g, PrettyPrintable tid, PrettyPrintable con)
  => PrettyPrintable (DataDec g tid con) where
  pp (DD tid tvs cons) = flip ppNest cons $
      "data" <+> pp tid <+> hsep (fmap (\(TV tv) -> pretty tv) tvs)


instance PrettyPrintable Op where
  pp = \case
    Plus -> "+"
    Minus -> "-"
    Times -> "*"
    Divide -> "/"

    Equals -> "=="
    NotEquals -> "/="


instance (PrettyPrintable g, PrettyPrintable l) => PrettyPrintable (Expr l g) where
  pp = cata ppExpr

ppExpr :: (PrettyPrintable g, PrettyPrintable l) => ExprF (Either g l) (Doc String) -> Doc String
ppExpr = \case
    Lit lt -> case lt of
      LBool x -> pretty x
      LInt x -> pretty x
    
    Var egl -> either pp pp egl 
    Op l op r -> hsep ["(", l, pp op, r, ")"]
    Call c args -> c <+> encloseSep "(" ")" "," args

instance (PrettyPrintable expr, PrettyPrintable l, PrettyPrintable g) => PrettyPrintable (Stmt l g expr) where
  pp = cata $ go . first pp
    where
      go = \case
        ExprStmt expr -> expr
        Print expr -> "print" <+> expr
        Assignment name expr -> pp name <+> "=" <+> expr
        If cond ifTrue elseIfs ifFalse -> vsep
          [ nest' ("if" <+> cond) (vsep (NE.toList ifTrue))
          , vsep (map (\(c, b) -> nest' ("elif" <+> c) (vsep (NE.toList b))) elseIfs)
          , maybe "" (nest' "else" . vsep . NE.toList) ifFalse
          ]
        Return expr -> "return" <+> expr

instance (PrettyPrintable g, PrettyPrintable l, PrettyPrintable t, PrettyPrintable stmt)
  => PrettyPrintable (FunDec g l t stmt) where
  pp (FD name params ret stmts) = flip ppNest stmts $
    pp name <+> encloseSep "(" ")" "," (map (\(param, pType) -> pp param <> ":" <+> pp pType) params) <+> "->" <+> pp ret

instance PrettyPrintable RModule where
  pp (RModule { rmFunctions, rmDataDecs, rmTLStmts }) = vsep [pp rmFunctions, pp rmDataDecs, pp rmTLStmts]

instance PrettyPrintable TModule where
  pp (TModule funs dds stmts) = vsep [pp funs, pp dds, pp stmts]

ppModule :: RModule -> String
ppModule = show . pp

ppShow :: PrettyPrintable a => a -> String
ppShow = show . pp
