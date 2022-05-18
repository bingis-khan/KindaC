{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module CPrettyPrinter (pp) where

import AST

import Prettyprinter
import Data.Functor.Foldable (cata)
import Data.Biapplicative (first, bimap)
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Foldable (foldl')
import Data.Semigroup (sconcat)
import Data.Maybe (fromMaybe)

import Data.Map ((!), (!?))


-- Todo: make a class for pretty printing
ppOp :: Op -> Doc String
ppOp = \case
  Plus -> "+"
  Minus -> "-"
  Times -> "*"
  Divide -> "/"
  Equals -> "=="
  NotEquals -> "!="

ppVar :: Either Global Local -> Doc String
ppVar (Right (Local l)) = pretty $ "loc" ++ show l
ppVar (Left (Global g)) = pretty $ "loc" ++ show g

ppExpr :: TExpr -> Doc String
ppExpr = cata $ \(ExprType t e) -> case e of
  Lit (LInt x) -> pretty x
  Lit (LBool True) -> "true"
  Lit (LBool False) -> "false"

  Op l op r -> l <+> ppOp op <+> r

  Var name -> ppVar name

builtin :: TypeID -> String -> Bool
builtin tid name = Just name == (builtIns !? tid)

ppFmt :: TypedType -> (Doc String, Doc String -> Doc String)
ppFmt (Fix t) = first (\s -> "\"" <> s <> "\\n\"") $ case t of
  TCon g _ | builtin g "Bool" -> ("%s", \s -> s <+> sep ["?", "\"True\"", ":", "\"False\""])
  TCon g _ | builtin g "Int" -> ("%d", id)
  TCon g _ -> undefined
  TVar tv -> undefined
  TFun fixs fix -> ("", id)

ppType :: TypedType -> Doc String
ppType = cata $ \case
  TCon g _ | builtin g "Bool" -> "bool"
  TCon g _ | builtin g "Int" -> "int"
  TCon t _ -> error $ "Unrecognized type: " ++ show t  -- Add a dictionary of TypeIDs to Strings.

ppBody :: NonEmpty (Doc String) -> Doc String
ppBody = (<> (line <> "}")) . ("{" <>) . nest 4 . (line <>) . vsep . NE.toList

ppBody' :: NonEmpty TStmt -> Doc String
ppBody' = ppBody . fmap ppStmt

ppStmt :: TStmt -> Doc String
ppStmt = cata $ (<> ";") . go . first (\e@(Fix (ExprType t _)) -> (t, ppExpr e))
  where
    go = \case
      Print (t, e) ->
        let (fmt, arg) = ppFmt t
        in "printf(" <> fmt <> "," <+> arg e <> ")"

      Assignment name (t, e) ->
        ppType t <+> ppVar (Right name) <+> "=" <+> e

      If (_, cond) ifTrue elifs mifFalse ->
        "if" <+> "(" <> cond <> ")"
          <+> ppBody ifTrue
          <+> sep (fmap (\((_, c), b) -> "else if" <+> "(" <> c <> ")" <+> ppBody b) elifs)
          <+> maybe mempty (\ifFalse -> "else" <+> ppBody ifFalse) mifFalse

pp :: [TStmt] -> String
pp stmts = show $ case stmts of
  [] -> mainDec <+> ppBody (NE.singleton "return 0;")
  (stmt : stmts') -> headers <> line <> line <> mainDec <+> ppBody' (stmt :| stmts')
  where
    mainDec = sep ["int", "main", "(", ")"]
    headers = vsep $ fmap (\s -> "#include" <+> "<" <> s <> ">") ["stdbool.h", "stdio.h"]