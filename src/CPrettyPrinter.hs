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
import Data.Maybe (fromMaybe, mapMaybe)

import Data.Map ((!), (!?))
import Data.List (intercalate)
import qualified Data.Set as S
import Data.Either (rights)
import Data.Set ((\\), Set)


-- Todo: make a class for pretty printing
ppOp :: Op -> Doc String
ppOp = \case
  Plus -> "+"
  Minus -> "-"
  Times -> "*"
  Divide -> "/"
  Equals -> "=="
  NotEquals -> "!="

ppIdType :: TypedType -> Doc String
ppIdType = cata $ \case
  TFun args ret -> "br_" <> mconcat (fmap (<> "_") args) <> "ret_" <> ret
  TCon (TypeID x) _ -> "t" <> pretty (show x)

ppGlobal :: TypedType -> Global -> Doc String
ppGlobal t g = "g" <> pretty (show g) <> ppIdType t

ppVar :: TypedType -> Either Global Local -> Doc String
ppVar _ (Right l) = pretty $ "loc" ++ show l
ppVar t (Left g) = ppGlobal t g



ppExpr :: TExpr -> Doc String
ppExpr = cata $ \(ExprType t e) -> case e of
  Lit (LInt x) -> pretty x
  Lit (LBool True) -> "true"
  Lit (LBool False) -> "false"

  Op l op r -> l <+> ppOp op <+> r

  Var name -> ppVar t name

  Call f args -> f <> "(" <> hsep (punctuate comma args) <> ")"

builtin :: TypeID -> String -> Bool
builtin tid name = Just name == (builtIns !? tid)

ppRealType :: TypedType -> Doc String
ppRealType t = pretty $ flip cata t $ \case
  TCon g _ -> fromMaybe "???" (builtIns !? g)
  TFun args ret -> "(" ++ intercalate ", " args ++ ") " ++ ret

ppFmt :: TypedType -> (Doc String, Doc String -> Doc String)
ppFmt (Fix t) = first (\s -> "\"" <> s <> "\\n\"") $ case t of
  TCon g _ | builtin g "Bool" -> ("%s", \s -> s <+> sep ["?", "\"True\"", ":", "\"False\""])
  TCon g _ | builtin g "Int" -> ("%d", id)
  TCon g _ -> undefined
  TVar tv -> undefined
  TDecVar tv -> undefined
  t@(TFun fixs fix) -> ("%x: " <> ppRealType (Fix t), id)

ppType :: TypedType -> Doc String
ppType = cata $ \case
  TCon g _ | builtin g "Bool" -> "bool"
  TCon g _ | builtin g "Int" -> "int"
  TCon t _ -> error $ "Unrecognized type: " ++ show t  -- Add a dictionary of TypeIDs to Strings.

  TFun args ret -> ret <+> "(" <> hsep (punctuate comma args) <> ")"

ppParam :: Local -> TypedType -> Doc String
ppParam l (Fix t@(TFun _ _)) =
  let (TFun args ret) = fmap ppType t
  in ret <+> ppVar (Fix t) (Right l) <+> encloseSep "(" ")" comma args
ppParam l t = ppType t <+> ppVar t (Right l)

ppBody :: NonEmpty (Doc String) -> Doc String
ppBody = (<> (line <> "}")) . ("{" <>) . nest 4 . (line <>) . vsep . NE.toList

ppBody' :: NonEmpty TStmt -> Doc String
ppBody' = ppBody . fmap ppStmt

ppTopLevelStmt :: Set Local -> TStmt -> Doc String
ppTopLevelStmt tlVars (Fix (Assignment l e@(Fix (ExprType t _)))) | l `S.member` tlVars = ppVar t (Right l) <+> "=" <+> ppExpr e <> ";"
ppTopLevelStmt _ s = ppStmt s

ppTopLevelBody :: Set Local -> NonEmpty TStmt -> Doc String
ppTopLevelBody tlVars = ppBody . fmap (ppTopLevelStmt tlVars)

ppStmt :: TStmt -> Doc String
ppStmt = cata $ (<> ";") . go . first (\e@(Fix (ExprType t _)) -> (t, ppExpr e))
  where
    go = \case
      Print (t, e) ->
        let (fmt, arg) = ppFmt t
        in "printf(" <> fmt <> "," <+> arg e <> ")"

      Assignment name (t, e) ->
        ppType t <+> ppVar t (Right name) <+> "=" <+> e

      If (_, cond) ifTrue elifs mifFalse ->
        "if" <+> "(" <> cond <> ")"
          <+> ppBody ifTrue
          <+> sep (fmap (\((_, c), b) -> "else if" <+> "(" <> c <> ")" <+> ppBody b) elifs)
          <+> maybe mempty (\ifFalse -> "else" <+> ppBody ifFalse) mifFalse

      Return (t, e) ->
        "return" <+> e

      ExprStmt (t, e) ->
          e

ppFun :: TFunDec -> Doc String
ppFun (FD name params ret body) = header <+> ppBody' body
  where
    t = Fix $ TFun (map snd params) ret
    header = "static" <+> ppType ret <+> ppVar t (Left name) <+> "(" <> hsep (punctuate comma $ map (uncurry ppParam) params) <> ")"

ppDec :: MonoFunDec -> Doc String
ppDec (MonoFunDec name t@(Fix (TFun params ret))) = ppType ret <+> ppVar t (Left name) <+> "(" <> hsep (punctuate comma $ map ppType params) <> ");"
ppDec _ = error "Should not happen."


-- Check if variables

pp :: [Either MonoFunDec TFunDec] -> [TStmt] -> String
pp funs stmts = show $ case stmts of
  [] -> mainDec <+> ppBody (NE.singleton "return 0;")
  (stmt : stmts') -> headers <> line <> line <> tlDeclarations <> line <> line <> functions <> line <> line <> mainDec <+> ppTopLevelBody actualTLVars (stmt :| stmts')
  where
    mainDec = sep ["int", "main", "(", ")"]
    headers = vsep $ fmap (\s -> "#include" <+> "<" <> s <> ">") ["stdbool.h", "stdio.h"]

    tlDeclarations = vsep $ map (\(l, t) -> "static" <+> ppType t <+> ppVar t (Right l) <> ";") tlAssignments
    functions = vsep $ punctuate line $ map (either ppDec ppFun) funs

    tlAssignments = mapMaybe (\case { Fix (Assignment l (Fix (ExprType t _))) -> Just (l, t); _ -> Nothing }) stmts
    locals = foldMap usedLocals $ rights funs

    actualTLVars = S.union (S.fromList $ map fst tlAssignments) locals
