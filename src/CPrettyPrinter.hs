{-# LANGUAGE LambdaCase, OverloadedStrings, ScopedTypeVariables #-}
module CPrettyPrinter (pp, Context''(..)) where

-- Maybe use something like https://hackage.haskell.org/package/language-c 

import AST

import Prettyprinter
import Data.Functor ((<&>))
import Data.Functor.Foldable (cata, cataA, Base)
import Data.Biapplicative (first, bimap)
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Foldable (foldl', fold)
import Data.Semigroup (sconcat)
import Data.Maybe (fromMaybe, mapMaybe)

import Data.Map (Map, (!), (!?))
import Data.List (intercalate)
import qualified Data.Set as S
import Data.Either (rights)
import Data.Set ((\\), Set)
import Data.Bifoldable (bifold)
import Control.Monad.Trans.Reader
import Control.Applicative (liftA2)
import Data.Bitraversable (bitraverse, bisequenceA)
import Data.Foldable (toList)
import qualified Data.Map as M
import Typecheck (apply, Subst (Subst))
import Data.Bool (bool)
import qualified Data.Text as T
import Data.Text (Text)
import Control.Monad.Trans.Class (lift)
import Data.Unique (Unique, newUnique, hashUnique)
import Control.Monad.Trans.State (State, runState)
import Control.Monad.Trans.RWS (RWS, tell, RWST, runRWST)
import qualified Control.Monad.Trans.RWS as RWS (ask)
import Debug.Trace (traceShowId)


data Context'' = Context
  { builtins :: Builtins
  , datas :: Map (TypeID, [TypedType]) TDataDec
  }

type Docc = Doc ()
type Context' = ReaderT Context'' IO
type Context = Context' Docc
type StmtContext' = RWST Context'' [Docc] () IO
type StmtContext = StmtContext' Docc  -- Adds shit when it quits the function. Used for lambdas.

-- Some writer stuff
putBefore :: Docc -> StmtContext' ()
putBefore = tell . pure


-- Operating on Context
liftCtx :: Context' a -> StmtContext' a
liftCtx ctx = do
  r <- RWS.ask
  lift $ runReaderT ctx r

runCtx :: StmtContext -> Context' (Docc, [Docc])
runCtx ctx = do
  rctx <- ask
  (x, _s, w) <- lift $ runRWST ctx rctx ()
  return (x, w)



-- Todo: make a class for pretty printing
ppOp :: Op -> Docc
ppOp = \case
  Plus -> "+"
  Minus -> "-"
  Times -> "*"
  Divide -> "/"
  Equals -> "=="
  NotEquals -> "!="

ppIdType :: TypedType -> Context
ppIdType = cataA $ \case
  TFun args ret -> do
    args' <- sequenceA args
    ret' <- ret
    pure $ "br_" <> mconcat (fmap (<> "_") args') <> "ret_" <> ret'
  TCon t _ -> pure $ "t" <> pretty (show t)

  -- Invalid state.
  TDecVar (TV tv) -> error $ concat ["'", T.unpack tv, "' decvar should not be here."]
  TVar (TV tv) -> error $ concat ["'", T.unpack tv, "' decvar should not be here."]

ppConstructor :: TypeID -> [TypedType] -> Global -> Context
ppConstructor t tts g = do
  dd <- (! (t, tts)) . datas <$> ask
  case dd of
    (DD _ _ cons) | isEnum cons -> memberTag g t tts
    _ -> dataConstructorName t tts g

isConstructor :: Global -> [TDataDec] -> Bool
isConstructor g = elem g . concatMap (\(DD _ _ cons) -> map (\(DC g _) -> g) (NE.toList cons))

ppGlobal :: TypedType -> Global -> Context
ppGlobal (Fix t) g = do
  (Builtins _ _ _ fromCons) <- builtins <$> ask
  dds <- M.elems . datas <$> ask
  case t of
    TCon t tts ->
      case fromCons !? g of
        Nothing -> ppConstructor t tts g
        Just s -> return $ pretty s
    TFun args (Fix (TCon t tts)) | isConstructor g dds -> ppConstructor t tts g
    TFun ret args ->
      (("g" <> pretty (show g)) <>) <$> ppIdType (Fix t)
    -- TVar tv -> _
    -- TDecVar tv -> _

ppVar :: TypedType -> Either Global Local -> Context
ppVar _ (Right l) = pure $ pretty $ "loc" ++ show l
ppVar t (Left g) = ppGlobal t g


newLambdaName :: StmtContext' Docc
newLambdaName = ("lam" <>) . pretty . hashUnique <$> lift newUnique

-- Adds a lambda to context, then returns its name.
addLambda :: [(Local, TypedType)] -> TypedType -> StmtContext -> StmtContext
addLambda params ret expr = do
  name <- newLambdaName
  innerExpr <- expr
  let stmt = "{" <+> "return" <+> innerExpr <> ";" <+> "}"
  lam <- liftCtx $ ppFun' params ret stmt name
  putBefore lam
  return name


ppExpr :: TExpr -> StmtContext
ppExpr = cataA $ \(ExprType t e) -> case e of
  Lit (LInt x) -> pure $ pretty x

  Op l op r -> liftA2 (\l r -> l <> ppOp op <> r) l r

  Var name -> liftCtx $ ppVar t name

  Call f args -> liftA2 (\f args -> f <> "(" <> hsep (punctuate comma args) <> ")") f $ sequenceA args

  Lam params body ->
    let Fix (TFun paramTypes ret) = t  -- if it's a lambda, must match.
        paramsWithTypes = zip params paramTypes
    in addLambda paramsWithTypes ret body

-- wtf does real type mean??
-- oh, how a type is represented by my language
ppRealType :: TypedType -> Context
ppRealType = cataA $ \case
  TCon g _ -> pure $ pretty $ show g --fromMaybe "???" (builtIns !? g)
  TFun args ret -> liftA2 (\args ret -> "(" <> hsep (punctuate ", " args) <> ") " <> ret) (sequenceA args) ret

ppFmt :: TypedType -> Context' (Docc, Docc -> Docc)
ppFmt (Fix t) = (fmap . first) (\s -> "\"" <> s <> "\\n\"") $ case t of
  --TCon g _ | builtin g "Bool" -> 
  -- Quik print for basic types
  TCon g ts -> do
    Builtins _ toTypes _ _ <- builtins <$> ask
    return $ case toTypes !? g of
      Nothing -> ("Non-builtin type detected :)", id) 
      Just "int" -> ("%d", id)
      Just "bool" -> ("%s", \s -> s <+> sep ["?", "\"True\"", ":", "\"False\""])
      _ -> undefined
  TVar tv -> undefined
  TDecVar tv -> undefined
  t@(TFun fixs fix) -> do
    t' <- ppRealType (Fix t)
    return ("%x: " <> t' , id)


ppDatatypeName :: TypeID -> [TypedType] -> Context
ppDatatypeName = structName


ppTypeName :: TypedType -> Context
ppTypeName t = do
  (Builtins _ toTypes _ _) <- builtins <$> ask
  let go (Fix t) = case t of
        TCon t apps -> case toTypes !? t of
          Just s -> return $ pretty s  -- We don't need no applications with built in types.
          Nothing -> ppDatatypeName t apps
        TCon t params -> traverse ppType params <&> \ps -> pretty (show t) <> "___" <> mconcat (fmap (<> "_") ps)
        TCon t _ -> error $ "Unrecognized type: " ++ show t  -- Add a dictionary of TypeIDs to Strings.

        TFun args ret -> liftA2 (\args ret -> ret <+> "(" <> hsep (punctuate comma args) <> ")") (traverse ppType args) (ppType ret)
  go t

ppType :: TypedType -> Context
ppType (Fix t) = do
  (Builtins _ toTypes _ _) <- builtins <$> ask
  case t of
    TCon t apps -> case toTypes !? t of
      Just s -> return $ pretty s  -- We don't need no applications with built in types.
      Nothing -> do
        (DD _ _ cons) <- (! (t, apps)) . datas <$> ask
        let preamble = if isEnum cons then "enum" else "struct"
        (preamble <+>) <$> ppDatatypeName t apps
    t -> ppTypeName $ Fix t


ppParam :: Local -> TypedType -> Context
ppParam l (Fix t@(TFun _ _)) =
  let (TFun args ret) = fmap ppType t
  in (\var args ret -> ret <+> "(*" <> var <> ")" <> encloseSep "(" ")" comma args) <$> ppVar (Fix t) (Right l) <*> sequenceA args <*> ret
ppParam l t = liftA2 (<+>) (ppType t) (ppVar t (Right l))

ppBody :: Traversable t => t StmtContext -> StmtContext
ppBody = fmap ((<> (line <> "}")) . ("{" <>) . nest 4 . (line <>) . vsep . toList) . sequenceA

ppBody' :: NonEmpty TStmt -> StmtContext
ppBody' = ppBody . fmap ppStmt

ppTopLevelStmt :: Set Local -> TStmt -> StmtContext
ppTopLevelStmt tlVars (Fix (Assignment l e@(Fix (ExprType t _)))) | l `S.member` tlVars = liftA2 (\t e -> t <+> "=" <+> e <> ";") (liftCtx $ ppVar t (Right l)) (ppExpr e)
ppTopLevelStmt _ s = ppStmt s

ppTopLevelBody :: Set Local -> NonEmpty TStmt -> StmtContext
ppTopLevelBody tlVars = ppBody . fmap (ppTopLevelStmt tlVars)

ppStmt :: TStmt -> StmtContext
ppStmt = cata $ fmap (<> ";") . go . first (\e@(Fix (ExprType t _)) -> (t, ppExpr e))
  where
    go :: Base (Stmt Local g (TypedType, StmtContext))  StmtContext -> StmtContext
    go = \case
      Print (t, e :: StmtContext) -> do
        e' <- e
        (fmt, arg) <- liftCtx $ ppFmt t
        return $ "printf(" <> fmt <> "," <+> arg e' <> ")"

      Assignment name (t, e) ->
        liftA2 (\var e -> var <+> "=" <+> e) (liftCtx $ ppParam name t) e

      If (_, cond) ifTrue elifs mifFalse -> do
        cond <- cond
        ifTrue <- ppBody ifTrue
        elifs <- traverse (\((_, c), b) -> liftA2 (\c b -> "else if" <+> "(" <> c <> ")" <+> b) c (ppBody b)) elifs
        ifFalse <- traverse ppBody mifFalse
        return $ "if" <+> "(" <> cond <> ")"
          <+> ifTrue
          <+> sep elifs
          <+> maybe mempty ("else" <+>) ifFalse

      Return (t, e) ->
        ("return" <+>) <$> e

      ExprStmt (t, e) ->
          e


-- More general ppFun
ppFun' :: [(Local, TypedType)] -> TypedType -> Docc -> Docc -> Context
ppFun' params ret body name = do
    params <- traverse (uncurry ppParam) params
    ret <- ppType ret
    let header = "static" <+> ret <+> name <+> "(" <> hsep (punctuate comma params) <> ")"
    return $ header <+> body

ppFun :: TFunDec -> Context
ppFun (FD name params ret body) = do
  let t = Fix $ TFun (map snd params) ret
  (body, prevs) <- runCtx $ ppBody' body
  let prev = vsep prevs <> line
  fun <- ppFun' params ret body =<< ppVar t (Left name)
  return $ prev <> fun

ppDec :: MonoFunDec -> Context
ppDec (MonoFunDec name t@(Fix (TFun params ret))) = do
  ret <- ppType ret
  name <- ppVar t (Left name)
  params <- traverse ppType params
  return $ "static" <+> ret <+> name <+> "(" <> hsep (punctuate comma params) <> ");"

ppDec _ = error "Should not happen."


tvarSubst :: [TVar] -> [TypedType] -> Subst
tvarSubst vars tts = Subst $ M.fromList $ zip vars tts

dataToAppliedType :: TDataDec -> [TypedType] -> TypedType
dataToAppliedType (DD t vars _) tts =
  let appt = Fix $ TCon t $ map (Fix . TVar) vars
  in apply (tvarSubst vars tts) appt

structName, structType, enumType :: TypeID -> [TypedType] -> Context
structName t tts = traverse ppTypeName tts <&> \tts -> "t" <> pretty (show t) <> "__" <> mconcat (punctuate "_" tts)
structType t tts = ("struct" <+>) <$> structName t tts
enumType t tts = ("enum" <+>) <$> structName t tts

structMember :: Global -> TypeID -> [TypedType] -> Context
structMember g t tts = structName t tts <&> (<> ("___" <> pretty (show g)))

memberTag :: Global -> TypeID -> [TypedType] -> Context
memberTag g t tts = structMember g t tts <&> (<> "_tag")

cDeclarationBody :: Traversable t => t (Context) -> Context
cDeclarationBody members = do
  members' <- nest 4 . (<> line) . (line <>) . vsep . toList . fmap (<> ";") <$> sequenceA members
  return $ "{" <+> members' <+> "}"

cDeclaration :: Traversable t => Context -> t (Context) -> Context
cDeclaration name members = liftA2 (<+>) name (cDeclarationBody members)

cAnonymousDeclaration :: Traversable t => Docc -> t (Context) -> Context
cAnonymousDeclaration name = cDeclaration (pure name)

cStructBody :: (Traversable t) => t (Context, Context) -> Context
cStructBody = cDeclarationBody . fmap (uncurry $ liftA2 (<+>))

cStruct :: Traversable t => Context -> t (Context, Context) -> Context
cStruct name members = cDeclaration (("struct" <+>) <$> name) (uncurry (liftA2 (<+>)) <$> members) <&> (<> ";")

cAnonymousTypedDeclaration :: Traversable t => Docc -> t (Context, Context) -> Context
cAnonymousTypedDeclaration name members = cAnonymousDeclaration name $ uncurry (liftA2 (<+>)) <$> members

memberEnum :: Traversable t => TypeID -> [TypedType] -> t TDataCon -> Context
memberEnum t tts cons = traverse (\(DC g _) -> memberTag g t tts) cons <&> \tags -> "enum" <+> encloseSep "{" "}" comma (toList tags)

unionName, enumName :: TypeID -> [TypedType] -> Context
unionName t tts = structName t tts <&> (<> "__union")
enumName t tts = structName t tts <&> (<> "__tags")

structMemberStructMember :: TypeID -> [TypedType] -> Global -> Int -> Context
structMemberStructMember t tts g i = structMember g t tts <&> (<> ("__" <> pretty (show i)))

structMemberStruct :: TypeID -> [TypedType] -> TDataCon -> Context
structMemberStruct t tts (DC g ms) = cAnonymousTypedDeclaration "struct" ((\(i, mt) -> (ppType mt, structMemberStructMember t tts g i)) <$> zip [0 :: Int ..] ms)

ppDataDeclaration :: MonoDataDec -> Context
ppDataDeclaration (MonoDataDec t tts) = ask >>= \ctx -> case datas ctx ! (t, tts) of
  DD t _ cons | isEnum cons -> enumType t tts <&> (<> ";")
  _ -> structType t tts <&> (<> ";")


dataConstructorName :: TypeID -> [TypedType] -> Global -> Context
dataConstructorName t tts g = do
  name <- structMember g t tts
  return $ name <> "_con"


outputBefore :: [Docc] -> Docc -> Docc
outputBefore xs y = vsep $ xs ++ [y]

dataConstructor :: TypeID -> [TypedType] -> TDataCon -> Context
dataConstructor t tts (DC g mts) = do
  typeName <- structType t tts
  conName <- dataConstructorName t tts g

  enumName <- enumName t tts
  currentTag <- memberTag g t tts

  unionName <- unionName t tts
  structName <- structMember g t tts

  conMembers <- traverse (\(i, mt) -> liftA2 (,) (ppType mt) (structMemberStructMember t tts g i)) $ zip [0 :: Int ..] mts

  let init l v = "." <> l <+> "=" <+> v
  case mts of
    [] -> return $ "static" <+> typeName <+> conName <+> "=" <+> enclose lbrace rbrace (init enumName currentTag) <+> ";"
    _ -> do
      let dataInit = encloseSep lbrace rbrace comma $ map (\(_, name) -> init name (name <> "_param")) conMembers

      -- Will prev be always empty tho?
      (body, prev) <- runCtx $ ppBody $ (:[]) $ pure $ "return" <+> enclose lparen rparen typeName <+> encloseSep lbrace rbrace comma [init enumName currentTag, init (unionName <> "." <> structName) dataInit] <> ";"

      let parameterList = map (uncurry (<+>) . fmap (<> "_param")) conMembers
      let con = "static" <+> typeName <+> conName <+> encloseSep lparen rparen comma parameterList <+> body
      return $ outputBefore prev con

structDataConstructor :: TypeID -> [TypedType] -> TDataCon -> Context
structDataConstructor t tts (DC g mts) = do
  typeName <- structType t tts
  conName <- dataConstructorName t tts g

  conMembers <- traverse (\(i, mt) -> liftA2 (,) (ppType mt) (structMemberStructMember t tts g i)) $ zip [0 :: Int ..] mts

  let init l v = "." <> l <+> "=" <+> v
  let dataInit = encloseSep lbrace rbrace comma $ map (\(_, name) -> init name (name <> "_param")) conMembers
  (body, prev) <- runCtx $ ppBody $ (:[]) $ pure $ "return" <+> enclose lparen rparen typeName <+> dataInit <> ";"

  let parameterList = map (uncurry (<+>) . fmap (<> "_param")) conMembers
  let con = "static" <+> typeName <+> conName <+> encloseSep lparen rparen comma parameterList <+> body
  return $ outputBefore prev con


isEnum :: Foldable t => t TDataCon -> Bool
isEnum = all (\(DC _ ts) -> null ts)


ppDataDefinition :: (TDataDec, [TypedType]) -> Context

-- Struct
ppDataDefinition (DD t vars (dc :| []), tts) = do
  let subst = tvarSubst vars tts
  let dc'@(DC g ts) = apply subst dc
  struct <- cStruct (structName t tts) ((\(i, mt) -> (ppType mt, structMemberStructMember t tts g i)) <$> zip [0 :: Int ..] ts)
  cons <- structDataConstructor t tts dc'
  return $ vsep [struct, cons]

-- Enum
ppDataDefinition (DD t vars cons, tts) | isEnum cons = do
  let subst = tvarSubst vars tts
  tags <- traverse (\(DC g _) -> memberTag g t tts) (apply subst cons)
  name <- structName t tts
  return $ "enum" <+> name <+> encloseSep lbrace rbrace comma (NE.toList tags) <> ";"

-- ADT
ppDataDefinition (DD t vars cons, tts) = do
  let subst = tvarSubst vars tts
      cons' = apply subst cons
  mainStruct <- cStruct (structName t tts)
    [ (memberEnum t tts cons', enumName t tts)
    , (cAnonymousTypedDeclaration "union" (mapMaybe (\case { (DC _ []) -> Nothing; dc@(DC g ts) -> Just (structMemberStruct t tts dc, structMember g t tts) }) (NE.toList cons')), unionName t tts)
    ]
  ccons <- traverse (dataConstructor t tts) cons'
  return $ vsep $ mainStruct : NE.toList ccons

ppDataDeclarations :: [Either MonoDataDec (TDataDec, [TypedType])] -> Context
ppDataDeclarations = fmap vsep . traverse (either ppDataDeclaration ppDataDefinition)

-- Check which are global variables.

pp :: Context'' -> [Either MonoDataDec (TDataDec, [TypedType])] -> [Either MonoFunDec TFunDec] -> [TStmt] -> IO String -- IO is for uniques
pp ctx dds funs stmts = fmap show $ flip runReaderT ctx $
  let mainDec = sep ["int", "main", "(", ")"]
  in case stmts of
  [] -> fmap ((mainDec <+>) . fst) $ runCtx $ ppBody $ NE.singleton $ pure "return 0;"
  (stmt : stmts') -> do

    let headers = vsep $ fmap (\s -> "#include" <+> "<" <> s <> ">") ["stdbool.h", "stdio.h"]

    dataDeclarations <- ppDataDeclarations dds

    let tlAssignments = mapMaybe (\case { Fix (Assignment l (Fix (ExprType t _))) -> Just (l, t); _ -> Nothing }) stmts
    let locals = foldMap usedLocals $ rights funs
    let actualTLVars = S.intersection (S.fromList $ map fst tlAssignments) locals
    tlDeclarations <- fmap vsep $ traverse (\(l, t) -> liftA2 (\t name -> "static" <+> t <+> name <> ";") (ppType t) (ppVar t (Right l))) $ filter (\(l, t) -> l `S.member` actualTLVars) tlAssignments
    functions <- vsep . punctuate line <$> traverse (either ppDec ppFun) funs
    (body, prev) <- runCtx $ ppTopLevelBody actualTLVars (stmt :| stmts')

    let main = mainDec <+> body
    return $ headers <> line <> line <> dataDeclarations <> line <> line <> tlDeclarations <> line <> line <> functions <> line <> line <> outputBefore prev main

