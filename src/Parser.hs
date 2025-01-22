{-# LANGUAGE LambdaCase, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

module Parser (parse) where


import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import qualified Text.Megaparsec as TM (parse)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Bifunctor (first)
import Data.Functor (void, ($>), (<&>))
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE

import Data.Maybe (isJust, catMaybes, fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty
import Data.Foldable (foldl')
import qualified Data.Set as Set
import qualified Text.Megaparsec.Char as C
import AST.Common (Ann (..), TCon (..), ConName (..), VarName (..), Annotated (..), Op (..), LitType (..), (:.) (..), ctx, UnboundTVar (..), MemName (..))
import AST.Untyped (ExprF (..), FunDec (..), DataCon (..), TypeF (..), StmtF (..), DataDef (..), DeconF (..), Module (..), Stmt, Decon, Expr, AnnStmt, Type, CaseF (..), uType, Case, DataRec (..))
import Data.Functor.Foldable (embed, cata)
import Control.Monad ((<=<))
import Data.Either (partitionEithers)
import Data.Biapplicative (bimap)


type Parser = Parsec MyParseError Text
type FileName = String

parse :: FileName -> Text -> Either Text Module
parse filename = first (Text.pack . errorBundlePretty) . TM.parse (scn >> topLevels <* eof) filename


-- Top level
topLevels :: Parser Module
topLevels = do
  eas <- many $ recoverStmt (L.nonIndented sc  (annotationOr statement)) <* scn
  Mod <$> annotateStatements eas



------------------------
-- Parsing statements --
------------------------

statement :: Parser Stmt
statement = choice
  [ sPass
  , sCase
  , sIf
  , sPrint
  , sReturn
  , sDataDefinition

  , sDefinition
  , sMutAssignment

  , try (checkIfFunction >> sFunctionOrCall)
  , sExpression
  ]

-- Each statement
sPass :: Parser Stmt
sPass = do
  keyword "pass"
  pure Pass

sIf :: Parser Stmt
sIf = do
  (cond, ifBody) <- scope (,) (keyword "if" >> expression)
  elifs <- many $ scope (,) (keyword "elif" >> expression)
  elseBody <- optional $ scope (const id) (keyword "else")
  pure $ If cond ifBody elifs elseBody

sCase :: Parser Stmt
sCase = recoverableIndentBlock $ do
  -- case header
  keyword "case"
  condition <- expression

  -- switch inner
  pure $ L.IndentSome Nothing (pure . Switch condition . NE.fromList) sSingleCase

sSingleCase :: Parser Case
sSingleCase = scope id $ do
  -- deconstructor
  decon <- sDeconstruction

  -- parse expression here in the future
  pure $ Case decon Nothing

sDeconstruction :: Parser Decon
sDeconstruction = caseVariable <|> caseRecord <|> caseConstructor
 where
    caseVariable = Fix . CaseVariable <$> variable
    caseConstructor = fmap Fix $ CaseConstructor <$> dataConstructor <*> args
    caseRecord = do
      name <- try $ typeName <* lookAhead (symbol "{")
      decons <- NonEmpty.fromList <$> between (symbol "{") (symbol "}") (sepBy1 recordFieldDecon (symbol ","))
      pure $ Fix $ CaseRecord name decons

    recordFieldDecon = do
      fieldName <- member
      symbol ":"
      decon <- sDeconstruction
      pure (fieldName, decon)


    args = do
      between (symbol "(") (symbol ")") (sepBy1 sDeconstruction (symbol ",")) <|> pure []

sPrint :: Parser Stmt
sPrint = do
  keyword "print"
  expr <- expression
  pure $ Print expr

sDefinition :: Parser Stmt
sDefinition = do
  name <- try $ variable <* symbol "="
  rhs <- expression
  pure $ Assignment name rhs

sMutAssignment :: Parser Stmt
sMutAssignment = do
  name <- try $ variable <* symbol "<="
  rhs <- expression
  pure $ Mutation name rhs

sReturn :: Parser Stmt
sReturn = do
  keyword "return"
  expr <- optional expression
  pure $ Return expr

sExpression :: Parser Stmt
sExpression = do
  from <- getOffset
  expr@(Fix chkExpr) <- expression
  to <- getOffset
  case chkExpr of
    Call _ _ -> pure $ ExprStmt expr
    _ -> do
      registerCustom $ MyPE (from, to) DisallowedExpressionAsStatement
      pure $ ExprStmt expr  -- report an error, but return this for AST


checkIfFunction :: Parser ()
checkIfFunction = void $ lookAhead (functionHeader >> eol)

sFunctionOrCall :: Parser Stmt
sFunctionOrCall = recoverableIndentBlock $ do
  (header, mExpr) <- functionHeader

  -- If it's a single expression function (has the ':'), we know it's not a call.
  ret $ case mExpr of
    Just expr ->
      let expr2stmt = Fix . O . Annotated [] . Return . Just
          stmt = expr2stmt expr
          body = NonEmpty.singleton stmt
      in L.IndentNone $ FunctionDefinition header body

    Nothing ->
      -- If that's a normal function, we check if any types were defined
      let (FD name params rett) = header
          types = rett : map snd params
      in if any isJust types
        then L.IndentSome Nothing (fmap (FunctionDefinition header . NonEmpty.fromList) . annotateStatements) $ recoverStmt (annotationOr statement)
        else flip (L.IndentMany Nothing) (recoverStmt (annotationOr statement)) $ \case
          stmts@(_:_) -> FunctionDefinition header . NonEmpty.fromList <$> annotateStatements stmts
          [] ->
            let args = map (deconToExpr . fst) params
                funName = Fix $ Var name
            in pure $ ExprStmt $ Fix $ Call funName args

-- some construction might also be misrepresented as a deconstruction.
deconToExpr :: Decon -> Expr
deconToExpr = cata $ embed . \case
  CaseVariable v                  -> Var v
  CaseConstructor con []          -> Con con
  CaseConstructor con exprs@(_:_) -> Call (Fix $ Con con) exprs
  CaseRecord con mems             -> RecCon con mems

functionHeader :: Parser (FunDec, Maybe Expr)
functionHeader = do
  let param = liftA2 (,) sDeconstruction (optional pType)
  name <- variable
  params <- between (symbol "(") (symbol ")") $ sepBy param (symbol ",")
  ret <- choice
    [ Left <$> (symbol ":" >> expression)
    , Right <$> optional (symbol "->" >> pType)
    ]

  return $ case ret of
    Left expr -> (FD name params Nothing, Just expr)
    Right mType -> (FD name params mType, Nothing)


-- Data definitions.
--   Either a normal ADT or a record type.
sDataDefinition :: Parser Stmt
sDataDefinition = recoverableIndentBlock $ do
  tname <- typeName
  polys <- many generic
  return $ flip (L.IndentMany Nothing) (recoverCon conOrRecOrAnnotation) $ toRecordOrADT tname polys <=< assignAnnotations Annotated
   where
    conOrRecOrAnnotation :: Parser (Either [Ann] (Either DataRec DataCon))
    conOrRecOrAnnotation = Left <$> annotation <|> Right . Left <$> dataRec <|> Right . Right <$> dataCon

    toRecordOrADT :: TCon -> [UnboundTVar] -> [Annotated (Either DataRec DataCon)] -> Parser Stmt
    -- empty datatype
    toRecordOrADT tname polys [] = pure $ DataDefinition $ DD tname polys (Right [])
    
    toRecordOrADT tname polys ((Annotated ann first) : rest) = 
      let (records, cons) = partitionEithers $ (\(Annotated ann x) -> bimap (Annotated ann) (Annotated ann) x) <$> rest
      in case first of
        Left rec ->
          case cons of
            [] ->
              pure $ DataDefinition $ DD tname polys $ Left $ Annotated ann rec :| records

            _:_ -> do
              fail "Encountered constructors in a Record definition."

        Right dc -> 
          case records of
            [] -> 
              pure $ DataDefinition $ DD tname polys $ Right $ Annotated ann dc : cons
            _:_ -> do
              fail "Encountered record fields in an ADT definition."  -- should not end parsing, but im lazy.


dataRec :: Parser DataRec
dataRec = do
  recordName <- member
  recordType <- pType
  pure $ DR recordName recordType

dataCon :: Parser DataCon
dataCon = do
  conName <- dataConstructor
  types <- many typeTerm
  return $ DC conName types



-----------------
-- Annotations --
-----------------

annotation :: Parser [Ann]
annotation = do
  void $ string commentDelimeter  -- Important that we don't consume whitespace after this (symbol consumes whitespace at the end).
  manns <- between (symbol "[") (symbol "]") $ annotation `sepBy1` symbol ","
  pure $ catMaybes manns

  where
    annotation = do
      keyOffset <- getOffset
      key <- identifier  -- just parse the "key" part
      value <- stringLiteral
      case key of
        "ctype" -> ann $ ACType value
        "cstdinclude" -> ann $ ACStdInclude value
        "clit" -> ann $ ACLit value
        unknownKey -> do
          registerExpect keyOffset unknownKey ["ctype", "cstdinclude", "clit"]
          pure Nothing
        where
          ann = pure . Just

annotateStatements :: [Either [Ann] Stmt] -> Parser [AnnStmt]
annotateStatements = assignAnnotations $ \anns stmt -> Fix $ O $ Annotated anns stmt

assignAnnotations :: ([Ann] -> a -> b) -> [Either [Ann] a] -> Parser [b]
assignAnnotations f annors =
  let (ns, leftOverAnns) = foldl' groupAnnotations ([], []) annors
  in case leftOverAnns of
    [] -> return $ reverse ns  -- the statements are added in reverse order in groupAnnotations, so we reverse it at the end.
    _ -> fail "Annotations which do not belong to any statement."  -- todo: add location information
  where
    groupAnnotations (ns, anns) eas = case eas of
      Left annotation -> (ns, anns ++ annotation)
      Right n -> (f anns n : ns, [])


annotationOr :: Parser a -> Parser (Either [Ann] a)
annotationOr x = Left <$> annotation <|> Right <$> x


-----------------
-- Expressions --
-----------------

expression :: Parser Expr
expression = makeExprParser term operatorTable

operatorTable :: [[Operator Parser Expr]]
operatorTable =
  [ [ subscriptOrCall
    , recordUpdate
    ]
  -- , [ prefix "-" Negation
  --   , prefix "not" Not
  --   ]
  , [ binary' "*" Times
    , binary' "/" Divide
    ]
  , [ binary' "+" Plus
    , binary' "-" Minus
    ]
  , [ binary' "==" Equals
    , binary' "/=" NotEquals
    ]
  , [ as
    ]
  , [ lambda
    ]
  ] where
    binary' name op = binary name $ \x y -> Fix (Op x op y)


binary :: Text -> (expr -> expr -> expr) -> Operator Parser expr
binary s f = InfixL $ f <$ symbol s

subscriptOrCall :: Operator Parser Expr
subscriptOrCall = Postfix $ fmap (foldl1 (.) . reverse) $ some (subscript <|> call)

subscript :: Parser (Expr -> Expr)
subscript = (symbol "." >> member) <&> \memname e -> Fix $ MemAccess e memname

call :: Parser (Expr -> Expr)
call = do
    args <- between (symbol "(") (symbol ")") $ expression `sepBy` symbol ","
    return $ Fix . flip Call args

recordUpdate :: Operator Parser Expr
recordUpdate = Postfix $ between (symbol "{") (symbol "}") $ do
  mems <- NonEmpty.fromList <$> sepBy1 memberdef (symbol ",")
  return $ Fix . flip RecUpdate mems

as :: Operator Parser Expr
as = Postfix $ do
    symbol "as"
    t <- pType
    return $ Fix . flip As t

lambda :: Operator Parser Expr
lambda = Prefix $ fmap (foldr1 (.)) $ some $ do
  params <- try $ (variable `sepBy` symbol ",") <* symbol ":"
  return $ Fix . Lam params


-----------
-- Terms --
-----------

term :: Parser Expr
term = choice
  [ eDecimal
  , eGrouping
  , eRecordConstruction
  , eIdentifier
  ]

eDecimal :: Parser Expr
eDecimal = do
  decimal <- lexeme (L.signed sc L.decimal)
  retf $ Lit $ LInt decimal

eGrouping :: Parser Expr
eGrouping = between (symbol "(") (symbol ")") expression

eIdentifier :: Parser Expr
eIdentifier = do
  id <- (Var <$> variable) <|> (Con <$> dataConstructor)
  retf id

eRecordConstruction :: Parser Expr
eRecordConstruction = do
  name <- try $ typeName <* lookAhead (symbol "{")
  recordDef <- NonEmpty.fromList <$> between (symbol "{") (symbol "}") (sepBy1 memberdef (symbol ","))

  retf $ RecCon name recordDef

memberdef :: Parser (MemName, Expr)
memberdef = do
      mem <- member
      symbol ":"
      e <- expression
      pure (mem, e)

-----------
-- Types --
-----------

-- This is used to parse a standalone type
pType :: Parser Type
pType = do
  term <- choice
    [ (:[]) <$> concrete
    , (:[]) <$> poly
    , groupingOrParams
    ]

  fun <- optional $ do
    symbol "->"
    pType
  case fun of
    Nothing -> case term of
      [t] -> return t
      ts -> fail $ "Cannot use an argument list as a return value. (you forgot to write a return type for the function.) (" <> concatMap (ctx uType) ts <> ")"  -- this would later mean that we're returning a tuple, so i'll leave it be.
    Just ret -> return $ Fix $ TFun term ret

  where
    concrete = do
      tcon <- typeName
      targs <- many typeTerm
      return $ Fix $ TCon tcon targs
    groupingOrParams = between (symbol "(") (symbol ")") $ sepBy pType (symbol ",")

-- This is used to parse a type "term", for example if you're parsing a data definition.
-- Ex. you cannot do this: Int -> Int, you have to do this: (Int -> Int)
typeTerm :: Parser Type
typeTerm = choice
  [ grouping
  , poly
  , concreteType
  ]
  where
    grouping = between (symbol "(") (symbol ")") pType
    concreteType = do
      tname <- typeName
      retf $ TCon tname []

poly :: Parser Type
poly = Fix . TVar <$> generic



-- This'll be tricky: a function definition can look exactly like a function call. Welp, I guess I know why `def`s are needed.
-- Still, these are parser combinators - let them worry about proper backtracking.
-- We're gonna do it like this: try to parse a function definition - if we happen to parse any function-y stuff, we're happy, because it's a function.
-- However, for something like this:
-- id (x)
--  return x
-- We have to check if there are any indents. If there aren't -> it's a function.
-- Also, we should throw a custom error if we *know* it's a function, but there's now body.

-- type-level identifiers
typeName :: Parser TCon
typeName = do
  lexeme $ do
    x <- upperChar
    xs <- many identifierChar
    pure $ TC $ T.pack (x:xs)

generic :: Parser UnboundTVar
generic = UTV <$> identifier

variable :: Parser VarName
variable = VN <$> identifier

member :: Parser MemName
member = MN <$> identifier


-- term-level identifiers
identifier :: Parser Text
identifier = do
  lexeme $ do
    x <- lowerChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)

dataConstructor :: Parser ConName
dataConstructor =
  lexeme $ do
    x <- upperChar
    xs <- many identifierChar
    pure $ CN $ T.pack (x:xs)


-- identifiers: common
identifierChar :: Parser Char
identifierChar = alphaNumChar <|> char '\'' <|> try (char '-' <* notFollowedBy hspace1)


stringLiteral :: Parser Text
stringLiteral = do
  void $ char '\''
  s <- manyTill L.charLiteral (char '\'')
  return $ T.pack s

symbol :: Text -> Parser ()
symbol = void . L.symbol sc

keyword :: Text -> Parser ()
keyword kword = void $ lexeme (try $ string kword <* notFollowedBy identifierChar)

scope :: (a -> NonEmpty AnnStmt -> b) -> Parser a -> Parser b
scope f ref = recoverableIndentBlock $ do
  x <- ref
  return $ L.IndentSome Nothing (fmap (f x . NE.fromList) . annotateStatements) (annotationOr statement)

lineComment :: Parser ()
lineComment =
  try (string commentDelimeter <* notFollowedBy "[") *> void (takeWhileP (Just "character") (/= '\n'))

-- lineComment = L.skipLineComment "#"  -- previous implementation without considering annotations.

commentDelimeter :: Text
commentDelimeter = "#"


scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space hspace1 lineComment empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

retf :: f (Fix f) -> Parser (Fix f)
retf = return . Fix

-- As a complement to retf
ret :: a -> Parser a
ret = pure


-- Errors

data MyParseError = MyPE (Int, Int) MyParseErrorType
  deriving (Eq, Show, Ord)

data MyParseErrorType
  = DisallowedExpressionAsStatement
  deriving (Eq, Show, Ord)

instance ShowErrorComponent MyParseError where
  showErrorComponent (MyPE _ err) = case err of
    DisallowedExpressionAsStatement -> "Only call as an expression."

  errorComponentLen (MyPE (from, to) _) = to - from


registerCustom :: MyParseError -> Parser ()
registerCustom err@(MyPE (from, _) _) = registerParseError $ FancyError from $ Set.singleton $ ErrorCustom err

registerExpect :: Int -> Text -> [Text] -> Parser ()
registerExpect offset found expected = registerParseError $ TrivialError offset tokenFound tokenExpected
  where
    tokenFound = Just $ Tokens $ text2token found
    tokenExpected = Set.fromList $ map (Tokens . text2token) expected
    text2token = NE.fromList . T.unpack


recoverStmt :: Parser (Either [Ann] Stmt) -> Parser (Either [Ann] Stmt)
recoverStmt = recoverLine (Right Pass)

recoverCon :: Parser (Either [Ann] (Either DataRec DataCon)) -> Parser (Either [Ann] (Either DataRec DataCon))
recoverCon = recoverLine $ Right $ Right $ DC (CN "PLACEHOLDER") []

recoverLine :: a -> Parser a -> Parser a
recoverLine sentinel = withRecovery (\err -> registerParseError err >> many (anySingleBut '\n') >> char '\n' $> sentinel)


recoverableIndentBlock ::
  Parser (L.IndentOpt Parser a b) ->
  Parser a
recoverableIndentBlock r = do
  scn
  ref <- L.indentLevel
  a <- r
  case a of
    L.IndentNone x -> x <$ scn
    L.IndentMany indent f p -> do
      mlvl <- (optional . try) (C.eol *> L.indentGuard scn GT ref)
      done <- isJust <$> optional eof
      case (mlvl, done) of
        (Just lvl, False) ->
          indentedItems ref (fromMaybe lvl indent) p >>= f
        _ -> scn *> f []
    L.IndentSome indent f p -> do
      pos <- C.eol *> L.indentGuard scn GT ref
      let lvl = fromMaybe pos indent
      x <-
        if
          | pos <= ref -> L.incorrectIndent GT ref pos
          | pos == lvl -> p
          | otherwise -> L.incorrectIndent EQ lvl pos
      xs <- indentedItems ref lvl p
      f (x : xs)

indentedItems ::
  -- | Reference indentation level
  Pos ->
  -- | Level of the first indented item ('lookAhead'ed)
  Pos ->
  -- | How to parse indented tokens
  Parser b ->
  Parser [b]
indentedItems ref lvl p = go
  where
    go = do
      scn
      pos <- L.indentLevel
      done <- isJust <$> optional eof
      if done
        then return []
        else
          if
            | pos <= ref -> return []
            | pos == lvl -> (:) <$> p <*> go
            | otherwise -> do
              o <- getOffset
              registerParseError $ FancyError o $ Set.singleton $ ErrorIndentation EQ lvl pos
              (:) <$> p <*> go
