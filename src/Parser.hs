{-# LANGUAGE LambdaCase, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Parser (parse) where

import AST hiding (typeName)


import Data.Void (Void)
import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import qualified Text.Megaparsec as TM (parse)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Bifunctor (first)
import Data.Functor (void)
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE

import Data.Maybe (isJust, catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty
import Data.Foldable (foldl')
import Debug.Trace (traceShowId)
import qualified Data.Set as Set


type Parser = Parsec Void Text
type FileName = String

parse :: FileName -> Text -> Either Text (Module Untyped)
parse filename = first (Text.pack . errorBundlePretty) . TM.parse (scn >> topLevels <* eof) filename


-- Top level
topLevels :: Parser (Module Untyped)
topLevels = do
  eas <- many $ L.nonIndented sc (annotationOr statement) <* scn
  annotateStatements $ traceShowId eas



------------------------
-- Parsing statements --
------------------------

statement :: Parser (Stmt Untyped)
statement = choice
  [ sIf
  , sPrint
  , sReturn
  , sDataDefinition

  , sDefinition

  , sMutDefinition
  , sMutAssignment

  , try (checkIfFunction >> sFunctionOrCall)
  , sExpression
  ]

-- Each statement
sIf :: Parser (Stmt Untyped)
sIf = do
  (cond, ifBody) <- scope (,) (keyword "if" >> expression)
  elifs <- many $ scope (,) (keyword "elif" >> expression)
  elseBody <- optional $ scope (const id) (keyword "else")
  ret $ If cond ifBody elifs elseBody

sPrint :: Parser (Stmt Untyped)
sPrint = do
  keyword "print"
  expr <- expression
  ret $ Print expr

sDefinition :: Parser (Stmt Untyped)
sDefinition = do
  name <- try $ identifier <* symbol "="
  rhs <- expression
  ret $ Assignment name rhs

sMutDefinition :: Parser (Stmt Untyped)
sMutDefinition = do
  keyword "mut"
  name <- identifier
  rhs <- optional $ symbol "<=" *> expression  -- I'm not sure if this should be optional (design reason: i want users to use inline if/case/whatever for conditional assignment). Right now we'll allow it, as it's easy to disallow it anyway.
  ret $ MutDefinition name rhs

sMutAssignment :: Parser (Stmt Untyped)
sMutAssignment = do
  name <- try $ identifier <* symbol "<="
  rhs <- expression
  ret $ MutAssignment name rhs

sReturn :: Parser (Stmt Untyped)
sReturn = do
  keyword "return"
  expr <- expression
  ret $ Return expr

sExpression :: Parser (Stmt Untyped)
sExpression = do
  expr@(Fix chkExpr) <- expression
  case chkExpr of
    Call _ _ -> ret $ ExprStmt expr
    _ -> fail "The only statement-expression thingy you can do is call."


checkIfFunction :: Parser ()
checkIfFunction = void $ lookAhead (functionHeader >> eol)

sFunctionOrCall :: Parser (Stmt Untyped)
sFunctionOrCall = L.indentBlock scn $ do
  (header, mExpr) <- functionHeader

  -- If it's a single expression function (has the ':'), we know it's not a call.
  ret $ case mExpr of
    Just expr ->
      let expr2stmt = Fix . AnnStmt [] . ExprStmt
          stmt = expr2stmt expr
          body = NonEmpty.singleton stmt
      in L.IndentNone $ FunctionDefinition header body

    Nothing ->
      -- If that's a normal function, we check if any types were defined
      let (FD name params rett) = header
          types = rett : map snd params
      in if any isJust types
        then L.IndentSome Nothing (fmap (FunctionDefinition header . NonEmpty.fromList) . annotateStatements) (annotationOr statement)
        else flip (L.IndentMany Nothing) (annotationOr statement) $ \case
          stmts@(_:_) -> FunctionDefinition header . NonEmpty.fromList <$> annotateStatements stmts
          [] ->
            let args = map (Fix . Var . fst) params
                funName = Fix $ Var name
            in ret $ ExprStmt $ Fix $ Call funName args

functionHeader :: Parser (FunDec Untyped, Maybe (Expr Untyped))
functionHeader = do
  let param = liftA2 (,) identifier (optional pType)
  name <- identifier
  params <- between (symbol "(") (symbol ")") $ sepBy param (symbol ",")
  ret <- choice
    [ Left <$> (symbol ":" >> expression)
    , Right <$> optional (symbol "->" >> pType)
    ]

  return $ case ret of
    Left expr -> (FD name params Nothing, Just expr)
    Right mType -> (FD name params mType, Nothing)


-- Data definitions
sDataDefinition :: Parser (Stmt Untyped)
sDataDefinition = L.indentBlock scn $ do
  tname <- typeName
  polys <- many generic
  return $ L.IndentMany Nothing (fmap (DataDefinition . DD tname polys) . assignAnnotations (\anns (DC name ts _) -> DC name ts anns)) conOrAnnotation
  where
    conOrAnnotation :: Parser (Either [Ann] (DataCon Untyped))
    conOrAnnotation = Left <$> annotation <|> Right <$> dataCon

dataCon :: Parser (DataCon Untyped)
dataCon = do
  conName <- typeName
  types <- many pType
  return $ DC conName types []  -- annotations will be added during parsing data constructor



-----------------
-- Annotations --
-----------------

annotation :: Parser [Ann]
annotation = do
  void $ string commentDelimeter  -- Important that we don't consume whitespace after this (symbol consumes whitespace at the end).
  manns <- between (symbol "[") (symbol "]") $ annotation `sepBy` symbol ","
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
          return Nothing
        where
          ann = pure . Just

annotateStatements :: [Either [Ann] (Stmt Untyped)] -> Parser [AnnStmt Untyped]
annotateStatements = assignAnnotations $ \anns stmt -> Fix $ AnnStmt anns stmt

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

expression :: Parser (Expr Untyped)
expression = makeExprParser term operatorTable

operatorTable :: [[Operator Parser (Expr Untyped)]]
operatorTable =
  [   --[ Postfix $ some identifier <&> \members expr -> toExpr (MemberAccess expr members)
        --]
    [ call
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

call :: Operator Parser (Expr Untyped)
call = Postfix $ fmap (foldr1 (.) . reverse) $ some $ do
    args <- between (symbol "(") (symbol ")") $ expression `sepBy` symbol ","
    return $ Fix . flip Call args

as :: Operator Parser (Expr Untyped)
as = Postfix $ do
    symbol "as"
    t <- pType
    return $ Fix . flip As t

lambda :: Operator Parser (Expr Untyped)
lambda = Prefix $ fmap (foldr1 (.)) $ some $ do
  params <- try $ (identifier `sepBy` symbol ",") <* symbol ":"
  return $ Fix . Lam params


-----------
-- Terms --
-----------

term :: Parser (Expr Untyped)
term = choice
  [ eDecimal
  --, symbol "True" >> return (Fix $ Lit $ LBool True)
  --, symbol "False" >> return (Fix $ Lit $ LBool False)
  , eGrouping
  , eIdentifier
  ]

eDecimal :: Parser (Expr Untyped)
eDecimal = do
  decimal <- lexeme (L.signed sc L.decimal)
  retf $ Lit $ LInt decimal

eGrouping :: Parser (Expr Untyped)
eGrouping = between (symbol "(") (symbol ")") expression

eIdentifier :: Parser (Expr Untyped)
eIdentifier = do
  id <- (Var <$> identifier) <|> (Con <$> dataConstructor)
  retf id


-----------
-- Types --
-----------

-- This is used to parse a standalone type
pType :: Parser (Type Untyped)
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
      ts -> fail $ "Cannot use an argument list as a return value. (you forgot to write a return type for the function.) (" <> show ts <> ")"  -- this would later mean that we're returning a tuple
    Just ret -> return $ Fix $ TFun term ret

  where
    concrete = do
      tcon <- typeName
      targs <- many typeTerm
      return $ Fix $ TCon tcon targs
    groupingOrParams = between (symbol "(") (symbol ")") $ sepBy pType (symbol ",")

-- This is used to parse a type "term", for example if you're parsing a data definition.
-- Ex. you cannot do this: Int -> Int, you have to do this: (Int -> Int)
typeTerm :: Parser (Type Untyped)
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

poly :: Parser (Type Untyped)
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
typeName :: Parser Text
typeName = do
  lexeme $ do
    x <- upperChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)

generic :: Parser TVar
generic = TV <$> varDec

varDec :: Parser Text
varDec = identifier


-- term-level identifiers
identifier :: Parser Text
identifier = do
  lexeme $ do
    x <- lowerChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)

dataConstructor :: Parser Text
dataConstructor =
  lexeme $ do
    x <- upperChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)


-- identifiers: common
identifierChar :: Parser Char
identifierChar = alphaNumChar <|> char '\''


stringLiteral :: Parser Text
stringLiteral = do
  void $ char '\''
  s <- manyTill L.charLiteral (char '\'')
  return $ T.pack s

-- parseType :: Parser Type
-- parseType = (Concrete <$>
--                 ((ClassType <$> typeName <*> return [])
--             <|> do
--                 params <- between (symbol "(") (symbol ")") $ parseType `sepBy` symbol ","
--                 returnType <- symbol "->" >> parseType
--                 return $ FunType $ FunctionType returnType params))
--         <|> (Polymorphic <$> generic)

symbol :: Text -> Parser ()
symbol = void . L.symbol sc

keyword :: Text -> Parser ()
keyword kword = void $ lexeme (string kword <* notFollowedBy identifierChar)

scope :: (a -> Data.List.NonEmpty.NonEmpty (AnnStmt Untyped) -> b) -> Parser a -> Parser b
scope f ref = L.indentBlock scn $ do
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

registerExpect :: Int -> Text -> [Text] -> Parser ()
registerExpect offset found expected = registerParseError $ TrivialError offset tokenFound tokenExpected
  where
    tokenFound = Just $ Tokens $ text2token found
    tokenExpected = Set.fromList $ map (Tokens . text2token) expected
    text2token = NE.fromList . T.unpack
