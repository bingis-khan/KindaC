{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Parser (parse) where

import AST


import Data.Void (Void)
import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import qualified Text.Megaparsec as TM (parse, parseMaybe, parseTest)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Bifunctor (first)
import Data.Functor (void)
import Data.Fix (Fix(Fix))
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Control.Applicative (liftA2)
import Data.Maybe (isNothing)
import Data.Text (Text)
import qualified Data.Text as T


type Parser = Parsec Void Text

lineComment :: Parser ()
lineComment = L.skipLineComment "#"

scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space hspace1 lineComment empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

sanitize :: Text -> Text
sanitize = T.concatMap sub
  where
    sub :: Char -> Text
    sub '\'' = "_prime"
    sub '_' = "__"
    sub s = T.singleton s

typeName :: Parser Text
typeName = do
  s <- lexeme $ do
    x <- upperChar
    xs <- many (alphaNumChar <|> char '\'')
    pure $ T.pack (x:xs)
  return $ sanitize s

identifierChar :: Parser Char
identifierChar = alphaNumChar <|> char '\''

identifier :: Parser Text
identifier = do
  s <- lexeme $ do
    x <- lowerChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)
  return $ sanitize s

dataConstructor :: Parser Text
dataConstructor = do
  s <- lexeme $ do
    x <- upperChar
    xs <- many identifierChar
    pure $ T.pack (x:xs)
  return $ sanitize s

varDec :: Parser Text
varDec = identifier

generic :: Parser TVar
generic = TV <$> varDec

-- parseType :: Parser Type
-- parseType = (Concrete <$>
--                 ((ClassType <$> typeName <*> return [])
--             <|> do
--                 params <- between (symbol "(") (symbol ")") $ parseType `sepBy` symbol ","
--                 returnType <- symbol "->" >> parseType
--                 return $ FunType $ FunctionType returnType params))
--         <|> (Polymorphic <$> generic)

symbol :: Text -> Parser Text
symbol = L.symbol sc

keyword :: Text -> Parser Text
keyword kword = lexeme (string kword <* notFollowedBy identifierChar)


binary :: Text -> (expr -> expr -> expr) -> Operator Parser expr
binary s f = InfixL $ f <$ symbol s

prefix :: Text -> (expr -> expr) -> Operator Parser expr
prefix name f = Prefix $ f <$ symbol name

call :: Operator Parser UExpr
call = Postfix $ do
    args <- between (symbol "(") (symbol ")") $ expr `sepBy` symbol ","
    return $ Fix . flip Call args
  
lambda :: Operator Parser UExpr
lambda = Prefix $ fmap (foldr1 (.)) $ some $ do
  params <- try $ (identifier `sepBy` symbol ",") <* symbol ":"
  return $ Fix . Lam (map Right params)

operatorTable :: [[Operator Parser UExpr]]
operatorTable =
  [   --[ Postfix $ some identifier <&> \members expr -> toExpr (MemberAccess expr members)
        --]
    [ call
    ]
    -- ,   [ prefix' "-" Negation
    --     , prefix' "not" Not
    --     ]
  , [ binary' "*" Times
    , binary' "/" Divide
    ]
  , [ binary' "+" Plus
    , binary' "-" Minus
    ]
  , [ binary' "==" Equals
    , binary' "/=" NotEquals
    ]
  , [ lambda
    ]
  ] where
    prefix' = prefix
    binary' name op = binary name $ \x y -> Fix (Op x op y)

term :: Parser UExpr
term = choice
  [ Fix . Lit . LInt <$> lexeme (L.signed sc L.decimal)
  --, symbol "True" >> return (Fix $ Lit $ LBool True)
  --, symbol "False" >> return (Fix $ Lit $ LBool False)
  , between (symbol "(") (symbol ")") expr
  , Fix . Var . Right <$> (identifier <|> dataConstructor)
  ]

expr :: Parser UExpr
expr = makeExprParser term operatorTable


definition :: Parser (StmtF Text g UExpr a)
definition = do
  name <- try $ identifier <* symbol "="

  Assignment name <$> expr

scope :: (a -> NonEmpty UStmt -> b) -> Parser a -> Parser b
scope f ref = L.indentBlock scn $ do
  x <- ref
  return $ L.IndentSome Nothing (return . f x . NE.fromList) stmt

scope' :: Parser (NonEmpty UStmt -> b) -> Parser b
scope' = scope ($)


ifStatement :: Parser (StmtF l g UExpr UStmt)
ifStatement = do
  (cond, ifBody) <- scope (,) $ keyword "if" >> expr
  elifs <- many $ scope (,) $ keyword "elif" >> expr
  elseBody <- optional $ scope (const id) $ keyword "else"

  return $ If cond ifBody elifs elseBody

stmtExpr :: Parser (StmtF l g UExpr UStmt)
stmtExpr = do
  expr@(Fix expr') <- expr
  case expr' of
    Call _ _ -> return (ExprStmt expr)
    _ -> fail "The only statement-expression thingy you can do is call."

stmt :: Parser UStmt
stmt = Fix <$> choice
  [ ifStatement
  , keyword "print" >> Print <$> expr
  , definition
  , keyword "return" >> Return <$> expr
  , stmtExpr
  ]

-- Iffy expression parser. When I add tuples *and* higher kinded types, we might be able to use the in-built expr parser.
-- Why iffy? I want '(' and ')' to be used solely as grouping, but they are kinda in-built right now.
parseType :: Parser UntypedType
parseType = choice
  [ funType
  , grouping
  , concrete
  , polyType
  ]
  where
    polyType = Fix . TDecVar <$> generic
    funType = do
      args <- try $ do
        params <- choice
          [ between (symbol "(") (symbol ")") $ parseType `sepBy` symbol "," 
          , (:[]) <$> (concrete <|> polyType)
          ]
        symbol "->"
        return params
      ret <- parseType
      return $ Fix $ TFun args ret
    
    grouping = between (symbol "(") (symbol ")") parseType

    concrete = do
      tcon <- typeName
      targs <- many $ grouping <|> polyType <|> ((\name -> Fix $ TCon name []) <$> typeName)
      return $ Fix $ TCon tcon targs

dataCon :: Parser UDataCon
dataCon = do
  conName <- typeName
  types <- many parseType
  return $ DC conName types

dataDec :: Parser UDataDec
dataDec = L.indentBlock scn $ do
  tname <- typeName
  polys <- many generic
  return $ L.IndentSome Nothing (return . DD tname polys . NE.fromList) dataCon


-- This'll be tricky: a function definition can look exactly like a function call. Welp, I guess I know why `def`s are needed.
-- Still, these are parser combinators - let them worry about proper backtracking.
-- We're gonna do it like this: try to parse a function definition - if we happen to parse any function-y stuff, we're happy, because it's a function.
-- However, for something like this:
-- id (x)
--  return x
-- We have to check if there are any indents. If there aren't -> it's a function.
-- Also, we should throw a custom error if we *know* it's a function, but there's now body.

-- If
onlyFunctionDeclaration :: Parser (Text, [(Text, Maybe UntypedType)], Either UExpr (Maybe UntypedType))
onlyFunctionDeclaration = do
  let param = liftA2 (,) identifier (optional parseType)

  name <- identifier
  params <- between (symbol "(") (symbol ")") $ sepBy param (symbol ",")
  ret <- choice
    [ Left <$> (symbol "=>" >> expr)
    , Right <$> optional (symbol "->" >> parseType)
    ]

  return (name, params, ret)

funDec :: Parser (Either UExpr UFunDec)
funDec = L.indentBlock scn $ do
  (name, params, exprOrRet) <- onlyFunctionDeclaration

  return $ case exprOrRet of
    Left expr -> L.IndentNone $ Right $ FD name params Nothing (NE.singleton (Fix (Return expr)))
    Right ret -> do

      -- If a function has no declared types, we need to check if it's actually a function or a call:
      let eitherCallOrFunction = \case
            [] -> Left $ Fix $ Call (Fix (Var (Right name))) (map (Fix . Var . Right . fst) params)   -- This means it's a function call.
            x : xs -> Right $ FD name params ret (x :| xs)                             -- A non-empty body means it's a function definition.

      if all (isNothing . snd) params && isNothing ret
        then L.IndentMany Nothing (return . eitherCallOrFunction) stmt  -- Might be a function call.
        else L.IndentSome Nothing (return . Right . FD name params ret . NE.fromList) stmt



topLevel :: Parser TopLevel
topLevel
  =   DataDec <$> dataDec
  -- Okay, this is fucking stupid, but it's necessary to differentiate function definitions and calls.
  <|> (try (lookAhead (onlyFunctionDeclaration >> eol)) >> either (TLStmt . Fix . ExprStmt) FunDec <$> funDec)
  <|> TLStmt <$> stmt

parse :: Text -> Either String [TopLevel]
parse = first errorBundlePretty . TM.parse (scn >> many (L.nonIndented sc topLevel <* scn) <* eof) "fairu"
