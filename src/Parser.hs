{-# LANGUAGE LambdaCase, OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedRecordDot #-}

module Parser (parse) where


import Text.Megaparsec hiding (parse)
import Text.Megaparsec.Char
import qualified Text.Megaparsec as TM (parse)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import Data.Bifunctor (first, bimap)
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
import AST.Def (Ann (..), TCon (..), ConName (..), VarName (..), Annotated (..), Op (..), LitType (..), (:.) (..), ctx, UnboundTVar (..), MemName (..), ClassName (..))
import AST.Common (ExprF (..), FunDec (..), DataCon (..), TypeF (..), StmtF (..), DataDef (..), DeconF (..), Module, Stmt, Decon, Expr, AnnStmt, Type, CaseF (..), Case, ClassFunDec (..), ClassDef (..), InstDef (..), ClassType, ClassTypeF (..), XMem, IfStmt (..), InstFun (..), XClassConstraints, Node (..), DeclaredType (..), MutAccess (..))
import Data.Functor.Foldable (cata)
import Control.Monad ((<=<))
import Data.Either (partitionEithers)
import AST.Untyped (Untyped, U, UntypedStmt (..), ClassConstraint (..))
import qualified AST.Untyped as U
import qualified AST.Common as Common


type Parser = Parsec MyParseError Text
type FileName = String

parse :: FileName -> Text -> Either Text (Module Untyped)
parse filename = first (Text.pack . errorBundlePretty) . TM.parse (scn >> topLevels <* eof) filename


-- Top level
topLevels :: Parser (Module Untyped)
topLevels = do
  eas <- many $ recoverStmt (L.nonIndented sc  (annotationOr statement)) <* scn
  ustmts <- annotateStatements eas
  pure $ U.Mod ustmts



------------------------
-- Parsing statements --
------------------------

statement :: Parser (Stmt Untyped)
statement = choice
  [ sPass
  , sCase
  , sIf
  , sPrint
  , sReturn
  , sWhile

  , sClass
  , sInst

  , sDataDefinition

  , sDefinition
  , sMutAssignment

  , try (checkIfFunction >> sFunctionOrCall)
  , sExpression
  ]

-- Each statement
sPass :: Parser (Stmt Untyped)
sPass = do
  keyword "pass"
  pure Pass

sIf :: Parser (Stmt U)
sIf = do
  (cond, ifBody) <- scope (,) (keyword "if" >> expression)
  elifs <- many $ scope (,) (keyword "elif" >> expression)
  elseBody <- optional $ scope (const id) (keyword "else")
  pure $ If $ IfStmt cond ifBody elifs elseBody

sCase :: Parser (Stmt U)
sCase = recoverableIndentBlock $ do
  -- case header
  keyword "case"
  condition <- expression

  -- switch inner
  pure $ L.IndentSome Nothing (pure . Switch condition . NE.fromList) sSingleCase

sSingleCase :: Parser (Case U)
sSingleCase = scope id $ do
  -- deconstructor
  decon <- sDeconstruction

  -- parse expression here in the future
  pure $ Case decon Nothing

sDeconstruction :: Parser (Decon U)
sDeconstruction = caseVariable <|> caseRecord <|> caseConstructor
 where
    caseVariable = node . CaseVariable <$> variable
    caseConstructor =  fmap node $ CaseConstructor <$> dataConstructor <*> args
    caseRecord = do
      name <- try $ typeName <* lookAhead (symbol "{")
      decons <- NonEmpty.fromList <$> between (symbol "{") (symbol "}") (sepBy1 recordFieldDecon (symbol ","))
      pure $ node $ CaseRecord name decons

    recordFieldDecon = do
      fieldName <- member
      symbol ":"
      decon <- sDeconstruction
      pure (fieldName, decon)


    args = do
      between (symbol "(") (symbol ")") (sepBy1 sDeconstruction (symbol ",")) <|> pure []

sPrint :: Parser (Stmt U)
sPrint = do
  keyword "print"
  expr <- expression
  pure $ Print expr

sDefinition :: Parser (Stmt U)
sDefinition = do
  name <- try $ variable <* symbol "="
  rhs <- expression
  pure $ Assignment name rhs

sMutAssignment :: Parser (Stmt U)
sMutAssignment = do
  (name, accesses) <- try $ do
    v <- variable
    accesses <- thatFunnyMutationOperator
    pure (v, accesses)
  rhs <- expression
  pure $ Mutation name () accesses rhs

-- maybe it's overly permissive?
--  I don't think I want to accept < .dupa=
--  or < & .dupa =
thatFunnyMutationOperator :: Parser [MutAccess U]
thatFunnyMutationOperator = lexeme $ do
  -- very strict parser
  -- _ <- char '<'
  -- accesses <- many $ choice
  --   [ char '&' $> MutRef
  --   , char '.' >> MutField <$> member
  --   ]
  -- _ <- char '='
  symbol "<"
  accesses <- many $ choice
    [ symbol "&" $> MutRef
    , symbol "." >> MutField <$> member
    ]
  symbol "="
  pure accesses

sReturn :: Parser (Stmt U)
sReturn = do
  keyword "return"
  expr <- optional expression
  pure $ Return expr

sWhile :: Parser (Stmt U)
sWhile = scope While $ keyword "while" >> expression

sClass :: Parser (Stmt U)
sClass = recoverableIndentBlock $ do
  keyword "class"
  name <- className
  return $ flip (L.IndentMany Nothing) sDefinedFunctionHeader $ \funs ->
    -- let (deps, funs) = partitionEithers depsOrFunctions
    pure $ Other $ ClassDefinition $ ClassDef
      { classID = name
      -- , classDependentTypes = deps  -- TODO: add later
      , classFunctions = funs
      }

-- sDepOrFunctionDec :: Parser (Either DependentType ClassFunDec)
-- sDepOrFunctionDec = Left <$> sDepDec <|> Right <$> sDefinedFunctionHeader

-- sDepDec :: Parser DependentType
-- sDepDec = Dep <$> typeName

sDefinedFunctionHeader :: Parser (ClassFunDec U)
sDefinedFunctionHeader = do
  name <- variable

  let param = liftA2 (,) sDeconstruction pClassType
  params <- between (symbol "(") (symbol ")") $ sepBy param (symbol ",")

  symbol "->"  -- or just assume that no return = Unit
  ret <- pClassType

  constraints <- sClassConstraints

  pure $ CFD () name params ret constraints


sInst :: Parser (Stmt Untyped)
sInst = recoverableIndentBlock $ do
  keyword "inst"
  name <- className

  instType <- do
    tcon <- typeName
    targs <- many generic
    pure (tcon, targs)

  constraints <- sClassConstraints

  pure $ flip (L.IndentMany Nothing) sInstFunction $ \funs ->
    -- let (deps, funs) = partitionEithers depOrFunctions
    pure $ Inst $ InstDef
      { instClass = name
      , instType = instType
      , instConstraints = constraints
      -- , instDependentTypes = deps
      , instFuns = funs
      }


sClassConstraints :: Parser (XClassConstraints U)
sClassConstraints = do
  mConstraints <- optional $ do
    symbol "<="  -- I might change it to "|"? may look prettier?
    sepBy1 sClassConstraint (symbol ",")

  pure $ fromMaybe [] mConstraints

sClassConstraint :: Parser U.ClassConstraint
sClassConstraint = do
  name <- className
  tv <- generic
  pure $ CC name tv


-- sDepOrFunctionDef :: Parser (Either (DependentType, ClassType) (FunDec, NonEmpty AnnStmt))
-- sDepOrFunctionDef = Left <$> sDepDef <|> Right <$> sInstFunction

-- sDepDef :: Parser (DependentType, ClassType)
-- sDepDef = do
--   depname <- sDepDec
--   symbol "="
--   typ <- pClassType

--   pure (depname, typ)

sInstFunction :: Parser (InstFun U)
sInstFunction = recoverableIndentBlock $ do
  (header, mExpr) <- functionHeader
  case mExpr of
    Just expr ->
      let expr2stmt = Fix . O . Annotated [] . Return . Just
          stmt = expr2stmt expr
          body = NonEmpty.singleton stmt
      in pure $ L.IndentNone $ InstFun { instFunDec = header, instFunBody = body, instClassFunDec = (), instDef = () }
    Nothing -> do
      pure $ flip (L.IndentSome Nothing) (recoverStmt (annotationOr statement)) $ \annsOrStmts -> do
        stmts <- NonEmpty.fromList <$> annotateStatements annsOrStmts
        pure $ InstFun { instFunDec = header, instFunBody = stmts, instClassFunDec = (), instDef = () }


sExpression :: Parser (Stmt U)
sExpression = do
  from <- getOffset
  expr@(Fix (N _ chkExpr)) <- expression
  to <- getOffset
  case chkExpr of
    Call _ _ -> pure $ ExprStmt expr
    _ -> do
      registerCustom $ MyPE (from, to) DisallowedExpressionAsStatement
      pure $ ExprStmt expr  -- report an error, but return this for AST


checkIfFunction :: Parser ()
checkIfFunction = void $ lookAhead (functionHeader >> eol)

sFunctionOrCall :: Parser (Stmt U)
sFunctionOrCall = recoverableIndentBlock $ do
  (header, mExpr) <- functionHeader

  -- If it's a single expression function (has the ':'), we know it's not a call.
  ret $ case mExpr of
    Just expr ->
      let expr2stmt = Fix . O . Annotated [] . Return . Just
          stmt = expr2stmt expr
          body = NonEmpty.singleton stmt
      in L.IndentNone $ Fun $ U.FunDef header body

    Nothing ->
      -- If that's a normal function, we check if any types were defined
      let types = header.functionReturnType : map snd header.functionParameters
      in if any Common.isTypeDeclared types || not (null header.functionOther)
        then L.IndentSome Nothing (fmap (Fun . U.FunDef header . NonEmpty.fromList) . annotateStatements) $ recoverStmt (annotationOr statement)
        else flip (L.IndentMany Nothing) (recoverStmt (annotationOr statement)) $ \case
          stmts@(_:_) -> Fun . U.FunDef header . NonEmpty.fromList <$> annotateStatements stmts
          [] ->
            let args = map (deconToExpr . fst) header.functionParameters
                funName = node $ Var header.functionId ()
            in pure $ ExprStmt $ node $ Call funName args

-- some construction might also be misrepresented as a deconstruction.
deconToExpr :: Decon U -> Expr U
deconToExpr = cata $ \(N _ decon) -> node $ case decon of
  CaseVariable v                  -> Var v ()
  CaseConstructor con []          -> Con con ()
  CaseConstructor con exprs@(_:_) -> Call (node $ Con con ()) exprs
  CaseRecord con mems             -> RecCon con mems

functionHeader :: Parser (FunDec U, Maybe (Expr U))
functionHeader = do
  let param = liftA2 (,) sDeconstruction (Common.fromMaybeToDeclaredType <$> optional pType)
  name <- variable
  params <- between (symbol "(") (symbol ")") $ sepBy param (symbol ",")
  ret <- choice
    [ Left <$> (symbol ":" >> expression)
    , Right <$> optional (symbol "->" >> pType)
    ]

  constraints <- sClassConstraints

  return $ case ret of
    Left expr -> (FD () name params TypeNotDeclared constraints, Just expr)
    Right mType -> (FD () name params (Common.fromMaybeToDeclaredType mType) constraints, Nothing)


-- Data definitions.
--   Either a normal ADT or a record type.
sDataDefinition :: Parser (Stmt U)
sDataDefinition = recoverableIndentBlock $ do
  tname <- typeName
  polys <- many generic
  return $ flip (L.IndentMany Nothing) (recoverCon conOrRecOrAnnotation) $ toRecordOrADT tname polys <=< assignAnnotations (\ann -> bimap (Annotated ann) (\fdc -> fdc ann))
   where
    conOrRecOrAnnotation :: Parser (Either [Ann] (Either (XMem U, Type U) ([Ann] -> DataCon U)))
    conOrRecOrAnnotation = Left <$> annotation <|> Right . Left <$> dataRec <|> Right . Right <$> dataCon

    toRecordOrADT :: TCon -> [UnboundTVar] -> [Either (Annotated (XMem U, Type U)) (DataCon U)] -> Parser (Stmt U)
    -- empty datatype
    toRecordOrADT tname polys [] = pure $ Other $ DataDefinition $ DD tname polys (Right []) []

    toRecordOrADT tname polys (first : rest) =
      let (records, cons) = partitionEithers rest
      in case first of
        Left rec ->
          case cons of
            [] ->
              pure $ Other $ DataDefinition $ DD tname polys (Left $ rec :| records) []

            _:_ -> do
              fail "Encountered constructors in a Record definition."

        Right dc ->
          case records of
            [] ->
              pure $ Other $ DataDefinition $ DD tname polys (Right $ dc : cons) []
            _:_ -> do
              fail "Encountered record fields in an ADT definition."  -- should not end parsing, but im lazy.


dataRec :: Parser (XMem U, Type U)
dataRec = do
  recordName <- member
  recordType <- pType
  pure (recordName, recordType)

dataCon :: Parser ([Ann] -> DataCon U)
dataCon = do
  conName <- dataConstructor
  types <- many typeTerm
  return $ DC () conName types



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
      case key of
        "ctype" -> do
          value <- stringLiteral
          ann $ ACType value
        "cstdinclude" -> do
          value <- stringLiteral
          ann $ ACStdInclude value
        "clit" -> do
          value <- stringLiteral
          ann $ ACLit value
        "actual-pointer-type" -> ann AActualPointerType
        unknownKey -> do
          registerExpect keyOffset unknownKey ["ctype", "cstdinclude", "clit"]
          pure Nothing
        where
          ann = pure . Just

annotateStatements :: [Either [Ann] (Stmt U)] -> Parser [AnnStmt U]
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

expression :: Parser (Expr U)
expression = makeExprParser term operatorTable

operatorTable :: [[Operator Parser (Expr U)]]
operatorTable =
  [ [ interleavable
    , recordUpdate
    ]
  -- , [ prefix "-" Negation
  --   , prefix "not" Not
  --   ]
  , [ binary' "*" Times
    , binaryS' (try $ symbol "/" <* notFollowedBy "=") Divide
    ]
  , [ binary' "+" Plus
    , binary' "-" Minus
    ]
  , [ binary' "==" Equals
    , binary' "/=" NotEquals
    , binary' "<"  LessThan
    , binary' ">"  GreaterThan
    ]
  , [ as
    ]

  -- examples to figure out precedence for ref:
  -- fn =& :420
  -- cmp-ref = x: &x
  , [ lowPrecedencePrefixOps
    ]
  ] where
    binary' name op = binary name $ \x y -> Fix $ N () $ Op x op y
    binaryS' name op = binaryS name $ \x y -> Fix $ N () $ Op x op y

binaryS :: Parser () -> (expr -> expr -> expr) -> Operator Parser expr
binaryS s f = InfixL $ f <$ s

binary :: Text -> (expr -> expr -> expr) -> Operator Parser expr
binary s f = InfixL $ f <$ symbol s

-- For some reason (i dunno, maybe that's how the OperatorTable works.), we can't properly chain postfix operators.
-- Making a general function like this is a fix for that.
interleavable :: Operator Parser (Expr U)
interleavable = Postfix $ fmap (foldl1 (.) . reverse) $ some $ choice
  [ subscript
  , call
  , deref
  ]

deref :: Parser (Expr U -> Expr U)
deref = symbol "&" $> node . Deref

subscript :: Parser (Expr U -> Expr U)
subscript = (symbol "." >> member) <&> \memname e -> node $ MemAccess e memname

call :: Parser (Expr U -> Expr U)
call = do
    args <- between (symbol "(") (symbol ")") $ expression `sepBy` symbol ","
    return $ node . flip Call args

recordUpdate :: Operator Parser (Expr U)
recordUpdate = Postfix $ between (symbol "{") (symbol "}") $ do
  mems <- NonEmpty.fromList <$> sepBy1 memberdef (symbol ",")
  return $ node . flip RecUpdate mems

as :: Operator Parser (Expr U)
as = Postfix $ do
    symbol "as"
    t <- pType
    return $ node . flip As t


lowPrecedencePrefixOps :: Operator Parser (Expr U)
lowPrecedencePrefixOps = Prefix $ fmap (foldr1 (.)) $ some $ choice
  [ ref
  , lambda
  ]

ref :: Parser (Expr U -> Expr U)
ref = symbol "&" $> node . Ref

lambda :: Parser (Expr U -> Expr U)
lambda = do
  -- Correct lambda:
  -- :420
  -- x: x + 1
  -- (x, y): x + y
  -- NOTE: right now we also allow '(): 420' This might later be known as Unit deconstruction, so might have to interpret it as this?
  let multipleParams = between "(" ")" (variable `sepBy` symbol ",") <|> ((:[]) <$> variable)
  let singleParam = variable <&> (:[])
  let paramList = fromMaybe [] <$> optional (multipleParams <|> singleParam)
  params <- try $ paramList <* symbol ":"
  return $ node . Lam () params

node :: nodeF U (Fix (Node U nodeF)) -> Fix (Node U nodeF)
node = Fix . N ()


-----------
-- Terms --
-----------

term :: Parser (Expr U)
term = choice
  [ eDecimal
  , eGrouping
  , eRecordConstruction
  , eIdentifier
  ]

eDecimal :: Parser (Expr U)
eDecimal = do
  decimal <- lexeme (L.signed sc L.decimal)
  retfe $ Lit $ LInt decimal

eGrouping :: Parser (Expr U)
eGrouping = between (symbol "(") (symbol ")") expression

eIdentifier :: Parser (Expr U)
eIdentifier = do
  id <- (flip Var () <$> variable) <|> (Con <$> dataConstructor <*> pure ())
  retfe id

eRecordConstruction :: Parser (Expr U)
eRecordConstruction = do
  name <- try $ typeName <* lookAhead (symbol "{")
  recordDef <- NonEmpty.fromList <$> between (symbol "{") (symbol "}") (sepBy1 memberdef (symbol ","))

  retfe $ RecCon name recordDef

memberdef :: Parser (MemName, Expr U)
memberdef = do
      mem <- member
      symbol ":"
      e <- expression
      pure (mem, e)

-----------
-- Types --
-----------

-- This is used to parse a standalone type
pType :: Parser (Type U)
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
      ts -> fail $ "Cannot use an argument list as a return value. (you forgot to write a return type for the function.) (" <> concatMap ctx ts <> ")"  -- this would later mean that we're returning a tuple, so i'll leave it be.
    Just ret -> return $ Fix $ TFun () term ret

  where
    concrete = do
      tcon <- typeName
      targs <- many typeTerm
      return $ Fix $ TCon tcon targs ()
    groupingOrParams = between (symbol "(") (symbol ")") $ sepBy pType (symbol ",")

-- This is used to parse a type "term", for example if you're parsing a data definition.
-- Ex. you cannot do this: Int -> Int, you have to do this: (Int -> Int)
typeTerm :: Parser (Type U)
typeTerm = choice
  [ grouping
  , poly
  , concreteType
  ]
  where
    grouping = between (symbol "(") (symbol ")") pType
    concreteType = do
      tname <- typeName
      retf $ TCon tname [] ()

poly :: Parser (Type U)
poly = Fix . TO <$> generic


-- COPIED FROM pType n shit. uhh.... Because I don't have an "identity" constructor in the TypeF datatype, I can't use fixpoint functions.
pClassType :: Parser (ClassType U)
pClassType
  =   Fix Self <$ symbol "_"
  <|> do
        term <- choice
          [ (:[]) <$> concrete
          , (:[]) . Fix . NormalType . TO <$> generic
          , groupingOrParams
          ]

        fun <- optional $ do
          symbol "->"
          pClassType
        case fun of
          Nothing -> case term of
            [t] -> return t
            ts -> fail $ "Cannot use an argument list as a return value. (you forgot to write a return type for the function.) (" <> concatMap ctx ts <> ")"  -- this would later mean that we're returning a tuple, so i'll leave it be.
          Just ret -> return $ Fix $ NormalType $ TFun () term ret

        where
          concrete = do
            tcon <- typeName
            targs <- many classTypeTerm
            return $ Fix $ NormalType $ TCon tcon targs ()
          groupingOrParams = between (symbol "(") (symbol ")") $ sepBy pClassType (symbol ",")

classTypeTerm :: Parser (ClassType U)
classTypeTerm = choice
  [ Fix Self <$ symbol "_"
  , grouping
  , Fix . NormalType . TO <$> generic
  , concreteType
  ]
  where
    grouping = between (symbol "(") (symbol ")") pClassType
    concreteType = do
      tname <- typeName
      retf $ NormalType $ TCon tname [] ()



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

className :: Parser ClassName
className = TCN . fromTC <$> typeName

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

scope :: (a -> NonEmpty (AnnStmt U) -> b) -> Parser a -> Parser b
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

retfe :: ExprF U (Expr U) -> Parser (Expr U)
retfe = return . Fix . N ()

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


recoverStmt :: Parser (Either [Ann] (Stmt U)) -> Parser (Either [Ann] (Stmt U))
recoverStmt = recoverLine (Right Pass)

recoverCon :: Parser (Either [Ann] (Either (XMem U, Type U) ([Ann] -> DataCon U))) -> Parser (Either [Ann] (Either (XMem U, Type U) ([Ann] -> DataCon U)))
recoverCon = recoverLine $ Right $ Right $ DC () (CN "PLACEHOLDER") []

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
