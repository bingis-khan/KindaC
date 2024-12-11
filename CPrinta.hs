{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module CPrinta (cModule) where

import AST.Common (Ann (..), Annotated (..), EnvID, Locality (..), Op (..), TCon (..), UnionID, UniqueCon, UniqueType (..), UniqueVar, type (:.) (..))
import qualified AST.Common as M
import AST.Converged (Prelude, boolTypeName, intTypeName, unitName)
import AST.Mono (Case (..), DataCon, DataDef, DeconF (..), ExprF (..), FunDec, Function, StmtF (..))
import qualified AST.Mono as M
import Control.Monad (unless, when)
import Control.Monad.Trans.RWS (RWS)
import qualified Control.Monad.Trans.RWS as RWS
import Control.Monad.Trans.RWS.CPS (RWST)
import Control.Monad.Trans.Writer (Writer)
-- import Data.List (unsnoc)

import Data.Biapplicative (first, second)
import Data.Bool (bool)
import Data.Fix (Fix (..))
import Data.Foldable (foldl', for_, sequenceA_, traverse_)
import Data.Functor ((<&>))
import Data.Functor.Foldable (cata, histo, para, project)
import Data.List (find)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String (IsString (..))
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Traversable (for)
import Data.Unique (hashUnique)
import Debug.Trace (traceShow, traceShowId, traceShowWith)
import GHC.Base (NonEmpty ((:|)))
import GHC.Num (Natural)

-- todo: some function order cleanup after it works

-- Global PP state.
newtype PPG a = PP {fromPP :: RWS () [Text] Context a} deriving (Functor, Applicative, Monad)

type PP = PPG ()

instance (a ~ ()) => Semigroup (PPG a) where
  PP l <> PP r = PP $ l >> r

instance (a ~ ()) => Monoid (PPG a) where
  mempty = PP $ RWS.rws $ \_ s -> (mempty, s, [])

-- Line (Expression) PP state.
newtype PPL a = PL {fromPL :: RWS () [Text] (Context, [AdditionalLine]) a} deriving (Functor, Applicative, Monad)

type PL = PPL ()

type AdditionalLine = PP -- TODO: maybe make it text, so everything evaluates correctly.

instance (a ~ ()) => Semigroup (PPL a) where
  PL l <> PL r = PL $ l >> r

instance (a ~ ()) => Monoid (PPL a) where
  mempty = PL $ RWS.rws $ \_ s -> (mempty, s, [])

---- maybe i should add a third type for resolving environments and unions (but again this should probably be done in the monomorphizer)

-- Basic operators + transitions
pl :: PPL a -> PPG a
pl (PL p) = do
  -- RWS.mapRWS (\(a, _, t) -> (a, extra, [Text.concat t])) p.fromPL
  r <- PP RWS.ask
  context <- PP RWS.get

  let (x, (context', precedingLines), tokens) = RWS.runRWS p r (context, [])
  let line = Text.concat tokens
  PP $ RWS.put context'

  sequenceA_ $ reverse precedingLines
  PP $ RWS.tell [line]

  pure x

statement :: PL -> PP
statement p = pl $ p & ";"

infixr 7 &

(&) :: PL -> PL -> PL
(&) = (<>)

infixr 6 § -- hihi

(§) :: PL -> PL -> PL
(§) p1 p2 = p1 & " " & p2

-- join with next line
infixr 5 &>

(&>) :: PL -> PP -> PP
(&>) l r = do
  line <- pl $ Text.concat <$> carvel l
  lins <- carveg r
  PP $ case lins of
    [] -> RWS.tell [line]
    (li : lis) -> RWS.tell $ (line <> li) : lis

infixl 5 §>

(§>) :: PL -> PP -> PP
(§>) l r = do
  line <- pl $ Text.concat <$> carvel l
  lins <- carveg r
  PP $ case lins of
    [] -> RWS.tell [line]
    (li : lis) | Text.null line -> RWS.tell $ li : lis
    (li : lis) -> RWS.tell $ (line <> " " <> li) : lis

infixr 4 <&

(<&) :: PP -> PL -> PP
(<&) l r = do
  lins <- carveg l
  line <- pl $ Text.concat <$> carvel r
  PP $ case unsnoc lins of
    Nothing -> RWS.tell [line]
    Just (lls, ll) | Text.null line -> RWS.tell $ lls ++ [ll]
    Just (lls, ll) -> RWS.tell $ lls ++ [ll <> line]

infixr 4 <§

(<§) :: PP -> PL -> PP
(<§) l r = do
  lins <- carveg l
  line <- pl $ Text.concat <$> carvel r
  PP $ case unsnoc lins of
    Nothing -> RWS.tell [line]
    Just (lls, ll) | Text.null line -> RWS.tell $ lls ++ [ll]
    Just (lls, ll) -> RWS.tell $ lls ++ [ll <> " " <> line]

data Context = Context
  { tempcounter :: Natural,
    -- include and pragma directives gathered here.
    headings :: [Text],
    -- functions, datatypes, environments, unions.
    topLevelBlocks :: [Text]
    -- Memoization (actually, I just need it to execute stuff only once)
  }

cModule :: M.Module -> Text
cModule M.Mod {M.toplevelStatements = stmts} = do
  _ <- RWS.runRWS undefined $ do
    undefined
  -- "#pragma clang diagnostic ignored \"-Wtautological-compare\""
  -- "#pragma clang diagnostic ignored \"-Wparentheses-equality\""

  comment' "DATATYPES"
  for_ dataTypes' cDataType

  -- kind of a hack...
  comment' "FUNCTIONS"
  for_ functions cFunction

  comment' "MAIN"
  cMain main

addPragma :: Text -> PP
addPragma = undefined

-- This should be removed - left for reference.
-- extra <- PP RWS.get
-- textEnvs <- carve $ do
--   comment "Envs and Unions"
--   sequenceA_ extra.ordered

type ConInfo = Map UniqueCon DataCon

collectConInfo :: [Annotated DataDef] -> ConInfo
collectConInfo = Map.fromList . map (\(M.Annotated _ dc@(M.DC uc _ _ _)) -> (uc, dc)) . concatMap (\(M.Annotated _ (M.DD _ cons _)) -> cons)

type StdIncludes = Set Text

splitBuiltins :: [Annotated DataDef] -> (StdIncludes, Builtin, [Annotated DataDef])
splitBuiltins = foldr splitCon (mempty, Builtin {typeSubst = mempty, conSubst = mempty}, [])
  where
    splitCon :: Annotated DataDef -> (StdIncludes, Builtin, [Annotated DataDef]) -> (StdIncludes, Builtin, [Annotated DataDef])
    splitCon add@(M.Annotated ddanns dd) (includes, bins, dds) =
      let includes' = addInclude ddanns <> includes
       in case customDatatype add of
            Left bin -> (includes', Builtin {typeSubst = bin.typeSubst <> bins.typeSubst, conSubst = bin.conSubst <> bins.conSubst}, dds)
            Right dd' -> (includes', bins, dd' : dds)

    addInclude :: [Ann] -> StdIncludes
    addInclude = Set.fromList . mapMaybe (\case ACStdInclude std -> Just std; _ -> Nothing)

    customDatatype :: Annotated DataDef -> Either Builtin (Annotated DataDef)
    customDatatype add@(M.Annotated anns (M.DD ut cons _)) = case find (\case ACType _ -> True; _ -> False) anns of
      Just (ACType tname) ->
        let ts = Map.singleton ut tname

            -- here, we know that it's a C type. it should have all constructors defined.
            -- we want to fail here on purpose - makes it easier to debug.
            -- TODO: make it a failure in typechecking if it does not have any ACLits per constructor.
            cs = Map.fromList $ (\(M.Annotated [ACLit conname] (M.DC _ uc _ _)) -> (uc, conname)) <$> cons
         in Left $ Builtin {typeSubst = ts, conSubst = cs}
      _ -> Right add

------ DATATYPEs
-- We can generate 3 types of datatypes:
-- 0. (THIS MIGHT BE REMOVED - probably during monomorphization) A datatype with no constructors. We will disregard it.
-- 1. If none of the constructor has any parameters -> enum
-- 2. If there's only one constructor -> struct
-- 3. Otherwise -> Normal ADT. Consists of a tag field and a union with a struct for each constructor

-- Q: What about Unit-style datatypes: 1 constructor, no parameters.
--  compile it to a single argument enum, as defined. (in C23 and C++, an empty struct is possible. this might be a better choice then.)

-- Also, I've decided for the definitions to be typedefs, because they require less information.

-- cDataType :: M.DataDef -> PP

-- 0. no constructors
cDataType (M.DD _ [] _) = mempty
-- 1. enum
cDataType (M.DD ut dc _)
  | all (\(M.Annotated _ (M.DC _ _ args _)) -> null args) dc =
      pt $ "typedef" § "enum" §> cBlock ((\(M.Annotated _ (M.DC _ uc _ _)) -> pl $ cCon NoArgs uc) <$> dc) <§ cUniqueType ut & ";"
-- 2. struct
cDataType (M.DD ut [dc] _) = do
  -- define the struct
  pt $ "typedef" §> cDataStruct dc <§ cUniqueType ut & ";"

  -- then, define the constructor
  -- TODO: currently broken
  cSingleDataConstructorFunction ut dc

-- 3. ADT
cDataType (M.DD ut dcs _) = do
  let tags = cDataConTag <$> dcs
  pt $
    "typedef"
      § "struct"
      &> cBlock
        [ "enum" §> cBlock [pl $ sepBy ", " tags] <§ "tag;",
          "union" §> cBlock (cDataCon ut <$> dcs) <§ "uni;"
        ]
      <§ cUniqueType ut
      & ";"

  for_ dcs $ cDataConstructorFunction ut

cDataCon :: UniqueType -> Annotated DataCon -> PT
-- I ideally don't want any preprocessor crap (for the source to be easily parsed.) This is temporary, because I want to make the ASTs more expressive soon (which would allow me to generate this at call site.)
cDataCon ut dc@(M.Annotated _ (M.DC _ uc [] _)) = pl $ "#define" § cCon NoArgs uc § enclose "(" ")" (enclose "(" ")" (cUniqueType ut) § "{" § ".tag" § "=" § cDataConTag dc § "}")
cDataCon _ dc@(M.Annotated _ (M.DC _ uc (_ : _) _)) = cDataStruct dc <§ cCon NoArgs uc & ";"

-- used by both of cDataCon and cDataType
cDataStruct :: Annotated DataCon -> PT
cDataStruct (M.Annotated _ (M.DC _ uc ts _)) = "struct" §> cBlock [member t i | (t, i) <- zip ts [1 :: Int ..]] -- cBlock "struct" (fmap cType ts) <+> cCon NoArgs uc <.> ";"
  where
    -- right now, it's impossible to access member variables. just assign next ints for now.
    member t i = statement $ cTypeVar (cDataConArgName uc i) t

-- An optional constructor (will not do the constructor if it the con does not need it.)
cSingleDataConstructorFunction :: UniqueType -> Annotated DataCon -> PP
cSingleDataConstructorFunction _ (M.Annotated _ (M.DC _ _ [] _)) = error "Impossible. This should have been considered an 'enum' type of datatype."
cSingleDataConstructorFunction ut (M.Annotated _ (M.DC _ uc args@(_ : _) _)) =
  let cparamnames = [cDataConArgName uc i | i <- [1 ..]]
      cparams = [cTypeVar name t | (t, name) <- zip args cparamnames]
      assigns = ["." & name § "=" § name | (_, name) <- zip args cparamnames]

      ret = Fix $ M.TCon ut [] -- this is bad (if we have any parameters, this will be incorrect. but it won't matter, per the current implementation of 'cTypeVar')
   in ccFunction
        (cCon WithArgs uc)
        ret
        cparams
        [statement $ "return" § enclose "(" ")" (cUniqueType ut) § "{" § sepBy ", " assigns § "}"]

cDataConstructorFunction :: UniqueType -> Annotated DataCon -> PP
cDataConstructorFunction _ (M.Annotated _ (M.DC _ _ [] _)) = mempty
cDataConstructorFunction ut dc@(M.Annotated _ (M.DC _ uc args@(_ : _) _)) = do
  let cparamnames = [cDataConArgName uc i | i <- [1 ..]]
  let cparams = [cTypeVar name t | (t, name) <- zip args cparamnames]
  let assigns = ["." & name § "=" § name | (_, name) <- zip args cparamnames]

  let ret = Fix $ M.TCon ut [] -- this is bad (if we have any parameters, this will be incorrect. but it won't matter, per the current implementation of 'cTypeVar')
  ccFunction
    (cCon WithArgs uc)
    ret
    cparams
    [statement $ "return" § enclose "(" ")" (cUniqueType ut) § "{" § ".tag" § "=" § cDataConTag dc & ", " § ".uni." & cCon NoArgs uc § "=" § "{" § sepBy ", " assigns § "}" § "}"]

cDataConArgName :: UniqueCon -> Int -> PL
cDataConArgName uc i = "c" & cCon NoArgs uc & "__" & pls i

-- temporary
cDataConTag :: Annotated DataCon -> PL
cDataConTag (M.Annotated _ (M.DC _ uc _ _)) = cCon NoArgs uc & "t"

cFunction :: M.Function -> PP
cFunction (M.Function (M.FD env uv params ret needsImplicitEnvironment) body) = do
  let funref =
        if not needsImplicitEnvironment
          then cVar uv
          else cVarFun uv
  let cparams = params <&> \(uv, t) -> cTypeVar (cVar uv) t
  let envparam = do
        (envtype, _, _) <- cEnv env
        ptrTo envtype § "env"

  let ccparams =
        if not needsImplicitEnvironment
          then cparams
          else envparam : cparams

  ccFunction funref ret ccparams (cStmt <$> body)

cMain :: [M.AnnStmt] -> PP
cMain stmts = pt $ "int" § "main" & "()" §> cBlock (cStmt <$> stmts)

cStmt :: M.AnnStmt -> PT
cStmt = cata $ \(O (Annotated anns monoStmt)) -> case monoStmt of
  Pass -> mempty -- comment "pass (nuttin)"
  Print et ->
    let e = cExpr et
     in case typeFromExpr et of
          Bool ->
            statement $ cPrintf "%s\\n" [cTernary e (cstr "True") (cstr "False")]
          Integer ->
            statement $ cPrintf "%d\\n" [e]
          Unit -> do
            bareExpr e
            statement $ cPrintf "()\\n" []
          CustomType ut ts -> do
            bareExpr e
            statement $ cPrintf (ppType (Fix (M.TCon ut ts)) <> "\\n") []
          Function union args ret ->
            let e' =
                  if isUnionEmpty union
                    then e
                    else e & ".fun"
             in statement $ cPrintf (ppType (Fix (M.TFun union args ret)) <> " at %p\\n") [enclose "(" ")" "void*" § e']
    where
      bareExpr = statement . (enclose "(" ")" "void" §)
  Assignment uv e -> do
    statement $ cTypeVar (cVar uv) (expr2type e) § "=" § cExpr e
  ExprStmt e -> statement $ cExpr e
  Return e ->
    statement $ "return" § cExpr e
  -- EnvHere envdefs ->
  --   for_ envdefs $ \envdef@(M.EnvDef _ union) ->
  --     if isUnionEmpty union
  --       then mempty
  --       else statement $ do
  --         (envtype, name, inst) <- cEnvDef envdef
  --         envtype § name § "=" § inst

  If cond bodyIfTrue elseIfs elseBody -> do
    "if" § enclose "(" ")" (cExpr cond) §> cBlock bodyIfTrue

    for_ elseIfs $ \(elifCond, elifBody) ->
      "else" § "if" § enclose "(" ")" (cExpr elifCond) §> cBlock elifBody

    optional elseBody $ \els ->
      "else" §> cBlock els
  Switch switch (firstCase :| otherCases) -> do
    condName <- statement' $ do
      next <- nextTemp
      cTypeVar next (expr2type switch) § "=" § cExpr switch
      pure next

    "if" § enclose "(" ")" (cDeconCondition condName firstCase.deconstruction) §> do
      let tvars = tvarsFromDecon condName firstCase.deconstruction
      let defs = map (\(uv, t, acc) -> statement $ cTypeVar (cVar uv) t § "=" § acc) tvars

      cBlock $ NonEmpty.prependList defs firstCase.body

    for_ otherCases $ \kase ->
      "else if" § enclose "(" ")" (cDeconCondition condName kase.deconstruction) §> do
        let tvars = tvarsFromDecon condName kase.deconstruction
        let defs = map (\(uv, t, acc) -> statement $ cTypeVar (cVar uv) t § "=" § acc) tvars

        cBlock $ NonEmpty.prependList defs kase.body

    -- this should not be needed. just in case
    "else"
      §> cBlock
        [ statement $ cCall "printf" ["\"Case not matched on line %d.\\n\"", "__LINE__"],
          statement $ cCall "exit" ["1"]
        ]

cDeconCondition :: PL -> M.Decon -> PL
cDeconCondition condVar decon = sepBy " && " $ fmap (\(uc, acc) -> enclose "(" ")" (condVar & acc § "==" § cCon NoArgs uc & "t")) $ flip cata decon $ \case
  -- cCon NoArgs uc & "t" is a quick inlining of cDataConTag...
  CaseVariable _ _ -> []
  CaseConstructor _ uc args ->
    let prefix :: PL
        prefix = ".uni." & cCon NoArgs uc & "."
        dcParams = concatMap (\(pref, as) -> (fmap . fmap) ((prefix & pref) &) as) $ zip (cDataConArgName uc <$> [1 :: Int ..]) args
     in (uc, ".tag") : dcParams

tvarsFromDecon :: PL -> M.Decon -> [(UniqueVar, M.Type, PL)]
tvarsFromDecon conName = (fmap . fmap . fmap) (conName &) $ cata $ \case
  CaseVariable t uv -> [(uv, t, "")]
  CaseConstructor _ uc vars ->
    let prefix :: PL
        prefix = ".uni." & cCon NoArgs uc & "."
        dcParams = concatMap (\(pref, as) -> (fmap . fmap) ((prefix & pref) &) as) $ zip (cDataConArgName uc <$> [1 :: Int ..]) vars
     in dcParams

cExpr :: M.Expr -> PL
cExpr expr = do
  builtin <- PL $ RWS.asks fst
  flip para expr $ \case
    M.TypedExpr t (Call (ft, e) args) ->
      let t'@(Fix (M.TFun union _ _)) = expr2type ft
       in if isUnionEmpty union
            then
              cCall e $ fmap snd args
            else do
              v <- createIntermediateVariable t' e
              cCall (v & ".fun") $ ("&" & v & ".uni") : fmap snd args

    -- TEMP: this is only defined to be okay per C23 standard (unions zero initialized)
    -- To be C99 compatible, I would have to declare it first, then memset it, then use it.
    M.TypedExpr _ (Op (Fix (M.TypedExpr t _), e) Equals (Fix (M.TypedExpr t' _), e')) | not (isBuiltinType t builtin) -> do
      el <- createIntermediateVariable t e
      er <- createIntermediateVariable t' e'
      enclose "(" ")" $ "0 == " § cCall "memcmp" [ref el, ref er, sizeOf t]
    M.TypedExpr _ (Op (Fix (M.TypedExpr t _), e) NotEquals (Fix (M.TypedExpr t' _), e')) | not (isBuiltinType t builtin) -> do
      el <- createIntermediateVariable t e
      er <- createIntermediateVariable t' e'
      enclose "(" ")" $ "0 != " § cCall "memcmp" [ref el, ref er, sizeOf t]
    M.TypedExpr t expr -> case fmap snd expr of
      Call {} -> error "unreachable"
      Lit (M.LInt x) -> pls x
      Var loc uv -> cVarVal loc uv
      Con uc -> case t of
        Fix (M.TFun {}) -> cCon WithArgs uc
        Fix (M.TCon {}) -> cCon NoArgs uc
      -- Op l Equals r | isBuiltinType undefined builtin -> undefined
      Op l op r -> enclose "(" ")" $ l § cOp op § r

-- EnvInit envdef@(M.EnvDef (M.FD _ v _ _) union) -> if isUnionEmpty union
--   then cVar v
--   else do
--     (_, _, inst) <- cEnvDef envdef
--     inst

sizeOf :: M.Type -> PL
sizeOf t = cCall "sizeof" [cType t]

ref :: PL -> PL
ref = ("&" &)

cCall :: PL -> [PL] -> PL
cCall callee args = callee & cParamList args

cParamList :: [PL] -> PL
cParamList = enclose "(" ")" . sepBy ", "

createIntermediateVariable :: M.Type -> PL -> PPL PL
createIntermediateVariable t e = do
  next <- nextTemp
  let assignment = statement $ cTypeVar next t § "=" § e

  PL $ RWS.modify $ second (assignment :)
  pure next

nextTemp :: PPL PL
nextTemp = do
  extra <- PL $ RWS.gets (\(ex, _, _) -> ex)
  PL $ RWS.modify $ \(extra, tls, ls) -> (extra {tempcounter = extra.tempcounter + 1}, tls, ls)

  let nextID = fromString $ "temp" <> show extra.tempcounter
  pure nextID

cTernary :: PL -> PL -> PL -> PL
cTernary cond ifTrue ifFalse = cond § "?" § ifTrue § ":" § ifFalse

cPrintf :: Text -> [PL] -> PL
cPrintf formatString args =
  let cformat = cstr formatString
   in cCall "printf" (cformat : args)

cBlock :: (Traversable t) => t PT -> PT
cBlock stmts = do
  "{"
  indent $ sequenceA_ stmts
  "}"

cVarVal :: Locality -> UniqueVar -> PL
cVarVal Local uv = cVar uv
cVarVal FromEnvironment uv = "env->" & cVar uv

cVar :: UniqueVar -> PL
cVar v = plt (sanitize v.varName.fromVN) & "__" & pls (hashUnique v.varID)

sanitize :: Text -> Text
sanitize = Text.concatMap $ \case
  '-' -> "_dash_"
  '_' -> "__"
  o -> fromString [o]

-- used when the function has an environment.
--  then this environment uses cVar and the function uses cVarFun
--  if the function has an empty environment, use cVar for the function
cVarFun :: UniqueVar -> PL
cVarFun v = plt v.varName.fromVN & "__" & pls (hashUnique v.varID) & "f"

data ConType
  = WithArgs
  | NoArgs

-- supposed to be the definitie source for unique names.
cCon :: ConType -> UniqueCon -> PL
-- enum type constructor (refer to actual datatype)
cCon NoArgs c = do
  cs <- PL $ RWS.asks $ conSubst . fst
  case cs !? c of
    Just t -> plt t
    Nothing -> plt c.conName.fromCN & "__" & pls (hashUnique c.conID)
-- type constructor with arguments - treat is as a function
cCon WithArgs c = plt c.conName.fromCN & "__" & pls (hashUnique c.conID) & "f"

cOp :: Op -> PL
cOp = \case
  Plus -> "+"
  Minus -> "-"
  Times -> "*"
  Divide -> "/"
  Equals -> "=="
  NotEquals -> "!="

-- Because of function types, we have to print types in a *very* special way.
cTypeVar :: PL -> M.Type -> PL
cTypeVar v (Fix (M.TCon ut _)) = cUniqueType ut § v
cTypeVar v (Fix (M.TFun union args ret)) | not (isUnionEmpty union) = do
  cUnion args ret union § v
cTypeVar v (Fix (M.TFun _ args ret)) =
  let cargs = cType <$> args
   in cTypeFun ret cargs v

-- Function printing logic (i had to use it in two places and I *really* don't want to duplicate this behavior.)
cTypeFun :: M.Type -> [PL] -> PL -> PL
cTypeFun ret cargs v = cTypeVar (cCall (enclose "(*" ")" v) cargs) ret

cType :: M.Type -> PL
cType (Fix (M.TCon ut _)) = cUniqueType ut
cType (Fix (M.TFun union args ret)) =
  let cargs =
        if isUnionEmpty union
          then cType <$> args
          else ptrTo (cUnion args ret union) : (cType <$> args)
   in cTypeVar (cCall "(*)" cargs) ret

-- The definite source for UniqueType naming
cUniqueType :: UniqueType -> PL
cUniqueType t = do
  ts <- PL $ RWS.asks $ typeSubst . fst
  case ts !? t of
    Just tname -> plt tname
    Nothing -> cUniqueTypeName t

isBuiltinType :: M.Type -> Builtin -> Bool
isBuiltinType (Fix (M.TFun _ _ _)) _ = False
isBuiltinType (Fix (M.TCon t _)) ts = isJust $ ts.typeSubst !? t

cUniqueTypeName :: UniqueType -> PL
cUniqueTypeName t = plt t.typeName.fromTC & "__" & pls (hashUnique t.typeID)

-- When creating an environment. (EnvInit and EnvHere)
-- Right now there are two possibilities for a function.
--  1. No environment
--  2. One of the functions in the union has an environment.
-- cEnvDef :: M.EnvDef -> PPL (PL, PL, PL)  -- (Type, Name, Inst)
-- cEnvDef (M.EnvDef fundec@(M.FD env v args ret) union) = do
--   let unionType = cUnion (snd <$> args) ret union
--   (_, envName, envinst) <- cEnv env

--   -- kind of spaghetti-ish. depending on the union, the function is defined to have an extra argument or not.
--   --   TODO: i copied it. it's also in the function definition... bad.
--   let funref = if isUnionEmpty union
--         then cVar v
--         else cVarFun v

--   -- TODO: shit. another code copy shit
--   let cargs = bool id ("void*" :) (not $ isUnionEmpty union) $ cType . snd <$> args
--   let funinst = ".fun" § "=" § enclose "(" ")" (cTypeVar (cCall "(*)" cargs) ret) § funref

--   -- how is environment instantiated
--   let unionenvinst = ".uni." & envName § "=" § envinst
--   let inst = enclose "(" ")" unionType § "{" § funinst & "," § unionenvinst § "}"

--   pure (unionType, cVar v, inst)

-- It just creates a union if it does not exist and returns the types.
--  no matter what the code is supposed to do, this is how you should obtain union name and type.
--   TODO: don't generate the union if it's empty (or should the check happen outside of the function?)
cUnion :: [M.Type] -> M.Type -> M.EnvUnion -> PL -- (Type, Fun Ass -> Env Ass -> Inst)
cUnion args ret union@(M.EnvUnion uid envs) = do
  envTypes <- for envs $ \env -> do
    -- this adds all environments to our scope (the one that matters :3)
    --   TODO: this is super iffy. I guess my structure aint very good.
    (envType, envName, _) <- cEnv env

    pure $ statement $ envType § envName

  let fun = statement $ do
        let cargs = bool id ("void*" :) (not $ isUnionEmpty union) $ cType <$> args
        cTypeFun ret cargs "fun"

  let union = "union" §> cBlock envTypes <§ "uni;"
  let whole = do
        extra <- getContext
        unless (uid `Set.member` extra.definedUnions) $ do
          modifyContext $ \extra -> extra {definedUnions = Set.insert uid extra.definedUnions}
          pt $ cUnionType uid §> cBlock [fun, union] <& ";"

  addTopLevel whole

  cUnionType uid

cEnv :: M.Env -> PPL (PL, PL, PL) -- (Type, Name, Inst)
cEnv (M.Env eid vars) = do
  let varTypes =
        vars <&> \(v, loc, t) -> do
          statement $ do
            cTypeVar (cVar v) t
  let env = do
        extra <- getContext
        unless (eid `Set.member` extra.definedEnvs) $ do
          modifyContext $ \extra -> extra {definedEnvs = Set.insert eid extra.definedEnvs}
          pt $ cEnvType eid §> cBlock varTypes <& ";"

  addTopLevel env

  let cvars = vars <&> \(v, loc, _) -> "." & cVar v § "=" § cVarVal loc v
  let inst = "{" § sepBy ", " cvars § "}"

  pure (cEnvType eid, cEnvName eid, inst)

cEnvName :: EnvID -> PL
cEnvName env = "e" & pls (hashUnique env.fromEnvID)

cEnvType :: EnvID -> PL
cEnvType env = "struct" § "et" & pls (hashUnique env.fromEnvID)

cUnionName :: UnionID -> PL
cUnionName u = "u" & pls (hashUnique u.fromUnionID)

-- Don't use this, because union will not be generated. Use `cUnion` for union type.
cUnionType :: UnionID -> PL
cUnionType u =
  "struct" § "ut" & pls (hashUnique u.fromUnionID)

ccFunction :: (Traversable t) => PL -> M.Type -> [PL] -> t PT -> PP
ccFunction name t args body = pt $ "static" § cTypeVar (name & enclose "(" ")" (sepBy ", " args)) t §> cBlock body

ptrTo :: PL -> PL
ptrTo = (<> "*")

-- statement :: PL -> PP
-- statement pp = RWS.mapRWS (\(r, extra, tokens) ->
--     let joined = Text.unwords tokens <> ";"
--         stmts = reverse $ joined : extra.statementsOverExpressions  -- we add statements with cons (:), so we have to reverse it now
--     in (r, extra { statementsOverExpressions = [] }, stmts)
--     ) w

enclose :: PL -> PL -> PL -> PL
enclose l r x = l & x & r

sepBy :: PL -> [PL] -> PL
sepBy _ [] = mempty
sepBy sep (x : xs) = foldl' (\l r -> l & sep & r) x xs

indent :: PT -> PT
indent (PT x) = PT $ RWS.censor (fmap ("  " <>)) x

optional :: Maybe a -> (a -> PT) -> PT
optional Nothing _ = mempty
optional (Just x) f = f x

comment' :: Text -> PP
comment' = pt . comment

comment :: Text -> PT
comment text = ptt $ "// " <> text

cInclude :: Text -> PP
cInclude t = ppt $ "#include <" <> t <> ">"

cstr :: Text -> PL
cstr text = plt $ "\"" <> text <> "\""

pls :: (Show s) => s -> PL
pls = fromString . show

plt :: Text -> PL
plt = fromString . Text.unpack

ptt :: Text -> PT
ptt = fromString . Text.unpack

ppt :: Text -> PP
ppt = fromString . Text.unpack

pp :: (Builtin, ConInfo) -> PP -> Text
pp b p =
  let extra =
        Context
          { tempcounter = 0,
            definedUnions = mempty,
            definedEnvs = mempty
          }
      (_, _, text) = RWS.runRWS p.fromPP b extra
   in Text.unlines text

instance (a ~ ()) => IsString (PPG a) where
  fromString s = PP $ RWS.rws $ \_ e -> ((), e, [Text.pack s])

instance (a ~ ()) => IsString (PPTL a) where
  fromString s = PT $ RWS.rws $ \_ e -> ((), e, [Text.pack s])

instance (a ~ ()) => IsString (PPL a) where
  fromString s = PL $ RWS.rws $ \_ e -> ((), e, [Text.pack s])

------- MISC -------

modifyContext :: (Context -> Context) -> PP
modifyContext fmod = PP $ RWS.modify fmod

-- \$ \(extra, tls, ls) -> (fmod extra, tls, ls)

getContext :: PPG Context
getContext = PP $ RWS.get

addTopLevel :: PP -> PL
addTopLevel thing = do
  PL $ RWS.modify $ \(extra, topLevelBlocks, lines) -> (extra, thing : topLevelBlocks, lines)

carve :: RWS r [Text] s () -> RWS r [Text] s [Text]
carve p =
  RWS.censor (const []) $ snd <$> RWS.listen p

carveg :: PP -> PPG [Text]
carveg = PP . carve . fromPP

carvel :: PL -> PPL [Text]
carvel p =
  PL $ RWS.censor (const []) $ snd <$> RWS.listen p.fromPL

-- expr2type :: M.Expr -> M.Type
-- expr2type (Fix (M.TypedExpr t _)) = t

-- isUnionEmpty :: M.EnvUnion -> Bool
-- isUnionEmpty (M.EnvUnion _ envs) = all null envs

-- typeFromExpr :: M.Expr -> SpecialTypeForPrinting
-- typeFromExpr (Fix (M.TypedExpr t _)) = do
--   case project t of
--     M.TFun union ts ret -> Function union ts ret

--     -- Brittle, but it's temporary anyway.
--     M.TCon ut ts
--       | ut.typeName == boolTypeName -> Bool
--       | ut.typeName == intTypeName -> Integer
--       | ut.typeName == TC "Unit" -> Unit
--       | otherwise -> CustomType ut ts

-- -- In the future, when I have better codegen, this should not be required.
-- data SpecialTypeForPrinting
--   = Integer
--   | Bool
--   | Unit
--   | Function M.EnvUnion [M.Type] (M.Type)
--   | CustomType UniqueType [M.Type]

-- ppType :: M.Type -> Text
-- ppType (Fix (M.TFun _ [arg] ret)) = "" <> ppType arg <> " -> " <> ppType ret
-- ppType (Fix (M.TFun _ args ret)) = "(" <> Text.intercalate ", " (ppType <$> args) <> ") -> " <> ppType ret
-- ppType (Fix (M.TCon ut ts)) = ut.typeName.fromTC <> mconcat ((" " <>) . ppType' <$> ts)
--   where
--     ppType' :: M.Type -> Text
--     ppType' (Fix typ) = case typ of
--       M.TFun _ [arg] ret -> "(" <> ppType' arg <> " -> " <> ppType ret <> ")"
--       M.TFun _ args ret -> "((" <> Text.unwords (ppType <$> args) <> ") -> "  <> ppType ret <> ")"
--       M.TCon tut [] -> tut.typeName.fromTC
--       M.TCon tut tts -> "(" <> tut.typeName.fromTC <> " " <> Text.unwords (ppType' <$> tts) <> ")"

--------- polyfills ---------

unsnoc :: [a] -> Maybe ([a], a)
-- The lazy pattern ~(a, b) is important to be productive on infinite lists
-- and not to be prone to stack overflows.
-- Expressing the recursion via 'foldr' provides for list fusion.
unsnoc = foldr (\x -> Just . maybe ([], x) (\(~(a, b)) -> (x : a, b))) Nothing
{-# INLINEABLE unsnoc #-}
