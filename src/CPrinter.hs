{-# LANGUAGE OverloadedStrings, OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CPrinter (cModule) where

import qualified AST.Mono as M
import AST.Mono (Mono, DataDef, FunDec, Function, AnnotatedStmt (..), StmtF (..), ExprF (..), DataCon)
import AST.Common (Module, Annotated, AnnStmt, Expr, Type, EnvUnion, UniqueType (..), TCon (..), UniqueVar, Env, Locality (..), UniqueCon, Op (..), EnvID, UnionID, Ann (..))

import Control.Monad.Trans.Writer (Writer)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Foldable (for_, foldl', sequenceA_, traverse_)
import Data.List.NonEmpty (NonEmpty)
import Data.String (IsString (..))
import Data.Functor.Foldable (cata, histo, para, project)
import Data.Fix (Fix(..))
import AST.Converged (Prelude, boolTypeName, intTypeName, unitName)
import Control.Monad.Trans.RWS (RWS)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Traversable (for)
import qualified AST.Common as M
import Control.Monad.Trans.RWS.CPS (RWST)
import GHC.Num (Natural)
import Data.Unique (hashUnique)
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad (when, unless)
import Data.Bool (bool)
-- import Data.List (unsnoc)
import Data.Maybe (fromMaybe, mapMaybe, isJust)
import Data.Biapplicative (second, first)
import Data.Map (Map, (!?))
import Data.List (find)
import qualified Data.Map as Map
import Debug.Trace (traceShowId, traceShow, traceShowWith)



-- todo: some function order cleanup after it works

-- Global PP state.
newtype PPG a = PP { fromPP :: RWS Builtin [Text] Extra a } deriving (Functor, Applicative, Monad)
type PP = PPG ()

instance (a ~ ()) => Semigroup (PPG a) where
  PP l <> PP r = PP $ l >> r

instance (a ~ ()) => Monoid (PPG a) where
  mempty = PP $ RWS.rws $ \_ s -> (mempty, s, [])


-- Top level PP state (every function/enum/struct/etc.)
newtype PPTL a = PT { fromPPTL :: RWS Builtin [Text] (Extra, [TopLevelBlock]) a } deriving (Functor, Applicative, Monad)
type PT = PPTL ()
type TopLevelBlock = PP

instance (a ~ ()) => Semigroup (PPTL a) where
  PT l <> PT r = PT $ l >> r

instance (a ~ ()) => Monoid (PPTL a) where
  mempty = PT $ RWS.rws $ \_ s -> (mempty, s, [])


-- Line (Expression) PP state.
newtype PPL a = PL { fromPL :: RWS Builtin [Text] (Extra, [TopLevelBlock], [AdditionalLine]) a } deriving (Functor, Applicative, Monad)
type PL = PPL ()
type AdditionalLine = PT

instance (a ~ ()) => Semigroup (PPL a) where
  PL l <> PL r = PL $ l >> r

instance (a ~ ()) => Monoid (PPL a) where
  mempty = PL $ RWS.rws $ \_ s -> (mempty, s, [])


---- maybe i should add a third type for resolving environments and unions (but again this should probably be done in the monomorphizer)


-- Basic operators + transitions
pt :: PPTL a -> PPG a
pt (PT p) = do
  r <- PP RWS.ask
  extra <- PP RWS.get

  let (x, (extra', topLevelBlocks), tokens) = RWS.runRWS p r (extra, [])
  let block = Text.unlines tokens
  PP $ RWS.put extra'

  sequenceA_ $ reverse topLevelBlocks
  PP $ RWS.tell [block]

  pure x


pl :: PPL a -> PPTL a
pl (PL p) = do -- RWS.mapRWS (\(a, _, t) -> (a, extra, [Text.concat t])) p.fromPL
  r <- PT RWS.ask
  (extra, tls) <- PT RWS.get

  let (x, (extra', topLevelBlocks, lines), tokens) = RWS.runRWS p r (extra, tls, [])
  let line = Text.concat tokens
  PT $ RWS.put (extra', topLevelBlocks)

  sequenceA_ $ reverse lines
  PT $ RWS.tell [line]

  pure x

statement :: PL -> PT
statement p = pl $ p & ";"


infixr 7 &
(&) :: PL -> PL -> PL
(&) = (<>)

infixr 6 §  -- hihi
(§) :: PL -> PL -> PL
(§) p1 p2 = p1 & " " & p2

-- join with next line
infixr 5 &>
(&>) :: PL -> PT -> PT
(&>) l r = do
  line <- pl $ Text.concat <$> carvel l
  lins <- carvet r
  PT $ case lins of
    [] -> RWS.tell [line]
    (li:lis) -> RWS.tell $ (line <> li) : lis

infixl 5 §>
(§>) :: PL -> PT -> PT
(§>) l r = do
  line <- pl $ Text.concat <$> carvel l
  lins <- carvet r
  PT $ case lins of
    [] -> RWS.tell [line]
    (li:lis) | Text.null line -> RWS.tell $ li : lis
    (li:lis) -> RWS.tell $ (line <> " " <> li) : lis

infixr 4 <&
(<&) :: PT -> PL -> PT
(<&) l r = do
  lins <- carvet l
  line <- pl $ Text.concat <$> carvel r
  PT $ case unsnoc lins of
    Nothing -> RWS.tell [line]
    Just (lls, ll) | Text.null line -> RWS.tell $ lls ++ [ll]
    Just (lls, ll) -> RWS.tell $ lls ++ [ll <> line]

infixr 4 <§
(<§) :: PT -> PL -> PT
(<§) l r = do
  lins <- carvet l
  line <- pl $ Text.concat <$> carvel r
  PT $ case unsnoc lins of
    Nothing -> RWS.tell [line]
    Just (lls, ll) | Text.null line -> RWS.tell $ lls ++ [ll]
    Just (lls, ll) -> RWS.tell $ lls ++ [ll <> " " <> line]


data Extra = Extra
  { tempcounter :: Natural

  -- Envs and Unions can be amywhere, so we have to keep track of what was generated.
  --  is this good? probably not. but I just want to get this C printer working.
  --   ??? if an environment refers to another environment, we would ideally like to have it sorted out.
  , definedUnions :: Set UnionID
  -- , ordered :: [PP]  -- this is more so, that I can have Envs and Unions in one place.
  , definedEnvs :: Set EnvID

  -- functions that should be defined once
  -- , equalityFunctions :: [PP]
  }

data Builtin = Builtin
  { typeSubst :: Map UniqueType Text
  , conSubst :: Map UniqueCon Text
  }


cModule :: Module Mono -> Text
cModule M.Mod{ M.functions = functions, M.dataTypes = dataTypes, M.main = main } =
  -- TODO: this should be checked beforehand to give an error during/after typechecking. (also Parse, not Validate)
  let (includes, builtin, dataTypes') = splitBuiltins dataTypes
  in pp builtin $ do

  comment' "includes"
  for_ includes $ \include ->
    ppt $ "#include<" <> include <> ">"

  -- Right now, it always gets included. It shouldn't be like this.
  ppt "#include<string.h>"


  "#pragma clang diagnostic ignored \"-Wtautological-compare\""
  "#pragma clang diagnostic ignored \"-Wparentheses-equality\""

  comment' "DATATYPES"
  for_ dataTypes' cDataType

  -- kind of a hack...
  comment' "FUNCTIONS"
  for_ functions cFunction

  comment' "MAIN"
  cMain main

  -- This should be removed - left for reference.
  -- extra <- PP RWS.get
  -- textEnvs <- carve $ do
  --   comment "Envs and Unions"
  --   sequenceA_ extra.ordered


type StdIncludes = Set Text
splitBuiltins :: [Annotated DataDef] -> (StdIncludes, Builtin, [Annotated DataDef])
splitBuiltins = foldr splitCon (Set.singleton "stdio.h", Builtin { typeSubst = mempty, conSubst = mempty }, [])
  where
    splitCon :: Annotated DataDef -> (StdIncludes, Builtin, [Annotated DataDef]) -> (StdIncludes, Builtin, [Annotated DataDef])
    splitCon add@(M.Annotated ddanns dd) (includes, bins, dds) =
      let includes' = addInclude ddanns <> includes
      in case customDatatype add of
        Left bin -> (includes', Builtin { typeSubst = bin.typeSubst <> bins.typeSubst, conSubst = bin.conSubst <> bins.conSubst  }, dds)
        Right dd' -> (includes', bins, dd' : dds)


    addInclude :: [Ann] -> StdIncludes
    addInclude = Set.fromList . mapMaybe (\case { ACStdInclude std -> Just std; _ -> Nothing })

    customDatatype :: Annotated DataDef -> Either Builtin (Annotated DataDef)
    customDatatype add@(M.Annotated anns (M.DD ut cons)) = case find (\case { ACType _ -> True; _ -> False }) anns of
      Just (ACType tname) ->
        let ts = Map.singleton ut tname

            -- here, we know that it's a C type. it should have all constructors defined.
            -- we want to fail here on purpose - makes it easier to debug.
            -- TODO: make it a failure in typechecking if it does not have any ACLits per constructor.
            cs = Map.fromList $ (\(M.Annotated [ACLit conname] (M.DC uc _)) -> (uc, conname)) <$> cons
        in Left $ Builtin { typeSubst = ts, conSubst = cs }

      _ -> Right add



-------- DATATYPEs
-- We can generate 3 types of datatypes:
--  0. (THIS MIGHT BE REMOVED - probably during monomorphization) A datatype with no constructors. We will disregard it.
--  1. If none of the constructor has any parameters -> enum
--  2. If there's only one constructor -> struct
--  3. Otherwise -> Normal ADT. Consists of a tag field and a union with a struct for each constructor

-- Q: What about Unit-style datatypes: 1 constructor, no parameters.
--   compile it to a single argument enum, as defined. (in C23 and C++, an empty struct is possible. this might be a better choice then.)

-- Also, I've decided for the definitions to be typedefs, because they require less information.

cDataType :: Annotated DataDef -> PP

-- 0. no constructors
cDataType (M.Annotated _ (M.DD _ [])) = mempty

-- 1. enum
cDataType (M.Annotated _ (M.DD ut dc)) | all (\(M.Annotated _ (M.DC _ args)) -> null args) dc  =
  pt $ "typedef" § "enum" §> cBlock ((\(M.Annotated _ (M.DC uc _)) -> pl $ cCon NoArgs uc) <$> dc) <§ cUniqueType ut & ";"

-- 2. struct
cDataType (M.Annotated _ (M.DD ut [dc])) = do
  -- define the struct
  pt $ "typedef" §> cDataStruct dc <§ cUniqueType ut & ";"

  -- then, define the constructor
  -- TODO: currently broken
  cSingleDataConstructorFunction ut dc



-- 3. ADT
cDataType (M.Annotated _ (M.DD ut dcs)) = do
  let tags = cDataConTag <$> dcs
  pt $ "typedef" § "struct" &> cBlock
    [ "enum" §> cBlock [ pl $ sepBy ", " tags ]  <§ "tag;"
    , "union" §> cBlock (cDataCon ut <$> dcs) <§ "uni;"
    ] <§ cUniqueType ut & ";"

  for_ dcs $ cDataConstructorFunction ut

cDataCon :: UniqueType -> Annotated DataCon -> PT
-- I ideally don't want any preprocessor crap (for the source to be easily parsed.) This is temporary, because I want to make the ASTs more expressive soon (which would allow me to generate this at call site.)
cDataCon ut dc@(M.Annotated _ (M.DC uc [])) = pl $ "#define" § cCon NoArgs uc § enclose "(" ")" (enclose "(" ")" (cUniqueType ut) § "{" § ".tag" § "=" § cDataConTag dc § "}")
cDataCon _ dc@(M.Annotated _ (M.DC uc (_:_))) = cDataStruct dc <§ cCon NoArgs uc & ";"

-- used by both of cDataCon and cDataType
cDataStruct :: Annotated DataCon -> PT
cDataStruct (M.Annotated _ (M.DC uc ts)) = "struct" §> cBlock [ member t i | (t, i) <- zip ts [1::Int ..] ]  -- cBlock "struct" (fmap cType ts) <+> cCon NoArgs uc <.> ";"
  where
    -- right now, it's impossible to access member variables. just assign next ints for now.
    member t i = statement $ cTypeVar (cDataConArgName uc i) t

-- An optional constructor (will not do the constructor if it the con does not need it.)
cSingleDataConstructorFunction :: UniqueType -> Annotated DataCon -> PP
cSingleDataConstructorFunction _ (M.Annotated _ (M.DC _ [])) = error "Impossible. This should have been considered an 'enum' type of datatype."
cSingleDataConstructorFunction ut (M.Annotated _ (M.DC uc args@(_:_))) =
  let
    cparamnames = [ cDataConArgName uc i | i <- [1..] ]
    cparams = [ cTypeVar name t | (t, name) <- zip args cparamnames ]
    assigns     = [ "." & name § "=" § name  |  (_, name) <- zip args cparamnames ]

    ret = Fix $ M.TCon ut []  -- this is bad (if we have any parameters, this will be incorrect. but it won't matter, per the current implementation of 'cTypeVar')

  in ccFunction (cCon WithArgs uc) ret cparams
    [ statement $ "return" § enclose "(" ")" (cUniqueType ut) § "{" § sepBy ", "  assigns § "}" ]

cDataConstructorFunction :: UniqueType -> Annotated DataCon -> PP
cDataConstructorFunction _ (M.Annotated _ (M.DC _ [])) = mempty
cDataConstructorFunction ut dc@(M.Annotated _ (M.DC uc args@(_:_))) = do
  let cparamnames = [ cDataConArgName uc i | i <- [1..] ]
  let cparams = [ cTypeVar name t | (t, name) <- zip args cparamnames ]
  let assigns     = [ "." & name § "=" § name  |  (_, name) <- zip args cparamnames ]

  let ret = Fix $ M.TCon ut []  -- this is bad (if we have any parameters, this will be incorrect. but it won't matter, per the current implementation of 'cTypeVar')
  ccFunction (cCon WithArgs uc) ret cparams
    [ statement $ "return" § enclose "(" ")" (cUniqueType ut) § "{" § ".tag" § "=" § cDataConTag dc & ", " § ".uni." & cCon NoArgs uc § "=" § "{" § sepBy ", " assigns § "}" § "}" ]

cDataConArgName :: UniqueCon -> Int -> PL
cDataConArgName uc i = "c" & cCon NoArgs uc & "__" & pls i

-- temporary
cDataConTag :: Annotated DataCon -> PL
cDataConTag (M.Annotated _ (M.DC uc _)) = cCon NoArgs uc & "t"


cFunction :: Annotated (Function (AnnStmt Mono)) -> PP
cFunction (M.Annotated _ (M.Fun (M.FD env uv params ret) union body)) = do
  let funref = if isUnionEmpty union
        then cVar uv
        else cVarFun uv
  let cparams = params <&> \(uv, t) -> cTypeVar (cVar uv) t
  let envparam = do
        (envtype, _, _) <- cEnv env
        ptrTo envtype § "env"

  let ccparams = if isUnionEmpty union
      then cparams
      else envparam : cparams

  ccFunction funref ret ccparams (cStmt <$> body)

cMain :: [AnnStmt Mono] -> PP
cMain stmts = pt $ "int" § "main" & "()" &> cBlock (cStmt <$> stmts)


cStmt :: AnnStmt Mono -> PT
cStmt = cata $ \(AnnStmt anns monoStmt) -> case monoStmt of
  Pass -> comment "pass (nuttin)"
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
          let e' = if isUnionEmpty union
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

  EnvHere envdefs ->
    for_ envdefs $ \envdef@(M.EnvDef _ union) ->
      if isUnionEmpty union
        then mempty
        else statement $ do
          (envtype, name, inst) <- cEnvDef envdef
          envtype § name § "=" § inst

  If cond bodyIfTrue elseIfs elseBody -> do
    "if" § enclose "(" ")" (cExpr cond) §> cBlock bodyIfTrue

    for_ elseIfs $ \(elifCond, elifBody) ->
      "else" § "if" § enclose "(" ")" (cExpr elifCond) §> cBlock elifBody

    optional elseBody $ \els ->
      "else" §> cBlock els

  MutDefinition {} -> undefined
  MutAssignment {} -> undefined


cExpr :: Expr Mono -> PL
cExpr expr = do
  builtin <- PL RWS.ask
  flip para expr $ \case
    M.ExprType t (Call (ft, e) args) ->
        let t'@(Fix (M.TFun union _ _)) = expr2type ft
        in if isUnionEmpty union
          then
            cCall e $ fmap snd args
          else do
            v <- createIntermediateVariable t' e
            cCall (v & ".fun") $ ("&" & v & ".uni") : fmap snd args

    M.ExprType _ (Op (Fix (M.ExprType t _), e) Equals (Fix (M.ExprType t' _), e')) | not (isBuiltinType t builtin) -> do
      el <- createIntermediateVariable t e
      er <- createIntermediateVariable t' e'
      enclose "(" ")" $ "0 == " § cCall "memcmp" [ref el, ref er, sizeOf t]
    M.ExprType _ (Op (Fix (M.ExprType t _), e) NotEquals (Fix (M.ExprType t' _), e')) | not (isBuiltinType t builtin) -> do
      el <- createIntermediateVariable t e
      er <- createIntermediateVariable t' e'
      enclose "(" ")" $ "0 != " § cCall "memcmp" [ref el, ref er, sizeOf t]

    M.ExprType t expr -> case fmap snd expr of
      Call {} -> error "unreachable"

      Lit (M.LInt x) -> pls x

      Var Local uv -> cVar uv
      Var FromEnvironment uv -> "env->" & cVar uv
      Var External _ -> undefined

      Con uc -> case t of
        Fix (M.TFun {}) -> cCon WithArgs uc
        Fix (M.TCon {}) -> cCon NoArgs uc

      -- Op l Equals r | isBuiltinType undefined builtin -> undefined
      Op l op r -> enclose "(" ")" $ l § cOp op § r

      EnvInit envdef@(M.EnvDef (M.FD _ v _ _) union) -> if isUnionEmpty union
        then cVar v
        else do
          (_, _, inst) <- cEnvDef envdef
          inst


sizeOf :: Type Mono -> PL
sizeOf t = cCall "sizeof" [cType t]

ref :: PL -> PL
ref = ("&" &)

cCall :: PL -> [PL] -> PL
cCall callee args = callee & cParamList args

cParamList :: [PL] -> PL
cParamList = enclose "(" ")" . sepBy ", "

createIntermediateVariable :: Type Mono -> PL -> PPL PL
createIntermediateVariable t e = do
  next <- nextTemp
  let assignment = statement $ cTypeVar next t § "=" § e

  PL $ RWS.modify $ second (assignment :)
  pure next

nextTemp :: PPL PL
nextTemp = do
  extra <- PL $ RWS.gets (\(ex, _, _) -> ex)
  PL $ RWS.modify $ \(extra, tls, ls) -> (extra { tempcounter = extra.tempcounter + 1 }, tls, ls)

  let nextID = fromString $ "temp" <> show extra.tempcounter
  pure nextID

cTernary :: PL -> PL -> PL -> PL
cTernary cond ifTrue ifFalse = cond § "?" § ifTrue § ":" § ifFalse

cPrintf :: Text -> [PL] -> PL
cPrintf formatString args =
  let cformat = cstr formatString
  in cCall "printf" (cformat : args)

cBlock :: Traversable t => t PT -> PT
cBlock stmts = do
  "{"
  indent $ sequenceA_ stmts
  "}"

cVar :: UniqueVar -> PL
cVar v = plt v.varName.fromVN & "__" & pls (hashUnique v.varID)

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
  cs <- PL $ RWS.asks conSubst
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
cTypeVar :: PL -> Type Mono -> PL
cTypeVar v (Fix (M.TCon ut _)) = cUniqueType ut § v

cTypeVar v (Fix (M.TFun union args ret)) | not (isUnionEmpty union) = do
  cUnion args ret union § v

cTypeVar v (Fix (M.TFun _ args ret)) =
  let cargs = cType <$> args
  in cTypeFun ret cargs v

-- Function printing logic (i had to use it in two places and I *really* don't want to duplicate this behavior.)
cTypeFun :: Type Mono -> [PL] -> PL -> PL
cTypeFun ret cargs v = cTypeVar (cCall (enclose "(*" ")" v) cargs) ret

cType :: Type Mono -> PL
cType (Fix (M.TCon ut _)) = cUniqueType ut
cType (Fix (M.TFun union args ret)) =
  let cargs = if isUnionEmpty union
      then cType <$> args
      else ptrTo (cUnion args ret union) : (cType <$> args)
  in cTypeVar (cCall "(*)" cargs) ret


-- The definite source for UniqueType naming
cUniqueType :: UniqueType -> PL
cUniqueType t = do
  ts <- PL $ RWS.asks typeSubst
  case ts !? t of
    Just tname -> plt tname
    Nothing -> cUniqueTypeName t

isBuiltinType :: Type Mono -> Builtin -> Bool
isBuiltinType (Fix (M.TFun _ _ _)) _ = False
isBuiltinType (Fix (M.TCon t _)) ts = isJust $ ts.typeSubst !? t


cUniqueTypeName :: UniqueType -> PL
cUniqueTypeName t = plt t.typeName.fromTC & "__" & pls (hashUnique t.typeID)


-- When creating an environment. (EnvInit and EnvHere)
-- Right now there are two possibilities for a function.
--  1. No environment
--  2. One of the functions in the union has an environment.
cEnvDef :: M.EnvDef -> PPL (PL, PL, PL)  -- (Type, Name, Inst)
cEnvDef (M.EnvDef fundec@(M.FD env v args ret) union) = do
  let unionType = cUnion (snd <$> args) ret union
  (_, envName, envinst) <- cEnv env

  -- kind of spaghetti-ish. depending on the union, the function is defined to have an extra argument or not.
  --   TODO: i copied it. it's also in the function definition... bad.
  let funref = if isUnionEmpty union
        then cVar v
        else cVarFun v

  -- TODO: shit. another code copy shit
  let cargs = bool id ("void*" :) (not $ isUnionEmpty union) $ cType . snd <$> args
  let funinst = ".fun" § "=" § enclose "(" ")" (cTypeVar (cCall "(*)" cargs) ret) § funref

  -- how is environment instantiated
  let unionenvinst = ".uni." & envName § "=" § envinst
  let inst = enclose "(" ")" unionType § "{" § funinst & "," § unionenvinst § "}"

  pure (unionType, cVar v, inst)


-- It just creates a union if it does not exist and returns the types.
--  no matter what the code is supposed to do, this is how you should obtain union name and type.
--   TODO: don't generate the union if it's empty (or should the check happen outside of the function?)
cUnion :: [Type Mono] -> Type Mono -> EnvUnion Mono -> PL -- (Type, Fun Ass -> Env Ass -> Inst)
cUnion args ret union@(M.EnvUnion uid envs) = do
  envTypes <- for envs $ \env -> do
        -- this adds all environments to our scope (the one that matters :3)
        --   TODO: this is super iffy. I guess my structure aint very good.
        (envType, envName, _) <- cEnv env

        pure $ statement $ envType § envName

  let fun = statement $ do
        let cargs = bool id ("void*":) (not $ isUnionEmpty union) $ cType <$> args
        cTypeFun ret cargs "fun"

  let union = "union" §> cBlock envTypes <§ "uni;"
  let whole = do
        extra <- getExtra
        unless (uid `Set.member` extra.definedUnions) $ do
          modifyExtra $ \extra -> extra { definedUnions = Set.insert uid extra.definedUnions }
          pt $ cUnionType uid §> cBlock [fun, union] <& ";"

  addTopLevel whole


  cUnionType uid


cEnv :: Env Mono -> PPL (PL, PL, PL)  -- (Type, Name, Inst)
cEnv (M.Env eid vars) = do
  let varTypes = vars <&> \(v, t) -> do
        statement $ do
          cTypeVar (cVar v) t
  let env = do
        extra <- getExtra
        unless (eid `Set.member` extra.definedEnvs) $ do
          modifyExtra $ \extra -> extra { definedEnvs = Set.insert eid extra.definedEnvs }
          pt $ cEnvType eid §> cBlock varTypes <& ";"

  addTopLevel env

  let cvars = vars <&> \(v, _) -> "." & cVar v § "=" § cVar v
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

ccFunction :: Traversable t => PL -> Type Mono -> [PL] -> t PT -> PP
ccFunction name t args body = pt $ "static" § cTypeVar (name & enclose "(" ")" (sepBy ", " args)) t  §> cBlock body

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
sepBy sep (x:xs) = foldl' (\l r -> l & sep & r) x xs

indent :: PT -> PT
indent (PT x) = PT $ RWS.censor (fmap ("  " <>)) x

optional :: Maybe a -> (a -> PT) -> PT
optional Nothing _ = mempty
optional (Just x) f = f x

comment' :: Text -> PP
comment' = pt . comment

comment :: Text -> PT
comment text = ptt $ "// " <> text

cstr :: Text -> PL
cstr text = plt $ "\"" <> text <> "\""

pls :: Show s => s -> PL
pls = fromString . show

plt :: Text -> PL
plt = fromString . Text.unpack

ptt :: Text -> PT
ptt = fromString . Text.unpack

ppt :: Text -> PP
ppt = fromString . Text.unpack


pp :: Builtin -> PP -> Text
pp b p =
  let
    extra = Extra
      { tempcounter = 0
      , definedUnions = mempty
      , definedEnvs = mempty
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

modifyExtra :: (Extra -> Extra) -> PP
modifyExtra fmod = PP $ RWS.modify fmod -- $ \(extra, tls, ls) -> (fmod extra, tls, ls)

getExtra :: PPG Extra
getExtra = PP $ RWS.get

addTopLevel :: PP -> PL
addTopLevel thing = do
  PL $ RWS.modify $ \(extra, topLevelBlocks, lines) -> (extra, thing : topLevelBlocks, lines)


carve :: RWS r [Text] s () -> RWS r [Text] s [Text]
carve p =
  RWS.censor (const []) $ snd <$> RWS.listen p

carveg :: PP -> PPG [Text]
carveg = PP . carve . fromPP

carvet :: PT -> PPTL [Text]
carvet = PT . carve . fromPPTL

carvel :: PL -> PPL [Text]
carvel p =
  PL $ RWS.censor (const []) $ snd <$> RWS.listen p.fromPL

expr2type :: Expr Mono -> Type Mono
expr2type (Fix (M.ExprType t _)) = t

isUnionEmpty :: EnvUnion Mono -> Bool
isUnionEmpty (M.EnvUnion _ envs) = all null envs

typeFromExpr :: Expr Mono -> SpecialTypeForPrinting
typeFromExpr (Fix (M.ExprType t _)) = do
  case project t of
    M.TFun union ts ret -> Function union ts ret

    -- Brittle, but it's temporary anyway.
    M.TCon ut ts
      | ut.typeName == boolTypeName -> Bool
      | ut.typeName == intTypeName -> Integer
      | ut.typeName == TC "Unit" -> Unit
      | otherwise -> CustomType ut ts

-- In the future, when I have better codegen, this should not be required.
data SpecialTypeForPrinting
  = Integer
  | Bool
  | Unit
  | Function (EnvUnion Mono) [Type Mono] (Type Mono)
  | CustomType UniqueType [Type Mono]


ppType :: Type Mono -> Text
ppType (Fix (M.TFun _ [arg] ret)) = "" <> ppType arg <> " -> " <> ppType ret
ppType (Fix (M.TFun _ args ret)) = "(" <> Text.intercalate ", " (ppType <$> args) <> ") -> " <> ppType ret
ppType (Fix (M.TCon ut ts)) = ut.typeName.fromTC <> mconcat ((" " <>) . ppType' <$> ts)
  where
    ppType' :: Type Mono -> Text
    ppType' (Fix typ) = case typ of
      M.TFun _ [arg] ret -> "(" <> ppType' arg <> " -> " <> ppType ret <> ")"
      M.TFun _ args ret -> "((" <> Text.unwords (ppType <$> args) <> ") -> "  <> ppType ret <> ")"
      M.TCon tut [] -> tut.typeName.fromTC
      M.TCon tut tts -> "(" <> tut.typeName.fromTC <> " " <> Text.unwords (ppType' <$> tts) <> ")"


--------- polyfills ---------

unsnoc :: [a] -> Maybe ([a], a)
-- The lazy pattern ~(a, b) is important to be productive on infinite lists
-- and not to be prone to stack overflows.
-- Expressing the recursion via 'foldr' provides for list fusion.
unsnoc = foldr (\x -> Just . maybe ([], x) (\(~(a, b)) -> (x : a, b))) Nothing
{-# INLINABLE unsnoc #-}
