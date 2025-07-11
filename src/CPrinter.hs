{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant &" #-}  -- BUG(LSP): LSP thinks it's the Data.Functor operator.

module CPrinter (cModule) where

import Misc.Memo (Memo, Memoizable)
import qualified Misc.Memo as Memo
import qualified AST.Common as Common
import qualified AST.Mono as M
import Data.Maybe (listToMaybe, mapMaybe, fromJust)
import Control.Monad (when, unless, join)
import Control.Monad.Trans.RWS (RWS)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Fix (Fix (..))
import Data.Foldable (for_, sequenceA_, foldl')
import Data.Functor.Foldable (cata, project, para, embed)
import Data.Functor.Identity (Identity(..))
import Data.Functor ((<&>))
import Data.Bifunctor (first, second)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.String (IsString)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Exts (IsString (..))
import GHC.Num (Natural)
import Text.Printf (printf)
import Data.Unique (hashUnique)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Either (lefts)
import qualified Data.Map as Map
import AST.Common (Module, AnnStmt, StmtF (..), Decon, DeconF (..), DataCon (..), DataDef (..), Type, Expr, Node (..), ExprF (..), TypeF (..), Function, IfStmt (..))
import AST.Mono (M)
import AST.Def ((:.)(..), Annotated (..), CtxData (..), Op (..), Locality, pp, fmap2)
import qualified AST.Def as Def


-- COMPLAINTS:
--  - hashUnique - we should make sure we generate correct IDs. it's okay for now, though.




cModule :: Module M -> Text
cModule M.Mod { M.topLevelStatements = stmts } =
  let tlBlocks = runPP $ cMain stmts
   in Text.unlines tlBlocks


runPP :: PP -> [Text]
runPP px =
  let ((), ctx, extraStatements) = RWS.runRWS (fromPP px) () emptyContext
   in case filter (not . Text.null) extraStatements of
        [] -> Set.toList ctx.headings <> reverse ctx.topLevelBlocks

        -- I assume no top level statements should be left.
        _ : _ -> error $ printf "[COMPILER ERROR]: Bad compilation. Statements left: %s\n" (Text.unlines $ fmap (\s -> "\"" <> s <> "\"") extraStatements)



cMain :: [AnnStmt M] -> PP
cMain stmts | null stmts || all (\(Fix (O (Annotated _ stmt))) -> case stmt of { Pass -> True; _ -> False }) stmts  = pl $ addTopLevel $ "int" § "main" & "()" <§ cBlock [statement "return 0"]  -- TEMP: return 0 when all statements are empty.
cMain stmts = pl $ addTopLevel $ "int" § "main" & "()" <§ cBlock (cStmt <$> stmts)


cStmt :: AnnStmt M -> PP
cStmt = cata $ \(O (Annotated _ monoStmt)) -> case monoStmt of
  Pass -> mempty
  Print et ->
    let e = cExpr et
     in do
      pl $ include "stdio.h"
      case typeFromExpr et of
          Bool ->
            statement $ cPrintf "%s\\n" [cTernary e (cstr "True") (cstr "False")]
          Integer ->
            statement $ cPrintf "%d\\n" [e]
          Unit -> do
            bareExpression e
            statement $ cPrintf "()\\n" []
          CustomType dd ts unions -> do
            bareExpression e
            statement $ cPrintf (Def.ctx' (Def.defaultContext { silent = False, printIdentifiers = False, displayTypeParameters = True }) pp (Fix (TCon dd ts []) :: Type M) <> "\\n") []
          Function union args ret ->
            let e' =
                  if M.areAllEnvsEmpty union
                    then e
                    else e & ".fun"
             in statement $ cPrintf (visibleType (Fix (TFun union args ret)) <> " at %p\\n") [enclose "(" ")" "void*" § e']
    where
      bareExpression = statement . (enclose "(" ")" "void" §)
  Assignment uv e -> statement $ cDefinition (Common.typeOfNode e) (cVarName uv) § "=" § cExpr e
  Mutation uv e -> statement $ cVarName uv § "=" § cExpr e
  -- Mutation uv Def.FromEnvironment e -> do
  --   pl "// ERROR: we don't handle references yet!"
  --   statement $ cVarName uv § "=" § cExpr e
  ExprStmt e -> statement $ cExpr e
  Return e ->
    statement $ "return" § cExpr e

  If (IfStmt cond bodyIfTrue elseIfs elseBody) -> do
    "if" § enclose "(" ")" (cExpr cond) <§ cBlock bodyIfTrue

    for_ elseIfs $ \(elifCond, elifBody) ->
      "else" § "if" § enclose "(" ")" (cExpr elifCond) <§ cBlock elifBody

    optional elseBody $ \els ->
      "else" <§ cBlock els

  Switch switch (firstCase :| otherCases) -> do
    cond <- createIntermediateVariable' (Common.typeOfNode switch) (cExpr switch)

    "if" § enclose "(" ")" (cDeconCondition cond firstCase.deconstruction) <§ do
      let vars = cDeconAccess cond firstCase.deconstruction
      let defs = vars <&> \(uv, t, acc) -> statement $ cDefinition t (cVarName uv) § "=" § acc
      cBlock $ NonEmpty.prependList defs firstCase.caseBody

    for_ otherCases $ \kase ->
      "else" § "if" § enclose "(" ")" (cDeconCondition cond kase.deconstruction) <§ do
        -- TODO: could be factored out.
        let vars = cDeconAccess cond kase.deconstruction
        let defs = vars <&> \(uv, t, acc) -> statement $ cDefinition t (cVarName uv) § "=" § acc

        cBlock $ NonEmpty.prependList defs kase.caseBody

    -- this should not be needed. just in case.
    --  NOTE: maybe I should leave it even if I have proper completeness checking? just to exit if there is some weird casting going on or, even worse, data corruption.
    "else" <§ cBlock
        [ statement $ do
          include "stdio.h"
          cCall "printf" [cstr "Case not matched on line %d.\n", "__LINE__"]

        , statement $ do
          include "stdlib.h"
          cCall "exit" ["1"]
        ]


  Fun envs ->
    for_ envs $ \(_, env) ->
      unless (M.isEnvEmpty env) $
        statement $ do
          envNames <- cEnv env
          envNames.envType § envNames.envName § "=" § envNames.envInstantiation

  Inst () -> undefined
  Other () -> undefined


cDeconCondition :: PL -> Decon M -> PL
cDeconCondition basevar mdecon =
  let conjunction = fmap (basevar &) $ flip cata mdecon $ \(N _ d) -> case d of
        CaseVariable _ -> []
        CaseRecord _ recs -> flip foldMap (NonEmpty.toList recs) $ \(um, rec) -> fmap (\c -> "." & cRecMember um & c) rec
        CaseConstructor dc@(DC (DD _ _ cons _) uc _ _) args ->
          let cons' = fromJust $ Def.eitherToMaybe cons  -- cannot be a record type! NOTE: this is ugly, should I just make two separate types?
          in case cons' of
            [] -> undefined
            conz | all (\(DC _ _ conargs _) -> null conargs) conz -> [" ==" § cCon dc]
            [_] -> flip concatMap (zip [1::Int ..] args) $ \(x, conargs) -> conargs <&> \ca -> "." & cConMember uc x & ca
            _:_ -> ("." & "tag" § "==" § cTag dc) : concatMap (\(x, conargs) -> conargs <&> \ca -> "." & "env" & "." & cConStruct dc & "." & cConMember uc x & ca) (zip [1::Int ..] args)

  in case conjunction of
    [] -> do
      include "stdbool.h"  -- kekek.
      "true"

    ps@(_:_) -> sepBy " && " ps

cDeconAccess :: PL -> Decon M -> [(Def.UniqueVar, Type M, PL)]
cDeconAccess basevar mdecon = fmap2 (basevar &) $ flip cata mdecon $ \(N t d) -> case d of
  CaseVariable uv -> [(uv, t, "" :: PL)]
  CaseRecord _ recs -> flip foldMap (NonEmpty.toList recs) $ \(um, rec) ->
    flip fmap2 rec $ \acc -> "." & cRecMember um & acc

  CaseConstructor dc@(DC (DD _ _ cons _) uc _ _) args ->
    let cons' = fromJust $ Def.eitherToMaybe cons
    in case cons' of
      []  -> []
      conz | all (\(DC _ _ conargs _) -> null conargs) conz -> []

      [_] -> flip concatMap (zip [1::Int ..] args) $ \(x, conargs) -> fmap2 (("." & cConMember uc x) &) conargs

      _:_ -> concatMap (\(x, conargs) -> fmap2 (("." & "env" & "." & cConStruct dc & "." & cConMember uc x) &) conargs) (zip [1::Int ..] args)


cExpr :: Expr M -> PL
cExpr expr = flip para expr $ \(N t e) -> case fmap (first Common.typeOfNode) e of
  Call (ft, fn) args ->
      let union = case ft of
            Fix (TFun munion _ _) -> munion
            _ -> undefined  -- should not happen.

       in if M.areAllEnvsEmpty union
            then
              cCall fn $ fmap snd args
            else do
              v <- createIntermediateVariable ft fn
              cCall (v & ".fun") $ ("&" & v & ".env") : fmap snd args

  Op (lt, le) Equals (rt, re) | not (isBuiltinType lt)-> do
    le' <- createIntermediateVariable lt le
    re' <- createIntermediateVariable rt re

    include "string.h"
    enclose "(" ")" $ "0" § "==" § cCall "memcmp" [cRef le', cRef re', cSizeOf lt]

  Op (lt, le) NotEquals (rt, re) | not (isBuiltinType lt)-> do
    le' <- createIntermediateVariable lt le
    re' <- createIntermediateVariable rt re

    include "string.h"
    enclose "(" ")" $ "0" § "!=" § cCall "memcmp" [cRef le', cRef re', cSizeOf lt]

  RecUpdate (et, ee) upd -> do
    let dd@DD { ddCons = erecs } = case project et of
          TCon dd _ _ -> dd
          _ -> undefined
    let records = case erecs of
          Left recs -> recs
          Right _ -> error "Not a record type!!!"

    let updatedFields = Set.fromList $ NonEmpty.toList $ fst <$> upd
    let persistedFields = filter (`Set.notMember` updatedFields) $ NonEmpty.toList $ records <&> \(Annotated _ (um, _)) -> um

    initializePersistedFields <- case persistedFields of
          []    -> pure []
          (_:_) -> do
            ol'value <- createIntermediateVariable et ee
            pure $ persistedFields <&> \um ->
              (um, ol'value & "." & cRecMember um)
    let initializeUpdatedFields = upd <&> \(um, (_, me)) ->
          (um, me)

    cRecordInit dd (NonEmpty.prependList initializePersistedFields initializeUpdatedFields)

  -- branch without the need for added types.
  pe -> case fmap snd pe of
    Lit (Def.LInt x) -> pls x

    -- here, referencing a normal variable. no need to do anything special.
    Var v loc -> cVar t loc v
    Con uc _ -> cCon uc
    Op l op r -> enclose "(" ")" $ l § cOp op § r
    Lam env params body -> cLambda env params t body
    MemAccess ee mem -> ee & "." & cRecMember mem
    RecCon dd insts -> cRecordInit dd insts
    _ -> undefined

cRecordInit :: DataDef M -> NonEmpty (Def.UniqueMem, PL) -> PL
cRecordInit (DD ut _ _ _) insts =
  let dataTypeName = plt ut.typeName.fromTC & "__" & pls (hashUnique ut.typeID)
  in enclose "(" ")" dataTypeName § Def.encloseSepBy "{" "}" ", " [
      "." & cRecMember um § "=" § e | (um, e) <- NonEmpty.toList insts
    ]


cUnion :: [Type M] -> Type M -> M.EnvUnion -> PL
cUnion args ret union' =

  -- Memoize all this stuff.
  unpack $ Memo.memo' (compiledUnions . fst) (\memo -> mapPLCtx $ \ctx -> ctx { compiledUnions = memo }) union' $ \union _ ->
    if M.areAllEnvsEmpty union
      then pure $ cTypeFun ret (cType <$> args) ""
      else do
          let unionType = "struct" § "ut" & pls (hashUnique union'.unionID.fromUnionID)

          let params = "void*" : (cType <$> args)
          let functionType = cTypeFun ret params "fun"
          let allEnvs = union.union <&> \env -> do
                -- instantiate the environment part.
                unless (M.isEnvEmpty env) $ statement $ do
                  envNames <- cEnv env
                  envNames.envType § envNames.envName

          addTopLevel $ unionType <§ cBlock
            [
              statement functionType,
              "union" <§ cBlock allEnvs §> "env;"
            ] §> ";"

          pure unionType



cEnv :: M.Env -> PPL EnvNames
cEnv = Memo.memo (compiledEnvs . fst) (\memo -> mapPLCtx $ \ctx -> ctx { compiledEnvs = memo }) $ \menv _ -> do
  case menv of
    M.RecursiveEnv _ _ -> undefined
    M.Env eid vars -> do
      -- safety measure for bugs
      when (M.isEnvEmpty menv) $
        error "[COMPILER ERROR]: Called `cEnv` with an empty environment. I can ignore it, but this is probably a bug. This should be checked beforehand btw. Why? sometimes, it requires special handling, so making it an error kind of makes me aware of this."

      let uniqueVars = fmap snd $ Map.toList $ Map.fromList $ vars <&> \case
            tup@(v@(M.DefinedFunction _), _, t) | doesFunctionNeedExplicitEnvironment t -> ((v, Just t), tup)
            tup@(v, _, _) -> ((v, Nothing), tup)

      let envVarName v t = case v of
              M.DefinedVariable uv -> cVarName uv
              M.DefinedFunction fn | doesFunctionNeedExplicitEnvironment t -> cEnvFunctionVarName (cFunction t fn) t
              M.DefinedFunction fn -> cFunction t fn

      let varTypes =
            uniqueVars <&> \(v, _, t) -> statement $ do
            cDefinition t $ envVarName v t

      let etype = "struct" § "et" & pls (hashUnique eid.fromEnvID)
      let env = etype <§ cBlock varTypes §> ";"
      addTopLevel env


      let name = "et" & pls (hashUnique eid.fromEnvID) & "s"
      let cvarInsts = uniqueVars <&> \(v, loc, t) -> "." & envVarName v t § "=" § cVar t loc v
      let inst = enclose "{ " " }" $ sepBy ", " cvarInsts
      pure EnvNames { envType = etype, envName = name, envInstantiation = inst }



cLambda :: M.Env -> [(Def.UniqueVar, Type M)] -> Type M -> PL -> PL
cLambda env params lamType lamBody = do
  tmp <- nextTemp

  -- type safety fans are SEETHING rn (#2)
  let (needsEnv, union, ret) = case project lamType of
       TFun munion _ mret ->
        (not $ M.areAllEnvsEmpty munion, cUnion (snd <$> params) mret munion, mret)
       TCon _ _ _ -> undefined

  let funref = tmp <> "_lambda"
  let cbody = [statement $ "return" § lamBody]
  let cparams = params <&> \(uv, t) -> cDefinition t (cVarName uv)
  let ccparams = if not needsEnv
      then cparams
      else
        let envparam = if M.isEnvEmpty env
            then "void*"
            else do
              envNames <- cEnv env
              cPtr envNames.envType
        in (envparam § "env") : cparams

  addTopLevel $ ccFunction funref ret ccparams cbody

  -- initialize union
  if not needsEnv
    -- we don't - just reference the function
    then funref

    -- there is an environment - either this function's env or some other environment. If it's not our function's, then we don't need to initialize it.
    else if M.isEnvEmpty env
      then "(" § union § ")" § "{" § ".fun" § "=" § cCast (cTypeFun ret ("void*" : cparams) "") funref § "}"

      else do
        envNames <- cEnv env
        "(" § union § ")" § "{" § ".fun" § "=" § cCast (cTypeFun ret ("void*" : cparams) "") funref & "," § ".env." & envNames.envName § "=" § envNames.envInstantiation § "}"



cFunction :: Type M -> Function M -> PL
cFunction fnt fun' =
  let needsEnv' = doesFunctionNeedExplicitEnvironment fnt
  in unpack $ Memo.memo' (compiledFunctions . fst) (\memo -> mapPLCtx $ \ctx -> ctx { compiledFunctions = memo }) (fun', needsEnv') $ \(fun, needsEnv) _ -> do
    let fd = fun.functionDeclaration
    let funref = cVarName fd.functionId

    -- prepare parameters for funny deconstruction.
    let nonDeconstructions = project . fst <$> fd.functionParameters <&> \(N t d) -> case d of -- find parameters that are just variables (to reduce noise, it doesn't actually matter.)
          CaseVariable uv -> Right uv
          kase -> Left (embed (N t kase))

    let paramTypes = snd <$> fd.functionParameters

    -- replace missing with temps
    addedTempsToParams <- for nonDeconstructions $ \case
      Right uv -> pure $ Right $ cVarName uv
      Left _ -> Left <$> nextTemp

    let filledIn = addedTempsToParams <&> \case { Left l -> l; Right r -> r }

    let cparams = zip filledIn paramTypes <&> \(var, t) -> cDefinition t var
    let envparam = do
          let envtype = if M.isEnvEmpty fd.functionEnv
              then "void*"
              else do
                envNames <- cEnv fd.functionEnv
                cPtr envNames.envType

          envtype § "env"

    let ccparams =
          if not needsEnv
            then cparams
            else envparam : cparams


    -- prepare deconstructions!!
    let actualDeconstructions = lefts nonDeconstructions
    let body = case actualDeconstructions of
          [] -> cStmt <$> fun.functionBody
          _:_ -> guard <| NonEmpty.prependList accesses (cStmt <$> fun.functionBody)
            where
              tempsForDeconstructions = lefts addedTempsToParams
              bigCondition = "!" & enclose "(" ")" (sepBy " && " $ zipWith cDeconCondition tempsForDeconstructions actualDeconstructions)  -- make a big condition. if it's not satisfied, we must fail immediately.

              guard = "if" § enclose "(" ")" bigCondition <§ cBlock
                    [ statement $ do
                      include "stdio.h"
                      cCall "printf" [cstr "Pattern not satisfied to enter function (line %d).\n", "__LINE__"]

                    , statement $ do
                      include "stdlib.h"
                      cCall "exit" ["1"]
                    ]


              varAccesses = concat $ zipWith cDeconAccess tempsForDeconstructions actualDeconstructions
              accesses = varAccesses <&> \(uv, t, acc) -> statement $ cDefinition t (cVarName uv) § "=" § acc


    addTopLevel $ ccFunction funref fd.functionReturnType ccparams body

    -- return the function identifier.
    pure funref



addTopLevel :: PP -> PL
addTopLevel tl = do
  tl' <- asTopLevel tl
  PL $ RWS.modify $ mapPLCtx $ \ctx -> ctx { topLevelBlocks = tl' : ctx.topLevelBlocks }


addIncludeIfPresent :: [Def.Ann] -> PL
addIncludeIfPresent anns =
  for_ includes $ \lib ->
    include lib
  where
    includes = mapMaybe (\case { Def.ACStdInclude inclname -> Just inclname; _ -> Nothing }) anns


include :: Text -> PL
include lib = addHeading $ "#include <" <> lib <> ">"


addHeading :: Text -> PL
addHeading heading = PL $ RWS.modify $ mapPLCtx $ \ctx -> ctx { headings = Set.insert heading ctx.headings }




----------
-- Unique Naming and shiz: Compiling functions and datatypes.
---------

cDefinition :: Type M -> PL -> PL
cDefinition (Fix t) v = case t of
  TCon dd _ _ -> cDataType dd § v
  TFun union args ret | not (M.areAllEnvsEmpty union) -> cUnion args ret union § v

  TFun _ args ret -> cTypeFun ret (cType <$> args) v

-- Function printing logic (i had to use it in two places and I *really* don't want to duplicate this behavior.)
cTypeFun :: Type M -> [PL] -> PL -> PL
cTypeFun ret cargs v = cDefinition ret (cCall (enclose "(*" ")" v) cargs)

cType :: Type M -> PL
cType (Fix t) = case t of
  TCon dd _ _ -> cDataType dd
  TFun union args ret | M.areAllEnvsEmpty union ->
    let cargs = cType <$> args
    in cDefinition ret (cCall "(*)" cargs)

  TFun union args ret -> cUnion args ret union


cDataType :: DataDef M -> PL
cDataType dd' = unpack $ Memo.memo' (compiledTypes . fst) (\memo -> mapPLCtx $ \ctx -> ctx { compiledTypes = memo }) dd' $ \dd@(DD _ _ econrec anns) addMemo -> do
  -- don't forget to add a required library
  addIncludeIfPresent anns

  let representsBuiltin = find (\case { Def.ACType con -> Just con; _ -> Nothing }) dd.ddAnns
      ut = dd.ddName
  case representsBuiltin of
    Just t -> pure $ plt t
    Nothing -> do
      let dataTypeName = plt ut.typeName.fromTC & "__" & pls (hashUnique ut.typeID)
      addMemo dataTypeName

      -- Check if it's a record or an ADT
      case econrec of
        -- it's a record!
        Left recs -> do
          addTopLevel $ "typedef" <§ cRecordStruct recs §> dataTypeName & ";"

        -- it's am ADT
        Right cons ->
          case cons of
            -- 0. No constructors (empty, TODO probably impossible? (because after monomorphization, this type will disappear, as it won't be able to be instantiated))
            [] ->
              pure mempty

            -- 1. enum
            dc
              | all (\(DC _ _ args _) -> null args) dc -> addTopLevel $ "typedef" § "enum" <§ cBlock [pl $ sepBy ", " $ cCon <$> dc] §> dataTypeName & ";"

            -- 2. struct
            [dc@(DC _ uc ts _)] -> do
              addTopLevel $ "typedef" <§ cStruct dc §> dataTypeName & ";"

              -- then, create a data constructor function
              addTopLevel $ ccFunction (cCon dc) (Fix $ TCon dd undefined undefined) [cDefinition t (cConMember uc i) | (t, i) <- zip ts [1 :: Int ..]]
                [
                  statement $ "return" § enclose "(" ")" dataTypeName § "{" § sepBy ", " ["." & cConMember uc i § "=" § cConMember uc i | (_, i) <- zip ts [1 :: Int ..]] § "}"
                ]


            -- 3. ADT
            dcs -> do
              let tags = cTag <$> dcs
              addTopLevel $ "typedef" § "struct" <§ cBlock
                [ "enum" <§ cBlock [pl $ sepBy ", " tags] §> "tag;"
                , "union" <§ cBlock [cStruct dc §> cConStruct dc & ";" | dc@(DC _ _ (_:_) _) <- dcs ] §> "env;"
                ] §> dataTypeName & ";"

              -- also, generate accessors
              for_ dcs $ \case
                -- for a constructor with no arguments....... generate preprocessor directives (TODO: bad.) try to make a better hierarchy of unique names. less functions, etc.
                dc@(DC _ _ [] _) -> do
                  addTopLevel $ pl $
                    "#define" § cCon dc § enclose "(" ")"
                      (enclose "(" ")" dataTypeName § "{" § ".tag" § "=" § cTag dc § "}")

                dc@(DC _ uc ts@(_:_) _) -> do
                  addTopLevel $ ccFunction (cCon dc) (Fix $ TCon dd undefined undefined) [cDefinition t (cConMember uc i) | (t, i) <- zip ts [1 :: Int ..]]
                    [
                      statement $ "return" § enclose "(" ")" dataTypeName § "{" § sepBy ", "
                        [ ".tag" § "=" § cTag dc
                        , ".env." & cConStruct dc § "=" § "{" § sepBy ", " ["." & cConMember uc i § "=" § cConMember uc i | (_, i) <- zip ts [1 :: Int ..]] § "}"
                        ]
                        § "}"
                    ]

      pure dataTypeName


cStruct :: DataCon M -> PP
cStruct (DC _ _ [] _) = mempty  -- this might be called by the ADT part of `cDataType`.
cStruct (DC _ uc ts@(_:_) _) = "struct" <§ cBlock
  [member t i | (t, i) <- zip ts [1 :: Int ..]]
  where
    member t i =
      statement $ cDefinition t (cConMember uc i)

cRecordStruct :: NonEmpty (Annotated (Def.UniqueMem, Type M)) -> PP
cRecordStruct recs = "struct" <§ cBlock
  [ statement $ cDefinition t (cRecMember um) | Annotated _ (um, t) <- NonEmpty.toList recs ]


cVar :: Type M -> Locality -> M.Variable -> PL
cVar _ Def.Local (M.DefinedVariable uv) = cVarName uv
cVar _ Def.FromEnvironment{} (M.DefinedVariable uv) = "env->" <> cVarName uv
cVar t Def.FromEnvironment{} (M.DefinedFunction fun) | doesFunctionNeedExplicitEnvironment t  =
  "env->" & cEnvFunctionVarName (cFunction t fun) t

cVar t Def.FromEnvironment{} (M.DefinedFunction fun) =
  "env->" & cFunction t fun

cVar t Def.Local (M.DefinedFunction fun) = do
  -- type safety fans are SEETHING rn
  let (union, args, ret) = case project t of
       TFun munion margs mret -> (cUnion margs mret munion, margs, mret)
       TCon _ _ _ -> undefined

  -- check if we even need an environment
  if not $ doesFunctionNeedExplicitEnvironment t
    -- we don't - just reference the function
    then cFunction t fun

    -- there is an environment - either this function's env or some other environment. If it's not our function's, then we don't need to initialize it.
    else if M.isEnvEmpty fun.functionDeclaration.functionEnv
      then "(" § union § ")" § "{" § ".fun" § "=" § cCast (cTypeFun ret ("void*" : (cType <$> args)) "") (cFunction t fun) § "}"

      else do
        envNames <- cEnv fun.functionDeclaration.functionEnv
        "(" § union § ")" § "{" § ".fun" § "=" § cCast (cTypeFun ret ("void*" : (cType <$> args)) "") (cFunction t fun) & "," § ".env." & envNames.envName § "=" § envNames.envName § "}"



cEnvFunctionVarName :: PL -> Type M -> PL
cEnvFunctionVarName fn t =
  let uid = case project t of
        TFun munion _ _ -> munion.unionID
        _ -> undefined
  in fn & "__" & pls (hashUnique uid.fromUnionID)

cVarName :: Def.UniqueVar -> PL
cVarName v = plt (sanitize v.varName.fromVN) & "__" & pls (hashUnique v.varID)

sanitize :: Text -> Text
sanitize = Text.concatMap $ \case
  '-' -> "_dash_"
  '_' -> "__"
  '\'' -> "_prime_"
  o -> fromString [o]


-- supposed to be the definitie source for unique names.
cCon :: DataCon M -> PL
-- type constructor with arguments - treat it as a function
cCon (DC _ c (_:_) _) = plt (sanitize c.conName.fromCN) & "__" & pls (hashUnique c.conID) & "f"
-- enum type constructor (refer to actual datatype)
cCon (DC _ c [] anns) =
  let representsBuiltin = find (\case { Def.ACLit con -> Just con; _ -> Nothing }) anns
  in case representsBuiltin of
    Just t -> plt (sanitize t)
    Nothing -> plt (sanitize c.conName.fromCN) & "__" & pls (hashUnique c.conID)


cTag :: DataCon M -> PL
cTag (DC _ c _ _) = plt (sanitize c.conName.fromCN) & "__" & pls (hashUnique c.conID) <> "t"


-- defines names of constructor members for functions to synchronize between each other.
cConMember :: Def.UniqueCon -> Int -> PL
cConMember uc i = "c" & plt (sanitize uc.conName.fromCN) & "__" & pls (hashUnique uc.conID) & "__" & pls i

cRecMember :: Def.UniqueMem -> PL
cRecMember um = "m" & plt (sanitize um.memName.fromMN) & "__" & pls (hashUnique um.memID)

cConStruct :: DataCon M -> PL
cConStruct (DC _ uc _ _) = "c" & plt (sanitize uc.conName.fromCN) & "__" & pls (hashUnique uc.conID) & "s"


isBuiltinType :: Type M -> Bool
isBuiltinType (Fix (TCon dd _ _)) = any (\case { Def.ACType _ -> True; _ -> False }) dd.ddAnns
isBuiltinType _ = False





---------------------
-- General Utility --
---------------------


cBlock :: (Traversable t) => t PP -> PP
cBlock blockLines = do
  "{"
  indent $ sequenceA_ blockLines
  "}"

ccFunction :: (Traversable t) => PL -> Type M -> [PL] -> t PP -> PP
ccFunction name t args body = "static" § cDefinition t (name & enclose "(" ")" (sepBy ", " args)) <§ cBlock body

cPrintf :: String -> [PL] -> PL
cPrintf format args = cCall "printf" (cstr format : args)

cCall :: PL -> [PL] -> PL
cCall fun args = fun & "(" & sepBy ", " args & ")"

cTernary :: PL -> PL -> PL -> PL
cTernary cond ifTrue ifFalse = cond § "?" § ifTrue § ":" § ifFalse

cOp :: Op -> PL
cOp = \case
  Plus -> "+"
  Minus -> "-"
  Times -> "*"
  Divide -> "/"
  Equals -> "=="
  NotEquals -> "!="


cRef :: PL -> PL
cRef = ("&" <>)

cPtr :: PL -> PL
cPtr = (<> "*")

cCast :: PL -> PL -> PL
cCast t x = enclose "(" ")" t § x

cSizeOf :: Type M -> PL
cSizeOf t = cCall "sizeof" [cType t]


-- constant string. should automatically escape stuff
cstr :: String -> PL
cstr s = fromString $ "\"" <> escaped <> "\""
  where
    escaped = flip concatMap s $ \case
      '"' -> "\\\""
      '\n' -> "\\n"
      c   -> pure c

createIntermediateVariable :: Type M -> PL -> PPL PL
createIntermediateVariable t e = do
  next <- nextTemp
  let assignment = statement $ cDefinition t next § "=" § e

  PL $ RWS.modify $ second (assignment :)
  pure next

createIntermediateVariable' :: Type M -> PL -> PPG PL
createIntermediateVariable' t e = do
  next <- nextTemp'
  statement $ cDefinition t next § "=" § e
  pure next


sepBy :: PL -> [PL] -> PL
sepBy _ [] = mempty
sepBy sep (x : xs) = foldl' (\l r -> l & sep & r) x xs


enclose :: PL -> PL -> PL -> PL
enclose l r x = l & x & r

optional :: Maybe a -> (a -> PP) -> PP
optional Nothing _ = mempty
optional (Just x) f = f x

indent :: PP -> PP
indent (PP x) = PP $ RWS.censor (fmap ("  " <>)) x




--------
-- Basic functions
-------

infixr 7 &

(&) :: PL -> PL -> PL
(&) = (<>)

infixr 6 § -- hihi

(§) :: PL -> PL -> PL
(§) p1 p2 = p1 & " " & p2

infixl 4 <§

(<§) :: PL -> PP -> PP
(<§) l r = do
  line <- asLine l
  appendFront line r

infixr 5 §>

(§>) :: PP -> PL -> PP
(§>) l r = do
  line <- asLine r
  appendBack line l

asLine :: PL -> PPG Text
asLine p = pl $ PL $ RWS.censor (const []) $ Text.concat . snd <$> RWS.listen p.fromPL

asTopLevel :: PP -> PPL Text
asTopLevel (PP p) = PL $ RWS.RWST $ \r (s, ogText) -> do
  let ((), s', additionalLines) = RWS.runRWS p r s
  Identity (Text.unlines additionalLines, (s', ogText), [])

appendFront :: Text -> PP -> PP
appendFront line p = do
  ppLines <- PP $ RWS.censor (const []) $ snd <$> RWS.listen p.fromPP
  PP $ case ppLines of
    [] -> RWS.tell [line]
    (li : lis) | Text.null line -> RWS.tell $ li : lis
    (li : lis) -> RWS.tell $ (line <> " " <> li) : lis

appendBack :: Text -> PP -> PP
appendBack line p = do
  ppLines <- PP $ RWS.censor (const []) $ snd <$> RWS.listen p.fromPP
  PP $ case unsnoc ppLines of
    Nothing -> RWS.tell [line]
    Just (lis, li) | Text.null line -> RWS.tell $ lis ++ [li]
    Just (lis, li) -> RWS.tell $ lis ++ [li <> " " <> line]

statement :: PPL a -> PPG a
statement line = pl $ do
  x <- line
  ";"
  pure x


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
  unless (null tokens) $ PP $ RWS.tell [line]

  pure x

pls :: Show a => a -> PL
pls = fromString . show

plt :: Text -> PL
plt = fromString . Text.unpack



-----------------
-- Monadic context, states and weird ass functions.
-----------------

-- Global PP state.
newtype PPG a = PP {fromPP :: RWS () [Text] Context a} deriving (Functor, Applicative, Monad)

type PP = PPG ()


instance (a ~ ()) => Semigroup (PPG a) where
  PP l <> PP r = PP $ l >> r

instance (a ~ ()) => Monoid (PPG a) where
  mempty = PP $ RWS.rws $ \_ s -> (mempty, s, [])



-- Line (Expression) PP state.
newtype PPL a = PL {fromPL :: RWS () [Text] (Context, [AdditionalLine]) a} deriving (Functor, Applicative, Monad, Memoizable)

type PL = PPL ()

type AdditionalLine = PP -- TODO: maybe make it text, so everything evaluates correctly.


instance (a ~ ()) => Semigroup (PPL a) where
  PL l <> PL r = PL $ l >> r

instance (a ~ ()) => Monoid (PPL a) where
  mempty = PL $ RWS.rws $ \_ s -> (mempty, s, [])

instance (a ~ ()) => IsString (PPG a) where
  fromString s = PP $ RWS.rws $ \_ ctx -> ((), ctx, [Text.pack s])

instance (a ~ ()) => IsString (PPL a) where
  fromString s = PL $ RWS.rws $ \_ ctx -> ((), ctx, [Text.pack s])


data Context = Context
  { tempcounter :: Natural
  , headings :: Set Text
  , topLevelBlocks :: [Text]

  , compiledUnions :: Memo M.EnvUnion PL
  , compiledEnvs :: Memo M.Env EnvNames
  , compiledFunctions :: Memo (Function M, NeedsImplicitEnvironment) PL
  , compiledTypes :: Memo (DataDef M) PL
  }
type NeedsImplicitEnvironment = Bool

emptyContext :: Context
emptyContext =
  Context
    { tempcounter = 0,
      headings = mempty,
      topLevelBlocks = []

    , compiledUnions = Memo.emptyMemo
    , compiledEnvs = Memo.emptyMemo
    , compiledFunctions = Memo.emptyMemo
    , compiledTypes = Memo.emptyMemo
    }

mapPLCtx :: (Context -> Context) -> (Context, [AdditionalLine]) -> (Context, [AdditionalLine])
mapPLCtx f (ctx, additionalLines) = (f ctx, additionalLines)


data EnvNames = EnvNames
  { envType :: PL
  , envName :: PL
  , envInstantiation :: PL
  }

nextTemp :: PPL PL
nextTemp = do
  extra <- PL $ RWS.gets fst
  PL $ RWS.modify $ \(ext, ls) -> (ext {tempcounter = ext.tempcounter + 1}, ls)

  let nextID = fromString $ "temp" <> show extra.tempcounter
  pure nextID

nextTemp' :: PPG PL
nextTemp' = do
  extra <- PP RWS.get
  PP $ RWS.modify $ \ext -> ext {tempcounter = ext.tempcounter + 1}

  let nextID = fromString $ "tltemp" <> show extra.tempcounter
  pure nextID


-- In the future, when I have better codegen, this should not be required.
data SpecialTypeForPrinting
  = Integer
  | Bool
  | Unit
  | Function M.EnvUnion [Type M] (Type M)
  | CustomType (DataDef M) [Type M] [M.EnvUnion]

typeFromExpr :: Expr M -> SpecialTypeForPrinting
typeFromExpr (Fix (N t _)) = case project t of
  TFun union ts ret -> Function union ts ret
  -- Brittle, but it's temporary anyway.
  TCon dd ts unions
    | dd.ddName.typeName == Def.TC "Bool" -> Bool
    | dd.ddName.typeName == Def.TC "Int" -> Integer
    | dd.ddName.typeName == Def.TC "Unit" -> Unit
    | otherwise -> CustomType dd ts unions

find :: (a -> Maybe b) -> [a] -> Maybe b
find f = listToMaybe . mapMaybe f

unpack :: PPL PL -> PL
unpack = join


visibleType :: Type M -> String
visibleType = cata $ \case
  TFun _ [arg] ret -> printf "%s -> %s" arg ret
  TFun _ ts ret -> printf "(%s) -> %s" (intercalate ", " ts) ret
  TCon dd _ _ -> Text.unpack dd.ddName.typeName.fromTC


doesFunctionNeedExplicitEnvironment :: Type M -> NeedsImplicitEnvironment
doesFunctionNeedExplicitEnvironment t = case project t of
    TFun union _ _ -> not $ M.areAllEnvsEmpty union
    _ -> undefined



-- (((polyfill)))
unsnoc :: [a] -> Maybe ([a], a)
-- The lazy pattern ~(a, b) is important to be productive on infinite lists
-- and not to be prone to stack overflows.
-- Expressing the recursion via 'foldr' provides for list fusion.
unsnoc = foldr (\x -> Just . maybe ([], x) (\(~(a, b)) -> (x : a, b))) Nothing
{-# INLINEABLE unsnoc #-}

