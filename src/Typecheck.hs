{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Typecheck (typecheck, TypeError(..)) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.Trans.RWS (RWST (RWST), runRWST)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (Base, cata, embed, hoist, project, para)
import Control.Monad (replicateM, zipWithM_, when)
import Data.Bitraversable (bitraverse)
import Data.Foldable (for_, fold)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Bifunctor (bimap)
import Data.List ( find )
import Data.Bifoldable (bifoldMap, bifold)
import Data.Traversable (for)


import qualified AST.Resolved as R
import qualified AST.Typed as T

import AST.Converged (Prelude(..), PreludeFind (..), boolFind, tlReturnFind, intFind, floatFind)
import AST.Common (TVar (TV), LitType (..), UniqueVar, UniqueType (typeName), Annotated (Annotated), Op (..), EnvID (..), UnionID (..), ctx, type (:.) (..), ppCon, Locality (..), ppUnionID, phase, ctxPrint, ctxPrint', Binding (..), mustOr)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe)
import AST.Typed (TyVar, Scheme (..), extractUnionsFromDataType, extractUnionsFromConstructor)
import Text.Printf (printf)
import Control.Applicative (liftA3)
import Data.List.NonEmpty (NonEmpty)
import Misc.Memo (memo, Memo(..))
import qualified AST.Common as Common



----------- TO REMEMBER -----------------
-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)

typecheck :: Maybe Prelude -> R.Module -> IO ([TypeError], T.Module)
typecheck mprelude rStmts = do
    let tcContext = Ctx { prelude = mprelude, returnType = Nothing }
    let senv = emptySEnv  -- we add typechecking state here, because it might be shared between modules? (especially memoization!)... hol up, is there anything to even share?

    -- Step 1: Generate type substitution (typing context) based on the constraints.
    (tStmts, su, errs) <- generateSubstitution tcContext senv rStmts

    phase "Typechecking (Before substitution)"
    ctxPrint T.tModule tStmts


    ----- Step 1.5: Substitute tyvars in Subst's unions, because they are not actively substituted yet?
    -- HACK: I didn't check it when that happens, so I'll do it at the end.
    --  Unions that are to be substituted may have unsubstituted parameters. This should quickly fix that. However, I'm not sure where this happens. So, this is a TODO to figure out why this happens and when.
    -- ISSUE(function-tvars-in-its-env)
    let Subst suUnions suTVs = su
    let suNoUnions = Subst mempty suTVs
    let suUnions' = subst suNoUnions <$> suUnions
    let su' = Subst suUnions' suTVs

    phase "Typechecking (og subst)"
    ctxPrint' $ dbgSubst su

    phase "Typechecking (fixed subst)"
    ctxPrint' $ dbgSubst su'


    -- Step 2: Substitute the types with the inferred ones.
    let tStmts' = subst su' tStmts
    let errs' = errs <> (AmbiguousType <$> Set.toList (ftv tStmts'))

    pure (errs', tStmts')



-- ---------------------------
-- --      INFERENCE        --
-- ---------------------------

generateSubstitution :: Context -> TypecheckingState -> R.Module -> IO (T.Module, Subst, [TypeError])
generateSubstitution env senv rModule = do
  (tvModule, s, errors) <- runRWST infer env senv

  pure (tvModule, s.typeSubstitution, errors)
  where
    infer = do
      -- Typecheck *all* functions, datatypes, etc. We want to typecheck a function even if it's not used (unlike Zig!)
      dds <- inferDatatypes rModule.datatypes
      fns <- inferFunctions rModule.functions
      tls <- inferTopLevel rModule.toplevel
      exs <- inferExports rModule.exports
      pure $ T.Mod
        { T.toplevelStatements = tls
        , T.exports = exs
        , T.functions = fns
        , T.datatypes = dds
        }

    inferFunctions fns = for fns inferFunction
    inferDatatypes dds = for dds inferDataDef
    inferTopLevel = inferStmts


-- Typechecks the top level part of the file.
--  Note: for top level, the return value will be set as U8, because of POSIX exit values.
--   Ideally, this type should mimic the target platform.
inferStmts :: (Traversable t) => t R.AnnStmt -> Infer (t T.AnnStmt)
inferStmts = traverse conStmtScaffolding  -- go through the block of statements...
  where
    -- for each statement...
    conStmtScaffolding :: R.AnnStmt -> Infer T.AnnStmt
    conStmtScaffolding = cata (fmap embed . inferAnnStmt)

    -- go through additional layers (in the future also position information)...
    inferAnnStmt :: Base R.AnnStmt (Infer a) -> Infer (Base T.AnnStmt a)
    inferAnnStmt (O (Annotated anns rStmt)) = do
        tstmt <- bitraverse inferExpr id rStmt

        -- Map expr -> type for unification
        let ttstmt = first (\expr@(Fix (T.TypedExpr t _)) -> (expr, t)) tstmt
        O . Annotated anns <$> inferStmt ttstmt

    inferStmt :: R.StmtF (T.Expr, T.Type) a -> Infer (T.StmtF T.Expr a)
    inferStmt stmt = case stmt of

      R.Assignment v (rexpr, t) -> do
        vt <- var v
        vt `uni` t

        pure $ T.Assignment v rexpr


      R.Mutation v loc (expr, t) -> do
        vt <- var v
        vt `uni` t
        addEnv (T.DefinedVariable v) vt

        pure $ T.Mutation v loc expr


      R.If (cond, condt) ifTrue elseIfs ifFalse -> do
        boolt <- findBuiltinType boolFind

        condt `uni` boolt

        for_ elseIfs $ \((_, t), _) ->
          t `uni` boolt

        pure $ T.If cond ifTrue ((fmap . first) fst elseIfs) ifFalse


      R.Switch (rswitch, switchType) cases -> do
        -- infer the type for the expression inserted into the switch...
        tdecons <- traverse inferCase cases

        for_ tdecons $ \(_, dec) ->
          -- ...each deconstruction should be of that type.
          switchType `uni` dec

        pure $ T.Switch rswitch (fst <$> tdecons)
        where

          inferCase R.Case { R.deconstruction = decon, R.caseCondition = caseCon, R.body = body } = do
            tdecon <- inferDecon decon
            let tCaseCon = fst <$> caseCon
            pure (T.Case tdecon tCaseCon body, T.decon2type tdecon)


          inferDecon :: R.Decon -> Infer T.Decon
          inferDecon = cata $ fmap embed . f where
            f = \case
              -- R.CaseVariable uv -> do
              --   t <- lookupVar uv

              --   pure (T.CaseVariable t uv)

              -- R.CaseConstructor uc args -> do

              --   -- HACK! Unify the case statement by creating a fake function type.
              --   ct <- lookupCon uc
              --   let conOnly = case ct of
              --         Fix (T.TCon {}) -> ct
              --         Fix (T.TFun _ _ c@(Fix (T.TCon {}))) -> c

              --         -- error in resolver: just return a fresh type. (lookupCon already does that)
              --         _ -> ct

              --   args' <- sequenceA args
              --   syntheticConType <- case args' of
              --         [] -> pure conOnly
              --         (_:_) -> do
              --           un <- emptyUnion
              --           pure $ Fix $ TFun un (decon2type <$> args') conOnly

              --   ct `uni` syntheticConType
              --   pure (T.CaseConstructor conOnly uc args')
              _ -> undefined


      R.Return (ret, t) -> do
        emret <- RWS.asks returnType

        let opty = maybe (findBuiltinType tlReturnFind) pure  -- NOTE: When default return type is nothing, this means that we are parsing prelude. Return type from top level should be "Int" (or, in the future, U8).
        eret <- opty emret
        t `uni` eret
        pure $ T.Return ret


      R.Print (expr, _) ->
        pure $ T.Print expr


      R.Pass ->
        pure T.Pass


      R.ExprStmt (expr, _) ->
        pure $ T.ExprStmt expr


      R.EnvDef rfn -> do
        fn <- inferFunction rfn
        pure $ T.EnvDef fn



inferExpr :: R.Expr -> Infer T.Expr
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType :: Base R.Expr (Infer T.Expr) -> Infer (Base T.Expr T.Expr)
    inferExprType e = do
      (e', t) <- inferLayer
      pure $ T.TypedExpr t e' where

      inferLayer = case e of

        (R.Lam _ env args body) -> do

          -- add types to lambda parameters
          argts <- traverse var args
          let args' = zip args argts

          -- eval body
          (fenv, body') <- withEnv env body

          union <- singleEnvUnion fenv
          let ret = T.getType body'
          let t = Fix $ T.TFun union argts ret

          pure (T.Lam fenv args' body', t)


        R.As ae t -> do
          e' <- ae
          t' <- inferType t

          T.getType e' `uni` t'

          pure (T.As e' t', t')


        R.Lit lt -> do
          t <- case lt of
            LInt _  -> findBuiltinType intFind
            LFloat _ -> findBuiltinType floatFind
          pure (T.Lit lt, t)


        R.Var loc v -> do
          v' <- inferVariable v
          t <- instantiateVariable v'

          when (loc == FromEnvironment) $ do
            addEnv v' t

          pure (T.Var loc v', t)


        R.Con c -> do
          c' <- inferConstructor c

          emptyEnv <- newEnvID  -- NOTE: for `newEnvID`, see note in AST.Typed near this constructor.
          t <- instantiateConstructor emptyEnv c'
          pure (T.Con emptyEnv c', t)


        R.Op il op ir -> do
          l <- il
          r <- ir

          let lt = T.getType l
              rt = T.getType r

          t <- if op == NotEquals || op == Equals
            then do
              lt `uni` rt
              findBuiltinType boolFind

            else do
              intt <- findBuiltinType intFind
              lt `uni` intt
              rt `uni` intt
              pure intt

          pure (T.Op l op r, t)


        R.Call callee args -> do
          args' <- sequenceA args
          let argts = T.getType <$> args'
          callee' <- callee

          ret <- fresh
          union <- emptyUnion
          let ft = Fix $ T.TFun union argts ret

          T.getType callee' `uni` ft

          pure (T.Call callee' args', ret)



inferVariable :: R.Variable -> Infer T.Variable
inferVariable = \case
  R.DefinedVariable v -> pure $ T.DefinedVariable v
  R.ExternalFunction fn -> pure $ T.DefinedFunction fn
  R.DefinedFunction fn -> T.DefinedFunction <$> inferFunction fn

inferConstructor :: R.Constructor -> Infer T.DataCon
inferConstructor = \case
  R.ExternalConstructor c -> pure c
  R.DefinedConstructor (R.DC rdd uc _ _) -> do
    (T.DD _ _ cons _) <- inferDataDef rdd

    -- HACK?: Find constructor through memoized DataDefinition.
    pure $ mustOr (printf "[Compiler Error] Could not find constructor %s." (ctx ppCon uc)) $
      find (\(T.DC _ uc' _ _) -> uc == uc') cons


inferType :: R.Type -> Infer T.Type
inferType = cata $ (.) (fmap embed) $ \case
  R.TCon (R.DefinedDatatype rdd) rparams -> do
    dd <- inferDataDef rdd
    params <- sequenceA rparams
    let unions = extractUnionsFromDataType dd  -- TODO: shouldn't this be cloned???
    pure $ T.TCon dd params unions

  R.TCon (R.ExternalDatatype dd) rparams -> do
    params <- sequenceA rparams
    let unions = extractUnionsFromDataType dd  -- TODO: same here...
    pure $ T.TCon dd params unions

  R.TVar tv -> pure $ T.TVar tv

  R.TFun rargs rret -> liftA3 T.TFun emptyUnion (sequenceA rargs) rret



inferDataDef :: R.DataDef -> Infer T.DataDef
inferDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $
  \(R.DD ut tvars rdcs anns) addMemo -> mdo
    let dd = T.DD ut (Scheme tvars unions) dcs anns  -- NOTE: TVar correctness (no duplication, etc.) should be checked in Resolver!

    addMemo dd

    dcs <- for rdcs $ \(R.DC _ uc rts dcAnn)-> do
      ts <- traverse inferType rts
      let dc = T.DC dd uc ts dcAnn
      pure dc

    let unions = concatMap extractUnionsFromConstructor dcs
    pure dd



inferFunction :: R.Function -> Infer T.Function
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration

    params <- for rfundec.functionParameters $ \(v, definedType) -> do
      vt <- var v
      case definedType of
        Just rt -> do
          t <- inferType rt

          vt `uni` t

        Nothing -> pure ()
      pure (v, vt)

    ret <- maybe fresh inferType rfundec.functionReturnType


    -- Set up temporary recursive env (if this function is recursive, this env will be used).
    envID <- newEnvID  -- NOTE: this envID later becomes the ID of this function.
    let recenv = T.RecursiveEnv envID (null $ R.fromEnv rfundec.functionEnv)
    let noGeneralizationScheme = Scheme mempty mempty
    let fundec = T.FD recenv rfundec.functionId params ret noGeneralizationScheme
    let fun = T.Function { T.functionDeclaration = fundec, T.functionBody = body }

    -- Add *ungeneralized* type.
    addMemo fun

    -- Infer body.
    (envc, body) <- withEnv' rfundec.functionEnv $ withReturn ret $ inferStmts rfn.functionBody

    -- now, replace it with a non-recursive environment.
    let env = T.Env envID envc
    let fundec' = fundec { T.functionEnv = env }
    let fun' = fun { T.functionDeclaration = fundec' }

    pure fun'

  -- Add *generalized* version.
  addMemo fn

  pure fn


-- Exports: what the current module will export.
inferExports :: R.Exports -> Infer T.Exports
inferExports e = do
  dts <- traverse inferDataDef e.datatypes
  fns <- traverse inferFunction e.functions
  pure $ T.Exports
    { variables = e.variables
    , functions = fns
    , datatypes = dts
    }


-- Generalizes the function inside.
generalize :: Infer T.Function -> Infer T.Function
generalize ifn = do
  unsuFn <- ifn

  ctxPrint' "Unsubstituted function:"
  ctxPrint T.tFunction unsuFn

  -- liftIO $ putStrLn $ ctx T.tFunction unsuFn
  csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  let fn = subst csu unsuFn
  let (su, scheme) = constructSchemeForFunctionDeclaration fn.functionDeclaration

  ctxPrint' $ printf "Scheme: %s" (T.tScheme scheme)
  let generalizedFn = subst su fn
  let generalizedFnWithScheme = generalizedFn { T.functionDeclaration = generalizedFn.functionDeclaration { T.functionScheme = scheme } }

  -- Also, remember the substitution! (tvars might escape the environment)
  --  TODO: not sure if that's the best way. maybe instead of doing this, just add it in the beginning and resubstitute the function.
  substituting $ do
    let (Subst _ tvars) = su
    for_ (Map.toList tvars) $ uncurry bind

  pure generalizedFnWithScheme


-- Constructs a scheme for a function.
-- ignores assigned scheme!
constructSchemeForFunctionDeclaration :: T.FunDec -> (Subst, Scheme)
constructSchemeForFunctionDeclaration dec =
  let digOutTyVarsAndUnionsFromType :: T.Type -> (Set TyVar, Set T.EnvUnion)
      digOutTyVarsAndUnionsFromType = para $ \case
        T.TyVar tyv -> (Set.singleton tyv, mempty)
        T.TFun union ts t -> (mempty, Set.singleton (fst <$> union)) <> foldMap snd ts <> snd t
        T.TCon _ ts unis -> foldMap snd ts <> foldMap ((mempty,) . Set.singleton . fmap fst) unis
        t -> foldMap snd t

      -- IMPORTANT! We only extract types from non-instantiated! The instantiated type might/will contain types from our function and we don't won't that. We only want to know which types are from outside.
      -- So, for a function, use its own type.
      -- For a variable, use the actual type as nothing is instantiated!
      digOutTyVarsAndUnionsFromEnv :: T.Env -> (Set TyVar, Set T.EnvUnion)
      digOutTyVarsAndUnionsFromEnv (T.RecursiveEnv _ _) = mempty
      digOutTyVarsAndUnionsFromEnv (T.Env _ env) = foldMap (\(v, _ ,t) -> digThroughVar t v) env
        where
          digThroughVar :: T.Type -> T.Variable -> (Set TyVar, Set T.EnvUnion)
          digThroughVar t = \case
            T.DefinedVariable _ -> digOutTyVarsAndUnionsFromType t
            T.DefinedFunction f -> foldMap (digOutTyVarsAndUnionsFromType . snd) f.functionDeclaration.functionParameters <> digOutTyVarsAndUnionsFromType f.functionDeclaration.functionReturnType

      (tyVarsOutside, unionsOutside) = digOutTyVarsAndUnionsFromEnv dec.functionEnv
      (tyVarsDeclaration, unionsDeclaration) = foldMap (digOutTyVarsAndUnionsFromType . snd) dec.functionParameters <> digOutTyVarsAndUnionsFromType dec.functionReturnType

      -- TypesDefinedHere = FnType \\ Environment
      tyVarsOnlyFromHere = tyVarsDeclaration \\ tyVarsOutside
      unionsOnlyFromHere = unionsDeclaration \\ unionsOutside

      -- goes trhough the type and finds tvars that are defined for this function.
      definedTVars :: T.Type -> Set TVar
      definedTVars = cata $ \case
        T.TVar tv@(TV _ (BindByVar varid)) | varid == dec.functionId -> Set.singleton tv
        t -> fold t

      tvarsDefinedForThisFunction = foldMap (definedTVars . snd) dec.functionParameters <> definedTVars dec.functionReturnType

      -- Then substitute it.
      asTVar (T.TyV tyname) = TV tyname (BindByVar dec.functionId)

      su = Subst mempty $ Map.fromSet (Fix . T.TVar . asTVar) tyVarsOnlyFromHere
      unionsOnlyFromHereWithTVars = Set.map (subst su) unionsOnlyFromHere  -- NOTE: Unions might also contain our TyVars, so we must substitute it also.

      tvarsFromTyVars = Set.map asTVar tyVarsOnlyFromHere
      scheme = Scheme (Set.toList $ tvarsFromTyVars <> tvarsDefinedForThisFunction) (Set.toList unionsOnlyFromHereWithTVars)
  in (su, scheme)

-- Substitute return type for function.
withReturn :: T.Type -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }




------
-- Instantiation
------

instantiateVariable :: T.Variable -> Infer T.Type
instantiateVariable = \case
  T.DefinedVariable v -> var v
  T.DefinedFunction fn -> do
    let fundec = fn.functionDeclaration
    let (Scheme schemeTVars schemeUnions) = fundec.functionScheme

    (tvs, unions) <- instantiateScheme fundec.functionScheme

    -- Prepare a mapping for the scheme!
    let tvmap = Map.fromList $ zip schemeTVars tvs
    let unionmap = Map.fromList $ zip (T.unionID <$> schemeUnions) unions
    let mapTVs = mapTVsWithMap tvmap unionmap

    ctxPrint' $ printf "Instantiation of %s" (show fundec.functionId.varName)
    ctxPrint (Common.ppMap . fmap (bimap Common.ppTVar T.tType) . Map.toList) tvmap
    ctxPrint (Common.ppMap . fmap (bimap Common.ppUnionID (T.tEnvUnion . fmap T.tType)) . Map.toList) unionmap


    -- Create type from function declaration
    fnUnion <- singleEnvUnion (mapTVs <$> fundec.functionEnv)
    let fnType = Fix $ T.TFun fnUnion (mapTVs . snd <$> fundec.functionParameters) (mapTVs fundec.functionReturnType)

    ctxPrint' $ printf "After instantiation: %s" (T.tType fnType)

    pure fnType

instantiateConstructor :: EnvID -> T.DataCon -> Infer T.Type
instantiateConstructor envID = \case
  T.DC dd@(T.DD _ scheme _ _) _ [] _ -> do
    (tvs, unions) <- instantiateScheme scheme
    pure $ Fix $ T.TCon dd tvs unions

  (T.DC dd@(T.DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts@(_:_) _) -> do
    (tvs, unions) <- instantiateScheme scheme
    let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
    let ts = mapTVs <$> usts

    let ret = Fix $ T.TCon dd tvs unions

    -- don't forget the empty env!
    let emptyEnv = T.Env envID []
    union <- singleEnvUnion emptyEnv

    pure $ Fix $ T.TFun union ts ret


instantiateScheme :: Scheme -> Infer ([T.Type], [T.EnvUnion])
instantiateScheme (Scheme schemeTVars schemeUnions) = do
  -- Prepare a mapping for the scheme!
  tvs <- traverse (const fresh) schemeTVars  -- scheme
  let tvmap = Map.fromList $ zip schemeTVars tvs

  -- Unions themselves also need to be mapped with the instantiated tvars!
  let mapOnlyTVsForUnions = mapTVsWithMap tvmap mempty
  unions <-traverse (\union -> cloneUnion (mapOnlyTVsForUnions <$> union)) schemeUnions

  pure (tvs, unions)


mapTVsWithMap :: Map TVar T.Type -> Map UnionID T.EnvUnion -> T.Type -> T.Type
mapTVsWithMap tvmap unionmap =
  let
    mapTVs :: T.Type -> T.Type
    mapTVs = cata $ (.) embed $ \case
      t@(T.TVar tv) -> maybe t project (tvmap !? tv)
      T.TFun union ts tret -> T.TFun (fromMaybe union (unionmap !? union.unionID)) ts tret
      T.TCon dd ts unions -> T.TCon dd ts $ unions <&> \union -> fromMaybe union (unionmap !? union.unionID)
      t -> t
  in mapTVs


-- Creates a new env alongside inferring an environment (TODO: why?)
withEnv :: R.Env -> Infer a -> Infer (T.Env, a)
withEnv renv x = do
  (tenv, x') <- withEnv' renv x
  envID <- newEnvID
  pure (T.Env envID tenv, x')


-- Constructs an environment from all the instantiations.
--  We need the instantiations, because not all instantiations of a function can come up in the environment.
--  But, when there is a TVar in the type, it means all instantiated types of TVars must be there.
withEnv' :: R.Env -> Infer a -> Infer ([(T.Variable, Locality, T.Type)], a)
withEnv' renv x = do

  -- 1. clear environment - we only collect things from this scope.
  outOfEnvInstantiations <- RWS.gets instantiations

  -- 2. execute in scope.
  RWS.modify $ \s -> s { instantiations = Set.empty }
  x' <- x
  modifiedInstantiations <- RWS.gets instantiations

  -- 3. then filter the stuff that actually is from the environment
  --  TODO: this might not be needed, since we conditionally add an instantiation if it's FromEnvironment.
  renvQuery <- Map.fromList <$> traverse (\(v, t) -> (,t) <$> inferVariable v) (R.fromEnv renv)
  let newEnv = mapMaybe (\(v, t) -> Map.lookup v renvQuery <&> (v,,t)) $ Set.toList modifiedInstantiations


  -- 4. and put that filtered stuff back.
  let usedInstantiations = Set.fromList $ fmap (\(v, _, t) -> (v, t)) newEnv
  RWS.modify $ \s -> s { instantiations = outOfEnvInstantiations <> usedInstantiations }

  pure (newEnv, x')


addEnv :: T.Variable -> T.Type -> Infer ()
addEnv v t = RWS.modify $ \s -> s { instantiations = Set.insert (v, t) s.instantiations }


-- maybe merge lookupVar and newVar,
--   because that's what the resolving step should... resolve.
var :: UniqueVar -> Infer T.Type
var v = do
  vars <- RWS.gets variables
  case vars !? v of
    Just t -> pure t
    Nothing -> do
      t <- fresh
      RWS.modify $ \s -> s { variables = Map.insert v t s.variables }
      pure t


findBuiltinType :: PreludeFind -> Infer T.Type
findBuiltinType (PF tc pf) = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> pure $ pf p
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap tc (\(R.DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(T.DD _ scheme _ _) -> do
          (tvs, unions) <- instantiateScheme scheme
          pure $ Fix $ T.TCon dd tvs unions
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."




-------------------------------
--        UNIFICATION

uni :: T.Type -> T.Type -> Infer ()
uni t1 t2 = do
  substituting $ do
    su <- RWS.get
    let (t1', t2') = subst su (t1, t2)
    unify t1' t2'

substituting :: SubstCtx a -> Infer a
substituting subctx = RWST $ \_ s -> do
  (x, su, errs) <- RWS.runRWST subctx () s.typeSubstitution
  pure (x, s { typeSubstitution = su }, errs)


------

unify :: T.Type -> T.Type -> SubstCtx ()
unify ttl ttr = do
  su <- RWS.get
  let (tl, tr) = subst su (ttl, ttr)
  case bimap project project $ subst su (tl, tr) of
    (l, r) | l == r -> pure ()
    (T.TyVar tyv, _) -> tyv `bind` tr
    (_, T.TyVar tyv) -> tyv `bind` tl
    (T.TFun lenv lps lr, T.TFun renv rps rr) -> do
      unifyMany lps rps
      unify lr rr
      lenv `unifyFunEnv` renv

    (T.TCon t ta unions, T.TCon t' ta' unions') | t == t' -> do
      unifyMany ta ta'
      zipWithM_ unifyFunEnv unions unions'

    (_, _) -> do
      err $ TypeMismatch tl tr

unifyMany :: [T.Type] -> [T.Type] -> SubstCtx ()
unifyMany [] [] = nun
unifyMany (tl:ls) (tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
  unify tl tr
  unifyMany ls rs

unifyMany tl tr = err $ MismatchingNumberOfParameters tl tr

bind :: TyVar -> T.Type -> SubstCtx ()
bind tyv (Fix (T.TyVar tyv')) | tyv == tyv' = nun
bind tyv t | occursCheck tyv t =
              err $ InfiniteType tyv t
           | otherwise = do
  RWS.modify $ \su ->
    let singleSubst  = Subst mempty (Map.singleton tyv t)
        Subst unions types = subst singleSubst su
    in Subst unions (Map.insert tyv t types)

unifyFunEnv :: T.EnvUnion -> T.EnvUnion -> SubstCtx ()
unifyFunEnv lenv@(T.EnvUnion { T.unionID = lid }) renv@(T.EnvUnion { T.unionID = rid }) = do
  unionID <- newUnionID
  let env = T.EnvUnion { T.unionID = unionID, T.union = funEnv }

  RWS.modify $ \su ->
    let unionSubst = Subst (Map.fromList [(lid, env), (rid, env)]) Map.empty -- i don't think we need an occurs check. BUG: we actually do, nigga.
        Subst unions ts = subst unionSubst su  -- NOTE: technically, we don't even need to add this mapping to our global Subst, but then we would have to create a new fresh variable every time a new variable is created, or something similar (more error prone, so maybe not worth it.).
    in Subst (Map.insert rid env $ Map.insert lid env unions) ts
  --       traceShow ("ENVUNI: " <> show lenv <> "|||||" <> show renv <> "8=====>" <> show env <> "\n") $ 
  where
    union2envset = Set.fromList . (\(T.EnvUnion { T.union = union }) -> union)
    envset2union = Set.toList
    funEnv = envset2union $ union2envset lenv <> union2envset renv

occursCheck :: Substitutable a => TyVar -> a -> Bool
occursCheck tyv t = tyv `Set.member` ftv t

err :: TypeError -> SubstCtx ()
err te = RWS.tell [te]

-- Sikanokonokonokokośtantan
nun :: SubstCtx ()
nun = pure ()




-------------------
-- Substitutable --
-------------------

class Substitutable a where
  ftv :: a -> Set TyVar
  subst :: Subst -> a -> a


instance Substitutable Subst where
  ftv (Subst unions types) = ftv (Map.elems unions) <> Map.keysSet types <> ftv (Map.elems types)
  subst su (Subst unions types) = Subst (Map.map (subst su) unions) (Map.map (subst su) types)

instance Substitutable T.Module  where
  -- TODO: We're not yet ftv-ing Datatypes, because it might lead to loops. Same with functions. I'll probably need another memoization system.
  ftv m = ftv m.toplevelStatements <> ftv m.functions -- <> ftv m.datatypes
  subst su m = T.Mod
    { T.toplevelStatements = subst su <$> m.toplevelStatements
    , T.exports = subst su m.exports

    , T.functions = subst su <$> m.functions
    , T.datatypes = m.datatypes -- subst su <$> m.datatypes
    }

instance Substitutable T.Exports where
  ftv e = ftv e.functions
  subst su e = e { T.functions = subst su e.functions }

instance Substitutable T.AnnStmt where
  ftv = cata $ \(O (Annotated _ stmt)) -> bifold $ first ftv stmt

  subst su = cata $ embed . sub
    where
      sub (O (Annotated ann stmt)) = O . Annotated ann $ case stmt of
        T.Switch cond cases ->
          let cond' = subst su cond
              cases' = subst su cases
          in T.Switch cond' cases'
        T.EnvDef env -> T.EnvDef $ subst su env
        s -> first (subst su) s

instance (Substitutable expr, Substitutable stmt) => Substitutable (T.Case expr stmt) where
  ftv kase = ftv kase.deconstruction <> ftv kase.caseCondition <> ftv kase.body
  subst su kase = T.Case (subst su kase.deconstruction) (subst su kase.caseCondition) (subst su kase.body)

instance Substitutable (Fix T.DeconF) where
  ftv = cata $ \case
    T.CaseVariable t _ -> ftv t
    T.CaseConstructor t _ ftvs -> ftv t <> mconcat ftvs
  subst su = hoist $ \case
    T.CaseVariable t v -> T.CaseVariable (subst su t) v
    T.CaseConstructor t uc ds -> T.CaseConstructor (subst su t) uc ds

instance Substitutable (Fix T.TypedExpr) where
  ftv = cata $ \(T.TypedExpr et ee) -> ftv et <> case ee of
    T.As e t -> e <> ftv t
    T.Lam env params body -> ftv env <> ftv params <> body
    e -> fold e
  subst su = hoist $ \(T.TypedExpr et ee) -> T.TypedExpr (subst su et) (case ee of
    T.As e t -> T.As e (subst su t)
    T.Lam env params body -> T.Lam (subst su env) (subst su params) body
    T.Var loc v -> T.Var loc $ subst su v
    e -> e)

instance Substitutable T.Variable where
  ftv _ = mempty
  subst su (T.DefinedFunction fn) = T.DefinedFunction $ subst su fn
  subst _ x = x


instance Substitutable UniqueVar where
  ftv _ = mempty
  subst _ = id



instance Substitutable T.Function where
  ftv fn = ftv fn.functionBody \\ ftv fn.functionDeclaration
  subst su fn = T.Function { T.functionDeclaration = subst su fn.functionDeclaration, T.functionBody = subst su fn.functionBody }

instance Substitutable T.FunDec where
  ftv (T.FD _ _ params ret _) = ftv params <> ftv ret -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 
  subst su (T.FD env fid params ret scheme) = T.FD (subst su env) fid (subst su params) (subst su ret) scheme


instance Substitutable (Fix T.TypeF) where
  ftv = cata $ \case
    T.TyVar tyv -> Set.singleton tyv
    t -> fold t

  subst su@(Subst _ tyvm) = cata $ embed . \case
    T.TyVar tyv -> case tyvm !? tyv of
        Nothing -> T.TyVar tyv
        Just t -> project t

    -- we might need to substitute the union thing
    T.TFun ogUnion ts t ->

      -- might need to replace the union
      let union = subst su ogUnion

      in T.TFun union ts t

    T.TCon ut cons unions -> T.TCon ut cons (subst su unions)

    t -> t

instance Substitutable (T.EnvUnionF (Fix T.TypeF)) where
  ftv (T.EnvUnion _ envs) = ftv envs
  subst su@(Subst unions _) (T.EnvUnion uid envs) = do
    case unions !? uid of
      Just suUnion -> suUnion
      Nothing -> T.EnvUnion uid $ subst su envs

instance Substitutable (T.EnvF (Fix T.TypeF)) where
  ftv (T.Env _ vars) = foldMap (\(_, _, t) -> ftv t) vars
  ftv (T.RecursiveEnv _ _) = mempty

  -- redundant work. memoize this shit also.
  subst su (T.Env eid env) = T.Env eid ((\(v, l, t) -> (subst su v, l, subst su t)) <$> env)
  subst su env = fmap (subst su) env


instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance Substitutable a => Substitutable (NonEmpty a) where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv
  subst su = bimap (subst su) (subst su)

instance Substitutable a => Substitutable (Maybe a) where
  ftv = maybe mempty ftv
  subst su = fmap (subst su)




-----------------
----- Smol

-- Make a new env ID.
newEnvID :: Infer EnvID
newEnvID = EnvID <$> liftIO newUnique

-- Make new union ID.
newUnionID :: MonadIO io => io UnionID
newUnionID = UnionID <$> liftIO newUnique


-- Returns a fresh new tyvare
fresh :: Infer T.Type
fresh = Fix . T.TyVar <$> freshTyvar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyvar :: Infer TyVar
freshTyvar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV (letters !! nextVar)

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']


singleEnvUnion :: T.Env -> Infer T.EnvUnion
singleEnvUnion env = do
  uid <- newUnionID
  pure T.EnvUnion { T.unionID = uid, T.union = [env] }

cloneUnion :: T.EnvUnionF a -> Infer (T.EnvUnionF a)
cloneUnion union = do
  uid <- newUnionID
  pure $ union { T.unionID = uid }

-- Creates an empty union.
emptyUnion :: Infer T.EnvUnion
emptyUnion = do
  uid <- newUnionID
  pure $ T.EnvUnion uid []


findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList




------------------------------------------
--          DATATYPES n shiiii
------------------------------------------

-- TODO: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer = RWST Context [TypeError] TypecheckingState IO  -- normal inference
type SubstCtx = RWST () [TypeError] Subst IO     -- substitution

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe T.Type
  }



data TypecheckingState = TypecheckingState
  { tvargen :: TVarGen

  -- current state of substitution.
  , typeSubstitution :: Subst

  , memoFunction :: Memo R.Function T.Function
  , memoDataDefinition :: Memo R.DataDef T.DataDef

  , variables :: Map UniqueVar T.Type

  -- HACK?: track instantiations from environments. 
  --  (two different function instantiations will count as two different "variables")
  , instantiations :: Set (T.Variable, T.Type)
  }

emptySEnv :: TypecheckingState
emptySEnv = TypecheckingState
  { tvargen = newTVarGen
  , typeSubstitution = emptySubst

  , memoFunction = Memo mempty
  , memoDataDefinition = Memo mempty

  , variables = mempty

  , instantiations = mempty
  }



newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst = Subst (Map UnionID T.EnvUnion) (Map TyVar T.Type)

emptySubst :: Subst
emptySubst = Subst mempty mempty



data TypeError
  = InfiniteType TyVar T.Type
  | TypeMismatch T.Type T.Type
  | MismatchingNumberOfParameters [T.Type] [T.Type]
  | AmbiguousType TyVar

-- not sure if we have to have a show instance
instance Show TypeError where
  show = \case
    InfiniteType tyv t -> unwords ["InfiniteType", ctx T.tTyVar tyv, ctx T.tType t]
    TypeMismatch t t' -> printf "Type Mismatch: %s %s" (ctx T.tType t) (ctx T.tType t')
    MismatchingNumberOfParameters ts ts' -> printf "Mismatching number of parameters: (%d) %s (%d) %s" (length ts) (show $ ctx T.tType <$> ts) (length ts') (show $ ctx T.tType <$> ts')
    AmbiguousType tyv -> printf "Ambiguous type: %s" (ctx T.tTyVar tyv)




-----
-- DEBUG
----

dbgSubst :: Subst -> String
dbgSubst (Subst unions ts) =
  let tvars = Map.toList ts <&> \(ty, t) -> printf "%s => %s" (ctx T.tTyVar ty) (ctx T.tType t)
      unionRels = Map.toList unions <&> \(uid, union) -> printf "%s => %s" (ctx ppUnionID uid) (ctx (T.tEnvUnion . fmap T.tType) union)
  in unlines $ tvars <> ["--"] <> unionRels
