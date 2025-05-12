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
import Control.Monad (replicateM, zipWithM_, when, unless)
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
import AST.Common (LitType (..), UniqueVar, UniqueType (typeName), Annotated (Annotated), Op (..), EnvID (..), UnionID (..), ctx, type (:.) (..), ppCon, Locality (..), ppUnionID, phase, ctxPrint, ctxPrint', Binding (..), mustOr, sctx, ppList, eitherToMaybe, MemName, sequenceA2, ppVar, ppUniqueClass, fmap2, UniqueClassInstantiation (..))
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe)
import AST.Typed (TyVar, Scheme (..), extractUnionsFromDataType, extractUnionsFromConstructor, extractUnionsFromRecord, defaultEmpty)
import Text.Printf (printf)
import Control.Applicative (liftA3)
import Data.List.NonEmpty (NonEmpty)
import Misc.Memo (memo, Memo(..), emptyMemo)
import qualified AST.Common as Common
import qualified Data.IORef as IORef
import Data.IORef (IORef)
import GHC.IO (unsafePerformIO)
import Data.String (fromString)



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
      -- Typecheck *all* functions, datatypes, etc. We want to typecheck a function even if it's not used (unlike Zig! (soig))
      dds <- inferDatatypes rModule.datatypes
      fns <- inferFunctions rModule.functions
      tls <- inferTopLevel rModule.toplevel
      classes <- inferClasses rModule.classes
      instances <- inferInstances rModule.instances
      exs <- inferExports rModule.exports

      -- run it one last time.
      cia <- substAccessAndAssociations
      reportAssociationErrors
      -- addSelectedEnvironmentsFromInst

      pure $ T.Mod
        { T.toplevelStatements = tls
        , T.exports = exs
        , T.classInstantiationAssociations = cia
        , T.functions = fns
        , T.datatypes = dds
        , T.classes = classes
        , T.instances = instances
        }

    inferFunctions fns = for fns inferFunction
    inferDatatypes dds = for dds inferDataDef
    inferClasses cls = for cls inferClassDef
    inferInstances insts = for insts inferInstance
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

        -- be sure to copy the environment HERE!
        let varsFromNestedFun = case fn.functionDeclaration.functionEnv of
              T.Env _ env -> Set.fromList $ env <&> \(v, _, t) -> (v, t)
              _ -> error "FUKKK"

        RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

        pure $ T.EnvDef fn

      R.InstDefDef rinst -> do
        inst <- inferInstance rinst

        -- be sure to copy the environment HERE!
        let varsFromNestedFun = fold $ inst.instFunctions <&> \fn -> case fn.instFunction.functionDeclaration.functionEnv of
              T.Env _ env -> Set.fromList $ env <&> \(v, _, t) -> (v, t)
              _ -> error "FUKKK"

        RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

        pure $ T.InstDefDef inst



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

          -- be sure to copy the environment HERE!
          let varsFromNestedFun = case fenv of
                T.Env _ env -> Set.fromList $ env <&> \(v, _, t) -> (v, t)
                _ -> error "FUKKK"

          RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

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
          (t, v') <- instantiateVariable =<< inferVariable v

          when (loc == FromEnvironment) $ do
            addEnv v' t

          pure (T.Var loc v', t)


        R.Con c -> do
          c' <- inferConstructor c

          emptyEnv <- newEnvID  -- NOTE: for `newEnvID`, see note in AST.Typed near this constructor.
          t <- instantiateConstructor emptyEnv c'
          pure (T.Con emptyEnv c', t)

        R.RecCon dd insts -> do
          -- currently, all the redefinitions are reported in Resolver.
          -- this might not be the case when implementing ISSUE(anonymous-structs)

          dd' <- inferDatatype dd
          insts' <- sequenceA2 insts
          t <- instantiateRecord dd'

          for_ insts' $ \(name, me) -> do
            mt <- addMember t name
            uni mt (T.getType me)

          pure (T.RecCon dd' insts', t)


        R.RecUpdate re updates -> do
          te <- re
          updates' <- sequenceA2 updates

          -- the type can be whatever, so we couldn't check these fields in the resolver ISSUE(anonymous-records)
          for_ updates' $ \(mem, me) -> do
            memt <- addMember (T.getType te) mem
            uni memt (T.getType me)

          pure (T.RecUpdate te updates', T.getType te)

        R.MemAccess re memname -> do
          te <- re

          -- by now, we don't know the type of the member, because it's possible to define multiple members with the same name.
          t <- addMember (T.getType te) memname

          pure (T.MemAccess te memname, t)

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

  R.ExternalFunction fn rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    pure $ T.DefinedFunction fn snapshot mempty

  R.DefinedFunction fn rsnapshot -> T.DefinedFunction <$> inferFunction fn <*> inferSnapshot rsnapshot <*> pure mempty

  R.ExternalClassFunction cfd@(T.CFD cd _ _ _) rsnapshot -> do
    -- insts <- fmap Map.fromList $ for (Map.toList (rinsts ! )) $ \(rdd, rinst) -> do
    --   dd <- inferDatatype rdd
    --   inst <- case rinst of
    --     R.DefinedInst rists  -> inferInstance rists
    --     R.ExternalInst tinst -> pure tinst
    --   pure (dd, inst)
    snapshot <- inferSnapshot rsnapshot
    let insts = defaultEmpty cd snapshot

    self <- fresh
    self `constrain` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self undefined

  R.DefinedClassFunction rcfd rsnapshot -> do
    cfd@(T.CFD cd _ _ _) <- inferClassDeclaration rcfd
    -- insts <- fmap Map.fromList $ traverse (bitraverse inferDatatype inferInstance) $ Map.toList rinsts
    snapshot <- inferSnapshot rsnapshot
    let insts = defaultEmpty cd snapshot

    self <- fresh
    self `constrain` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self undefined

inferSnapshot :: R.ScopeSnapshot -> Infer T.ScopeSnapshot
inferSnapshot = Common.bitraverseMap inferClass inferPossibleInstances
  where
    inferPossibleInstances :: R.PossibleInstances -> Infer T.PossibleInstances
    inferPossibleInstances = Common.bitraverseMap inferDatatype inferInst

inferVariableProto :: R.VariableProto -> Infer T.VariableProto
inferVariableProto = \case
  R.PDefinedVariable v -> pure $ T.PDefinedVariable v

  R.PExternalFunction fn -> pure $ T.PDefinedFunction fn
  R.PDefinedFunction fn -> T.PDefinedFunction <$> inferFunction fn

  R.PExternalClassFunction cfd -> pure $ T.PDefinedClassFunction cfd
  R.PDefinedClassFunction  cfd -> do
    T.PDefinedClassFunction <$> inferClassDeclaration cfd


inferConstructor :: R.Constructor -> Infer T.DataCon
inferConstructor = \case
  R.ExternalConstructor c -> pure c
  R.DefinedConstructor (R.DC rdd uc _ _) -> do
    (T.DD _ _ cons _) <- inferDataDef rdd

    -- HACK?: Find constructor through memoized DataDefinition.
    pure $ mustOr (printf "[Compiler Error] Could not find constructor %s." (ctx ppCon uc)) $
      find (\(T.DC _ uc' _ _) -> uc == uc') =<< eitherToMaybe cons


-- pointless remap for class type
-- we keep the original structure to later check if the inst function matches the lass declaration
inferClassType :: R.ClassType -> Infer T.ClassType
inferClassType = cata $ (.) (fmap embed) $ \case
  R.Self -> pure T.Self
  R.NormalType nt -> case nt of
    R.TCon (R.DefinedDatatype rdd) rparams -> do
      dd <- inferDataDef rdd
      params <- sequenceA rparams
      pure $ T.CTCon dd params
    R.TCon (R.ExternalDatatype dd) rparams -> do
      params <- sequenceA rparams
      pure $ T.CTCon dd params
    R.TVar rtv -> do
      tv <- inferTVar rtv
      pure $ T.CTVar tv
    R.TFun params ret -> do
      fnUnion <- emptyUnion
      T.CTFun fnUnion.unionID <$> sequenceA params <*> ret

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

  R.TVar tv -> T.TVar <$> inferTVar tv

  R.TFun rargs rret -> liftA3 T.TFun emptyUnion (sequenceA rargs) rret

inferTVar :: R.TVar -> Infer T.TVar
inferTVar rtv = do
  classes <- Common.traverseSet inferClass rtv.tvClasses
  pure $ T.TV
    { fromTV = rtv.fromTV
    , binding = rtv.binding
    , tvConstraints = classes
    }

mkTypeFromClassType :: T.Type -> T.ClassType -> T.Type
mkTypeFromClassType self = cata $ fmap embed $ \case
  T.Self -> project self
  T.CTCon dd params -> T.TCon dd params (extractUnionsFromDataType dd)
  T.CTVar tv -> T.TVar tv
  T.CTFun emptyUnionID params ret -> T.TFun (T.EnvUnion { T.unionID = emptyUnionID, T.union = [] }) params ret



inferDatatype :: R.Datatype -> Infer T.DataDef
inferDatatype = \case
  R.ExternalDatatype tdd -> pure tdd
  R.DefinedDatatype rdd -> inferDataDef rdd

inferDataDef :: R.DataDef -> Infer T.DataDef
inferDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $
  \(R.DD ut rtvars erdcs anns) addMemo -> mdo
    tvars <- traverse inferTVar rtvars
    let dd = T.DD ut (Scheme tvars unions) edcs anns  -- NOTE: TVar correctness (no duplication, etc.) should be checked in Resolver!

    addMemo dd

    edcs <- case erdcs of
      Right rdcs -> fmap Right $ for rdcs $ \(R.DC _ uc rts dcAnn)-> do
        ts <- traverse inferType rts
        let dc = T.DC dd uc ts dcAnn
        pure dc

      Left rrecs -> fmap Left $ for rrecs $ \(R.DR _ memname rt recAnn) -> do
        t <- inferType rt
        pure $ T.DR dd memname t recAnn

    let unions = case edcs of
          Right dcs -> concatMap extractUnionsFromConstructor dcs
          Left drs -> concatMap extractUnionsFromRecord drs

    pure dd



inferFunction :: R.Function -> Infer T.Function
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration

    params <- for rfundec.functionParameters $ \(v, definedType) -> do
      tv <- inferDecon v
      let vt = T.decon2type tv

      case definedType of
        Just rt -> do
          t <- inferType rt

          vt `uni` t

        Nothing -> pure ()
      pure (tv, vt)

    ret <- maybe fresh inferType rfundec.functionReturnType


    -- Set up temporary recursive env (if this function is recursive, this env will be used).
    envID <- newEnvID  -- NOTE: this envID later becomes the ID of this function.
    let recenv = T.RecursiveEnv envID (null $ R.fromEnv rfundec.functionEnv)
    let noGeneralizationScheme = Scheme mempty mempty
    let fundec = T.FD recenv rfundec.functionId params ret noGeneralizationScheme [] mempty
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
  dts   <- traverse inferDataDef e.datatypes
  fns   <- traverse inferFunction e.functions
  cls   <- traverse inferClassDef e.classes
  insts <- traverse inferInstance e.instances
  pure $ T.Exports
    { variables = e.variables
    , functions = fns
    , datatypes = dts
    , classes   = cls
    , instances = insts
    }


inferClass :: R.Class -> Infer T.ClassDef
inferClass = \case
  R.DefinedClass cd -> inferClassDef cd
  R.ExternalClass cd -> pure cd

inferClassDef :: R.ClassDef -> Infer T.ClassDef
inferClassDef = memo memoClass (\mem s -> s { memoClass = mem }) $ \cd _ -> mdo
  let tcd = T.ClassDef
        { classID = cd.classID
        , classFunctions = funs
        }
  funs <- for cd.classFunctions $ \(R.CFD _ uv params ret)-> do
    params' <- for params $ \(decon, rt) -> do
      d <- inferDecon decon
      t  <- inferClassType rt

      let dt = T.decon2type d
      self <- fresh
      dt `uni` mkTypeFromClassType self t

      pure (d, t)

    ret' <- inferClassType ret
    pure $ T.CFD tcd uv params' ret'

  pure tcd

inferClassDeclaration :: R.ClassFunDec -> Infer T.ClassFunDec
inferClassDeclaration (R.CFD rcd uv _ _) = do
  tcd <- inferClassDef rcd
  let mcfd = find (\(T.CFD _ cuv _ _) -> cuv == uv) tcd.classFunctions
  pure $ mustOr (printf "[COMPILER ERROR]: Could not find function %s in class %s." (ppVar Local uv) (ppUniqueClass tcd.classID)) mcfd

inferInst :: R.Inst -> Infer T.InstDef
inferInst = \case
  R.ExternalInst inst -> pure inst
  R.DefinedInst inst -> inferInstance inst

inferInstance :: R.InstDef -> Infer T.InstDef
inferInstance = memo memoInstance (\mem s -> s { memoInstance = mem }) $ \inst _ -> mdo
  klass <- inferClass inst.instClass
  it <- inferDatatype $ fst inst.instType
  tvars <- traverse inferTVar $ snd inst.instType

  let instDef = T.InstDef
        { instClass = klass
        , instType = (it, tvars)
        , instFunctions = fns
        }

  fns <- for inst.instFunctions $ \rfn -> do
    -- TODO: add check?
    fn <- generalize $ mdo

      -- Infer function declaration.
      let rfundec = rfn.classFunctionDeclaration

      params <- for rfundec.functionParameters $ \(v, definedType) -> do
        tv <- inferDecon v
        let vt = T.decon2type tv

        case definedType of
          Just rt -> do
            t <- inferType rt

            vt `uni` t

          Nothing -> pure ()
        pure (tv, vt)

      ret <- maybe fresh inferType rfundec.functionReturnType


      -- Set up temporary recursive env (if this function is recursive, this env will be used).
      envID <- newEnvID  -- NOTE: this envID later becomes the ID of this function.
      let recenv = T.RecursiveEnv envID (null $ R.fromEnv rfundec.functionEnv)
      let noGeneralizationScheme = Scheme mempty mempty
      let fundec = T.FD recenv rfundec.functionId params ret noGeneralizationScheme [] mempty
      let fun = T.Function { T.functionDeclaration = fundec, T.functionBody = body }

      -- Infer body.
      (envc, body) <- withEnv' rfundec.functionEnv $ withReturn ret $ inferStmts rfn.classFunctionBody

      -- now, replace it with a non-recursive environment.
      let env = T.Env envID envc
      let fundec' = fundec { T.functionEnv = env }
      let fun' = fun { T.functionDeclaration = fundec' }
      pure fun'

    pure T.InstanceFunction
      { instFunction = fn
      , instFunctionClassUniqueVar = rfn.classFunctionPrototypeUniqueVar
      , instDef = instDef
      }

  pure instDef


-- Generalizes the function inside.
generalize :: Infer T.Function -> Infer T.Function
generalize ifn = do
  unsuFn <- ifn

  ctxPrint' "Unsubstituted function:"
  ctxPrint T.tFunction unsuFn


  -- First, finalize substitution by taking care of member access.
  -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
  --  At the end there will be one last member access.
  classInstantiationAssocs <- substAccessAndAssociations

  csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  let fn = subst csu unsuFn
  (su, scheme, assocs) <- constructSchemeForFunctionDeclaration fn.functionDeclaration

  ctxPrint' $ printf "Scheme: %s" (T.tScheme scheme)
  let generalizedFn = subst su fn


  let generalizedFnWithScheme = generalizedFn { T.functionDeclaration = generalizedFn.functionDeclaration { T.functionScheme = scheme, T.functionAssociations = assocs, T.functionClassInstantiationAssociations = classInstantiationAssocs } }

  -- Also, remember the substitution! (tvars might escape the environment)
  --  TODO: not sure if that's the best way. maybe instead of doing this, just add it in the beginning and resubstitute the function.
  substituting $ do
    let (Subst _ tvars) = su
    for_ (Map.toList tvars) $ uncurry bind

  pure generalizedFnWithScheme


substAccessAndAssociations :: Infer T.ClassInstantiationAssocs
substAccessAndAssociations = do
  liftIO $ phase "SUBST ACCESS"
  go where
    go = do
      didAccessProgressedSubstitutions <- substAccess
      classInstantiationAssocs <- substAssociations
      let didAssociationsProgressedSubstitutions = not $ null classInstantiationAssocs
      liftIO $ ctxPrint' $ printf "CIA: %s" (Common.ppMap $ fmap (bimap (fromString . show) (Common.encloseSepBy "[" "]" ", " . fmap (Common.ppTup . bimap T.tType (Common.ppTup . bimap (Common.encloseSepBy "[" "]" ", " . fmap T.tType) (\ifn -> Common.ppVar Local ifn.instFunction.functionDeclaration.functionId))))) $ Map.toList classInstantiationAssocs)

      if didAccessProgressedSubstitutions || didAssociationsProgressedSubstitutions
        then Map.unionWith (++) classInstantiationAssocs <$> go
        else do
          liftIO $ phase "END SUBST ACCESS"
          pure mempty


-- substitutes members n shiii (this is done in conjunction with associated types).
-- returns True if substitutions were done.
substAccess :: Infer Bool
substAccess = do
  membersAccessed <- RWS.gets memberAccess
  csu <- RWS.gets typeSubstitution
  let subMembers = subst csu membersAccessed
  substitutedMembers <- fmap filterDesignatedForRemoval $ for subMembers $ \(ogt, memname, t) -> do
    (mexpectedType, shouldRemove) <- getExpectedType ogt memname
    case mexpectedType of
      Nothing -> pure ()
      Just expectedType -> expectedType `uni` t
    pure ((ogt, memname, t), shouldRemove)

  RWS.modify $ \s -> s { memberAccess = substitutedMembers }
  pure (length substitutedMembers < length subMembers)


-- returns True if substitutions were done.
substAssociations :: Infer T.ClassInstantiationAssocs
substAssociations = do
  assocs <- RWS.gets associations
  RWS.modify $ \s -> s { associations = mempty }

  csu <- RWS.gets typeSubstitution
  let subAssociations = first (subst csu) <$> assocs
  liftIO $ ctxPrint' $ printf "Associations (before): %s" (Common.encloseSepBy "[" "]" ", " $ subAssociations <&> \(T.TypeAssociation from to _ _, _) -> printf "%s: %s" (T.tType from) (T.tType to) :: String)
  (substitutedAssociations, classInstantiationAssocs) <- fmap (bimap filterDesignatedForRemoval (foldr (Map.unionWith (++)) Map.empty) . unzip) $ for subAssociations $ \t@(T.TypeAssociation from to (T.CFD _ uv _ _) uci, insts) -> do
    case project from of
        T.TCon dd _ _ -> case insts !? dd of
          Just inst -> do
            -- select instance function to instantiate.
            let instFun = mustOr "[COMPILER ERROR]: Could not select function %s bruh," $ find (\fn -> fn.instFunctionClassUniqueVar == uv) inst.instFunctions

            -- hope it's correct....
            let baseFunctionScopeSnapshot = Map.singleton instFun.instDef.instClass insts  -- FIX: bad interface. we make a singleton, because we know which class it is. also, instance might create constraints of some other class bruh. ill fix it soon.
            (instFunType, T.DefinedFunction _ _ instAssocs) <- instantiateFunction baseFunctionScopeSnapshot instFun.instFunction

            to `uni` instFunType

            pure ((t, True), Map.singleton uci [(from, (instAssocs, instFun))])

          Nothing -> do
            pure ((t, False), mempty)  -- error.

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        _ -> pure ((t, False), mempty)

  liftIO $ ctxPrint' $ printf "Associations (after): %s" (Common.encloseSepBy "[" "]" ", " $ substitutedAssociations <&> \(T.TypeAssociation from to _ _, _) -> printf "%s: %s" (T.tType from) (T.tType to) :: String)
  RWS.modify $ \s -> s { associations = s.associations <> substitutedAssociations }
  pure classInstantiationAssocs

--  2. report any errors or something.
-- TODO: all of these 3 functions are kinda hindi-style programming. FIX IT AFTER I UNDERSTAND WHAT IM DOING.
reportAssociationErrors :: Infer ()
reportAssociationErrors = do
  assocs <- RWS.gets associations
  su <- RWS.gets typeSubstitution
  let subAssociations = first (subst su) <$> assocs

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for subAssociations $ \t@(T.TypeAssociation from _ (T.CFD cd _ _ _) _, insts) -> do
    case project from of
        T.TCon dd _ _ -> case insts !? dd of
          Just _ -> error "[COMPILER ERROR]: resolvable associated type found. should already be taken care of."

          Nothing -> do
            err $ DataDefDoesNotImplementClass dd cd
            pure (t, True)

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        T.TFun {} -> do
          err $ FunctionTypeConstrainedByClass from cd
          pure (t, True)

        T.TVar tv -> do
          error $ printf "[COMPILER ERROR]: associated type of tvar %s not bound by this function. should not happen?" (T.tTVar tv)

        T.TyVar _ -> do
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }


-- used after generalization to
--  1. extract associations for the function.
rummageThroughAssociations :: UniqueVar -> Subst -> Infer [T.FunctionTypeAssociation]
rummageThroughAssociations funUV su = do
  assocs <- RWS.gets associations
  let subAssociations = first (subst su) <$> assocs

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for subAssociations $ \t@(T.TypeAssociation from _ (T.CFD cd _ _ _) _, insts) -> do
    case project from of
        T.TVar tv | tv.binding == BindByVar funUV -> do
          -- will be added later to the association list!
          pure (t, True)

        _ ->
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }

  -- second: extract associations for the function.
  let functionAssociations = flip mapMaybe subAssociations $ \(T.TypeAssociation from to cfd uci, _) -> case project from of
        T.TVar tv | tv.binding == BindByVar funUV ->
          Just $ T.FunctionTypeAssociation tv to cfd uci
        _ -> Nothing

  pure functionAssociations


  -- -- when some changes accured, do it again. this is because some expressions, like: a.b.c.d would require 3 iterations... is this okay??
  -- when (length substitutedMembers < length subMembers) substAccess

filterDesignatedForRemoval :: [(a, Bool)] -> [a]
filterDesignatedForRemoval = fmap fst . filter (not . snd)

-- addSelectedEnvironmentsFromInst :: Infer ()
-- addSelectedEnvironmentsFromInst = do
--   classUnions <- RWS.gets classFunctionUnions
--   for_ classUnions $ \(union, cfd, self, insts) -> do
--     su <- RWS.gets typeSubstitution
--     let self' = subst su self
--     let union' = subst su union
--     let (fn, inst) = T.selectInstanceFunction cfd self' insts
--     -- singletonEnv <- singleEnvUnion fn.instFunction.functionDeclaration.functionEnv
--     pure ()

--     -- By the end of typechecking, an instance should be selected.
--     -- We need to add that instance's environment to that function environment union.
--     -- First, unify environment.
--     -- substituting $ do
--     --   unifyFunEnv union' singletonEnv

--     -- second, unify the type with its constraints.
--     -- make a new type.
--     -- ERROR: wait, but why? I think I should remove it kekek.
--     -- let (dd@(T.DD _ scheme _ _), instTVs) = inst.instType
--     -- (tvs, unions) <- instantiateScheme scheme

--     -- for_ (zip instTVs tvs) $ \(instTV, tv) -> do
--     --   case T.fromCCs inst.instConstraints !? instTV of
--     --     Nothing -> pure ()
--     --     Just classes ->
--     --       for_ classes $ \klass ->
--     --         tv `constrain` klass

--     -- let t = Fix $ T.TCon dd tvs unions
--     -- self' `uni` t


-- Constructs a scheme for a function.
-- ignores assigned scheme!
constructSchemeForFunctionDeclaration :: T.FunDec -> Infer (Subst, Scheme, [T.FunctionTypeAssociation])
constructSchemeForFunctionDeclaration dec = do
      -- IMPORTANT: We only extract types from non-instantiated! The instantiated type might/will contain types from our function and we don't won't that. We only want to know which types are from outside.
      -- So, for a function, use its own type.
      -- For a variable, use the actual type as nothing is instantiated!
  let digOutTyVarsAndUnionsFromEnv :: T.Env -> (Set TyVar, Set T.EnvUnion)
      digOutTyVarsAndUnionsFromEnv (T.RecursiveEnv _ _) = mempty
      digOutTyVarsAndUnionsFromEnv (T.Env _ env) = foldMap (\(v, _ ,t) -> digThroughVar t v) env
        where
          digThroughVar :: T.Type -> T.Variable -> (Set TyVar, Set T.EnvUnion)
          digThroughVar t = \case
            T.DefinedVariable _ -> digOutTyVarsAndUnionsFromType t
            T.DefinedFunction f _ _ -> foldMap (digOutTyVarsAndUnionsFromType . snd) f.functionDeclaration.functionParameters <> digOutTyVarsAndUnionsFromType f.functionDeclaration.functionReturnType
            T.DefinedClassFunction (T.CFD cd _ _ _) snapshot _ _   -- TODO: I think we don't need to dig through instances?
              -> foldMap digOutFromInst insts
              where
                insts = defaultEmpty cd snapshot

                digOutFromInst :: T.InstDef -> (Set TyVar, Set T.EnvUnion)
                digOutFromInst inst = foldMap digOutFromInstFunction inst.instFunctions

                digOutFromInstFunction :: T.InstanceFunction -> (Set TyVar, Set T.EnvUnion)
                digOutFromInstFunction fn =
                  let fndec = fn.instFunction.functionDeclaration
                  in foldMap (digOutTyVarsAndUnionsFromType . snd) fndec.functionParameters <> digOutTyVarsAndUnionsFromType fndec.functionReturnType

      (tyVarsOutside, unionsOutside) = digOutTyVarsAndUnionsFromEnv dec.functionEnv
      (tyVarsDeclaration, unionsDeclaration) = foldMap (digOutTyVarsAndUnionsFromType . snd) dec.functionParameters <> digOutTyVarsAndUnionsFromType dec.functionReturnType

      -- TypesDefinedHere = FnType \\ Environment
      tyVarsOnlyFromHere = tyVarsDeclaration \\ tyVarsOutside
      unionsOnlyFromHere = unionsDeclaration \\ unionsOutside

      -- ALGO: ASSOCIATIONS

      -- function to find tvars defined for this function!
      definedTVars = findTVarsForID dec.functionId

      tvarsDefinedForThisFunction = foldMap (definedTVars . snd) dec.functionParameters <> definedTVars dec.functionReturnType

      -- Then substitute it.
      asTVar (T.TyV tyname classInstances) = T.TV tyname (BindByVar dec.functionId) (Set.fromList $ fst <$> classInstances)

      su = Subst mempty $ Map.fromSet (Fix . T.TVar . asTVar) tyVarsOnlyFromHere
      unionsOnlyFromHereWithTVars = Set.map (subst su) unionsOnlyFromHere  -- NOTE: Unions might also contain our TyVars, so we must substitute it also.

      tvarsFromTyVars = Set.map asTVar tyVarsOnlyFromHere
      Scheme tvars _ = Scheme (Set.toList $ tvarsFromTyVars <> tvarsDefinedForThisFunction) (Set.toList unionsOnlyFromHereWithTVars)

  -- add associations.
  assocs <- rummageThroughAssociations dec.functionId su -- remember to use the new Subst, which generalizes the associations.
  reportAssociationErrors

  let (_, assocUnions) = foldMap (\(T.FunctionTypeAssociation _ t _ _) -> digOutTyVarsAndUnionsFromType t) assocs
  let assocScheme = Scheme tvars (Set.toList $ unionsOnlyFromHereWithTVars <> assocUnions)

  pure (su, assocScheme, assocs)

digOutTyVarsAndUnionsFromType :: T.Type -> (Set TyVar, Set T.EnvUnion)
digOutTyVarsAndUnionsFromType = para $ \case
    T.TyVar tyv -> (Set.singleton tyv, mempty)
    T.TFun union ts t -> (mempty, Set.singleton (fst <$> union)) <> foldMap snd ts <> snd t
    T.TCon _ ts unis -> foldMap snd ts <> foldMap ((mempty,) . Set.singleton . fmap fst) unis
    t -> foldMap snd t


-- goes through the type and finds tvars that are defined for this function.
findTVarsForID :: UniqueVar -> T.Type -> Set T.TVar
findTVarsForID euid = cata $ \case
  T.TVar tv@(T.TV _ (BindByVar varid) _) | varid == euid -> Set.singleton tv
  t -> fold t

-- copy of previous function for ClassType
findTVarsForIDInClassType :: UniqueVar -> T.ClassType -> Set T.TVar
findTVarsForIDInClassType euid = cata $ \case
  T.CTVar tv@(T.TV _ (BindByVar varid) _) | varid == euid -> Set.singleton tv
  t -> fold t


-- Substitute return type for function.
withReturn :: T.Type -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }

getExpectedType :: T.Type -> MemName -> Infer (Maybe T.Type, Bool)  -- (maybe type, should remove from list?)
getExpectedType t memname = case project t of
  T.TCon dd@(T.DD _ (Scheme ogTVs ogUnions) (Left recs) _) tvs unions ->
    case find (\(T.DR _ name _ _) -> name == memname) recs of
      Just (T.DR _ _ recType _) -> do
        let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
        let recType' = mapTVs recType
        pure (Just recType', True)

      Nothing -> do
        err $ DataTypeDoesNotHaveMember dd memname
        pure (Nothing, True)

  T.TyVar _ ->
      -- type not yet known. ignore.
    pure (Nothing, False)

  T.TCon dd@(T.DD _ _ (Right _) _) _ _ -> do
    err $ DataTypeIsNotARecordType dd memname
    pure (Nothing, True)

  T.TFun {} -> do
    err $ FunctionIsNotARecord t memname
    pure (Nothing, True)

  T.TVar tv -> do
    err $ TVarIsNotARecord tv memname
    pure (Nothing, True)


inferDecon :: R.Decon -> Infer T.Decon
inferDecon = cata $ fmap embed . \case
    R.CaseVariable uv -> do
      t <- var uv
      pure (T.CaseVariable t uv)

    R.CaseRecord dd cases -> do
      dd' <- inferDatatype dd
      t <- instantiateRecord dd'
      cases' <- sequenceA2 cases

      for_ cases' $ \(mem, decon) -> do
        mt <- addMember t mem
        uni mt (T.decon2type decon)

      pure $ T.CaseRecord t dd' cases'

    R.CaseConstructor rcon idecons -> do

      -- Ger proper constructor.
      con@(T.DC dd@(T.DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts _) <- inferConstructor rcon

      -- Deconstruct decons.
      decons <- sequenceA idecons

      -- Custom instantiation for a deconstruction.
      -- Create a parameter list to this constructor
      (tvs, unions) <- instantiateScheme mempty scheme
      let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
      let ts = mapTVs <$> usts

      let args = T.decon2type <$> decons
      uniMany ts args

      let t = Fix $ T.TCon dd tvs unions
      pure (T.CaseConstructor t con decons)


------
-- Instantiation
------

-- TODO: merge it with 'inferVariable'.
instantiateVariable :: T.Variable -> Infer (T.Type, T.Variable)
instantiateVariable = \case
  T.DefinedVariable v -> var v <&> (,T.DefinedVariable v)
  T.DefinedFunction fn snapshot _ -> do
    instantiateFunction snapshot fn

  T.DefinedClassFunction cfd@(T.CFD cd funid params ret) snapshot self _ -> do
    -- TODO: a lot of it is duplicated from DefinedFunction. sussy
    let allTypes = ret : map snd params
    let thisFunctionsTVars = foldMap (findTVarsForIDInClassType funid) allTypes

    -- dig out unions from class type (instantiate class type)
    -- all these unions should come from datatypes. so...
    let extractUnions :: T.ClassType -> Set T.EnvUnion
        extractUnions = cata $ \case
          T.CTCon dd params ->
            let ddUnions = Set.fromList $ extractUnionsFromDataType dd
                paramUnions = fold params
            in ddUnions <> paramUnions
          ct -> fold ct

    let thisFunctionsUnions = foldMap extractUnions allTypes

    let schemeTVars = Set.toList thisFunctionsTVars
    let schemeUnions = Set.toList thisFunctionsUnions
    let scheme = Scheme schemeTVars schemeUnions

    (itvs, iunions) <- instantiateScheme mempty scheme
    let tvmap = Map.fromList $ zip schemeTVars itvs
    let unionmap = Map.fromList $ zip (T.unionID <$> schemeUnions) iunions
    let mapTVs = mapTVsWithMap tvmap unionmap . mkTypeFromClassType self
    fnUnion <- emptyUnion

    let fnType = Fix $ T.TFun fnUnion (mapTVs . snd <$> params) (mapTVs ret)

    let insts = defaultEmpty cd snapshot
    uci <- newClassInstantiation
    associateType self fnType cfd insts uci
    -- addClassFunctionUse fnUnion cfd self insts


    pure (fnType, T.DefinedClassFunction cfd snapshot self uci)

instantiateFunction :: T.ScopeSnapshot -> T.Function -> Infer (T.Type, T.Variable)
instantiateFunction snapshot fn = do
    let fundec = fn.functionDeclaration
    let (Scheme schemeTVars schemeUnions) = fundec.functionScheme

    (tvs, unions) <- instantiateScheme snapshot fundec.functionScheme

    -- Prepare a mapping for the scheme!
    let tvmap = Map.fromList $ zip schemeTVars tvs
    let unionmap = Map.fromList $ zip (T.unionID <$> schemeUnions) unions
    let mapTVs = mapTVsWithMap tvmap unionmap

    ctxPrint' $ printf "Instantiation of %s" (show fundec.functionId.varName)
    ctxPrint (Common.ppMap . fmap (bimap T.tTVar T.tType) . Map.toList) tvmap
    ctxPrint (Common.ppMap . fmap (bimap Common.ppUnionID (T.tEnvUnion . fmap T.tType)) . Map.toList) unionmap


    -- Create type from function declaration
    fnUnion <- singleEnvUnion (mapTVs <$> fundec.functionEnv)
    let fnType = Fix $ T.TFun fnUnion (mapTVs . snd <$> fundec.functionParameters) (mapTVs fundec.functionReturnType)

    -- add new associations
    assocs <- for fundec.functionAssociations $ \(T.FunctionTypeAssociation tv to cfd@(T.CFD cd _ _ _) uci) -> do
      let from = mapTVs $ Fix $ T.TVar tv
      let mto = mapTVs to
      associateType from mto cfd (fromMaybe mempty $ snapshot !? cd) uci  -- TEMP
      pure mto


    ctxPrint' $ printf "After instantiation: %s" (T.tType fnType)

    pure (fnType, T.DefinedFunction fn snapshot assocs)


associateType :: T.Type -> T.Type -> T.ClassFunDec -> T.PossibleInstances -> UniqueClassInstantiation -> Infer ()
associateType based result cfd insts uci =
  let ta = T.TypeAssociation based result cfd uci
  in RWS.modify $ \s -> s { associations = (ta, insts) : s.associations }


-- addClassFunctionUse :: T.EnvUnion -> T.ClassFunDec -> T.Type -> T.PossibleInstances -> Infer ()
-- addClassFunctionUse eu cfd self insts = RWS.modify $ \s -> s { classFunctionUnions = (eu, cfd, self, insts) : s.classFunctionUnions }

instantiateConstructor :: EnvID -> T.DataCon -> Infer T.Type
instantiateConstructor envID = \case
  T.DC dd@(T.DD _ scheme _ _) _ [] _ -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    pure $ Fix $ T.TCon dd tvs unions

  (T.DC dd@(T.DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts@(_:_) _) -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
    let ts = mapTVs <$> usts

    let ret = Fix $ T.TCon dd tvs unions

    -- don't forget the empty env!
    let emptyEnv = T.Env envID []
    union <- singleEnvUnion emptyEnv

    pure $ Fix $ T.TFun union ts ret

instantiateRecord :: T.DataDef -> Infer T.Type
instantiateRecord dd@(T.DD _ scheme (Left _) _) = do
  (tvs, unions) <- instantiateScheme mempty scheme
  pure $ Fix $ T.TCon dd tvs unions

instantiateRecord (T.DD ut _ (Right _) _) = error $ printf "Attempted to instantiate ADT (%s) as a Record!" (Common.ppTypeInfo ut)


instantiateScheme :: T.ScopeSnapshot -> Scheme -> Infer ([T.Type], [T.EnvUnion])
instantiateScheme insts (Scheme schemeTVars schemeUnions) = do
  -- Prepare a mapping for the scheme!
  tyvs <- traverse (const fresh) schemeTVars  -- scheme
  let tvmap = Map.fromList $ zip schemeTVars tyvs

  -- Unions themselves also need to be mapped with the instantiated tvars!
  let mapOnlyTVsForUnions = mapTVsWithMap tvmap mempty
  unions <- traverse (\union -> cloneUnion (mapOnlyTVsForUnions <$> union)) schemeUnions

  -- also, don't forget to constrain new types.
  for_ (zip tyvs schemeTVars) $ \(t, tv) -> do
    for_ tv.tvConstraints $ \klass -> do
      let instmap = fromMaybe mempty $ insts !? klass
      t `constrain` (klass, instmap)

  pure (tyvs, unions)


mapTVsWithMap :: Map T.TVar T.Type -> Map UnionID T.EnvUnion -> T.Type -> T.Type
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
  renvQuery <- Map.fromList <$> traverse (\(v, t) -> (,t) <$> inferVariableProto v) (R.fromEnv renv)
  let newEnv = mapMaybe (\(v, t) -> Map.lookup (T.asProto v) renvQuery <&> (v,,t)) $ Set.toList modifiedInstantiations


  -- 4. and put that filtered stuff back. ? NO. ONLY IN ENV DEFS. SO WE COPY THAT ENVIRONMENT THERE NIGGA. inferFunction can be called for normal variables.
  -- let usedInstantiations = Set.fromList $ fmap (\(v, _, t) -> (v, t)) newEnv
  RWS.modify $ \s -> s { instantiations = outOfEnvInstantiations }

  pure (newEnv, x')


addEnv :: T.Variable -> T.Type -> Infer ()
addEnv v t = RWS.modify $ \s -> s { instantiations = Set.insert (v, t) s.instantiations }


var :: UniqueVar -> Infer T.Type
var v = do
  vars <- RWS.gets variables
  case vars !? v of
    Just t -> pure t
    Nothing -> do
      t <- fresh
      RWS.modify $ \s -> s { variables = Map.insert v t s.variables }
      pure t


addMember :: T.Type -> MemName -> Infer T.Type
addMember ogType memname = do
  t <- fresh  -- we don't know its type yet.
  RWS.modify $ \s -> s { memberAccess = (ogType, memname, t) : s.memberAccess }

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
          (tvs, unions) <- instantiateScheme mempty scheme
          pure $ Fix $ T.TCon dd tvs unions
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."



-------------------------------
--        UNIFICATION

uni :: T.Type -> T.Type -> Infer ()
uni t1 t2 = do
  substituting $ do
    su <- RWS.gets ctxSubst
    let (t1', t2') = subst su (t1, t2)
    unify t1' t2'

uniMany :: [T.Type] -> [T.Type] -> Infer ()
uniMany ts1 ts2 =
  substituting $ do
    su <- RWS.gets ctxSubst
    let (ts1', ts2') = subst su (ts1, ts2)
    unifyMany ts1' ts2'

constrain :: T.Type -> (T.ClassDef, T.PossibleInstances) -> Infer ()
constrain t cdi = do
  substituting $ do
    su <- RWS.gets ctxSubst
    let t' = subst su t
    addConstraint t' cdi

substituting :: SubstCtx a -> Infer a
substituting subctx = RWST $ \_ s -> do
  (x, ss, errs) <- RWS.runRWST subctx () (SubstState { ctxSubst = s.typeSubstitution, ctxTvargen = s.tvargen })
  pure (x, s { typeSubstitution = ss.ctxSubst, tvargen = ss.ctxTvargen }, errs)


------

unify :: T.Type -> T.Type -> SubstCtx ()
unify ttl ttr = do
  su <- RWS.gets ctxSubst
  let (tl, tr) = subst su (ttl, ttr)
  case bimap project project $ subst su (tl, tr) of
    (l, r) | l == r -> pure ()
    (T.TyVar tyv, _) -> do
      tyv `bind` tr
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint tr klass

    (_, T.TyVar tyv) -> do
      tyv `bind` tl
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint tl klass

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

addConstraint :: T.Type -> (T.ClassDef, T.PossibleInstances) -> SubstCtx ()
addConstraint t (klass, instances) = case project t of
      T.TCon dd _ _ -> do
        let mSelectedInst = instances !? dd
        case mSelectedInst of
          Nothing -> do
            err $ DataDefDoesNotImplementClass dd klass

          Just _ -> do
            -- Don't do anything? like, we only have to confirm that the instance gets applied, right?
            pure ()

      T.TVar tv -> do
        unless (Set.member klass tv.tvConstraints) $ do
          err $ TVarDoesNotConstrainThisClass tv klass

      T.TyVar tyv -> do
        -- create new tyvar with both classes merged!
        let cids = (klass, instances) : tyv.tyvConstraints
        newtyv <- freshTyVarInSubst cids
        tyv `bind` Fix (T.TyVar newtyv)

      T.TFun {} ->
        err $ FunctionTypeConstrainedByClass t klass

bind :: TyVar -> T.Type -> SubstCtx ()
bind tyv (Fix (T.TyVar tyv')) | tyv == tyv' = nun
bind tyv t | occursCheck tyv t =
              err $ InfiniteType tyv t
           | otherwise = do
  RWS.modify $ \su -> su
    { ctxSubst =
        let singleSubst  = Subst mempty (Map.singleton tyv t)
            Subst unions types = subst singleSubst su.ctxSubst
        in Subst unions (Map.insert tyv t types)
    }

unifyFunEnv :: T.EnvUnion -> T.EnvUnion -> SubstCtx ()
unifyFunEnv lenv renv = do
  unionID <- newUnionID

  -- BUG: adding 'subst su' here fixed some environments not having instantiated shit. (test 5_t10)
  su <- RWS.gets ctxSubst
  let (lenv'@(T.EnvUnion { T.unionID = lid }), renv'@(T.EnvUnion { T.unionID = rid })) = subst su (lenv, renv)
      union2envset = Set.fromList . (\(T.EnvUnion { T.union = union }) -> union)
      envset2union = Set.toList
      funEnv = envset2union $ union2envset lenv' <> union2envset renv'

  let env = T.EnvUnion { T.unionID = unionID, T.union = funEnv }

  RWS.modify $ \su -> su
    { ctxSubst =
        let unionSubst = Subst (Map.fromList [(lid, env), (rid, env)]) Map.empty -- i don't think we need an occurs check. BUG: we actually do, nigga.
            Subst unions ts = subst unionSubst su.ctxSubst  -- NOTE: technically, we don't even need to add this mapping to our global Subst, but then we would have to create a new fresh variable every time a new variable is created, or something similar (more error prone, so maybe not worth it.).
        in Subst (Map.insert rid env $ Map.insert lid env unions) ts
    }
  --       traceShow ("ENVUNI: " <> show lenv <> "|||||" <> show renv <> "8=====>" <> show env <> "\n") $ 

occursCheck :: Substitutable a => TyVar -> a -> Bool
occursCheck tyv t = tyv `Set.member` ftv t

err :: Monad m => TypeError -> RWST r [TypeError] s m ()
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
    , T.classInstantiationAssociations = Map.map (subst su) m.classInstantiationAssociations

    , T.functions = subst su <$> m.functions
    , T.datatypes = m.datatypes -- subst su <$> m.datatypes
    , T.classes = subst su <$> m.classes
    , T.instances = subst su <$> m.instances
    }

instance Substitutable T.ClassDef where
  ftv = mempty  -- no FTVs in declarations. will need to get ftvs from associated types and default functions when they'll be implemented.
  subst su cd = cd  -- TODO: not sure if there is anything to substitute.

instance Substitutable T.InstDef where
  ftv inst = foldMap ftv inst.instFunctions
  subst su inst = inst
    { T.instFunctions = subst su <$> inst.instFunctions
    }

instance Substitutable T.InstanceFunction where
  ftv ifn = ftv ifn.instFunction
  subst su ifn = ifn { T.instFunction = subst su ifn.instFunction }

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
        T.InstDefDef inst -> T.InstDefDef $ subst su inst
        s -> first (subst su) s

instance (Substitutable expr, Substitutable stmt) => Substitutable (T.Case expr stmt) where
  ftv kase = ftv kase.deconstruction <> ftv kase.caseCondition <> ftv kase.body
  subst su kase = T.Case (subst su kase.deconstruction) (subst su kase.caseCondition) (subst su kase.body)

instance Substitutable (Fix T.DeconF) where
  ftv = cata $ \case
    T.CaseVariable t _ -> ftv t
    T.CaseConstructor t _ ftvs -> ftv t <> mconcat ftvs
    T.CaseRecord t _ ftvs -> ftv t <> foldMap snd ftvs
  subst su = hoist $ \case
    T.CaseVariable t v -> T.CaseVariable (subst su t) v
    T.CaseConstructor t uc ds -> T.CaseConstructor (subst su t) uc ds
    T.CaseRecord t dd ds -> T.CaseRecord (subst su t) dd ds

instance Substitutable (Fix T.TypedExpr) where
  ftv = cata $ \(T.TypedExpr et ee) -> ftv et <> case ee of
    T.As e t -> e <> ftv t
    T.Lam env params body -> ftv env <> ftv params <> body
    T.Var _ v -> ftv v
    e -> fold e
  subst su = hoist $ \(T.TypedExpr et ee) -> T.TypedExpr (subst su et) (case ee of
    T.As e t -> T.As e (subst su t)
    T.Lam env params body -> T.Lam (subst su env) (subst su params) body
    T.Var loc v -> T.Var loc $ subst su v
    e -> e)

instance Substitutable T.Variable where
  ftv _ = mempty
  subst su (T.DefinedFunction fn ss assocs) = T.DefinedFunction (subst su fn) ss (subst su assocs)
  subst su (T.DefinedClassFunction cfd insts self uci) = T.DefinedClassFunction cfd (fmap2 (subst su) insts) (subst su self) uci
  subst _ x = x


instance Substitutable UniqueVar where
  ftv _ = mempty
  subst _ = id

instance Substitutable UniqueClassInstantiation where
  ftv _ = mempty
  subst _ = id

instance Substitutable MemName where
  ftv _ = mempty
  subst _ = id



instance Substitutable T.Function where
  ftv fn = ftv fn.functionBody \\ ftv fn.functionDeclaration
  subst su fn = T.Function { T.functionDeclaration = subst su fn.functionDeclaration, T.functionBody = subst su fn.functionBody }

instance Substitutable T.FunDec where
  ftv (T.FD _ _ params ret _ assocs _) = ftv params <> ftv ret <> ftv assocs -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 
  subst su (T.FD env fid params ret scheme assocs classInstantiationAssocs) = T.FD (subst su env) fid (subst su params) (subst su ret) scheme (subst su assocs) (Map.fromList $ fmap (bimap (subst su) (subst su)) $ Map.toList classInstantiationAssocs)

instance Substitutable T.TypeAssociation where
  ftv (T.TypeAssociation from to _ _) = ftv from <> ftv to
  subst su (T.TypeAssociation from to c uci) = T.TypeAssociation (subst su from) (subst su to) c uci

-- FIX: FUCK
instance Substitutable a => Substitutable (IORef a) where
  ftv ioref = ftv $ unsafePerformIO $ IORef.readIORef ioref
  subst su ioref = unsafePerformIO $ do
    IORef.modifyIORef ioref (subst su)
    pure ioref

instance Substitutable T.FunctionTypeAssociation where
  ftv (T.FunctionTypeAssociation _ to _ _) = ftv to
  subst su (T.FunctionTypeAssociation from to c uci) = T.FunctionTypeAssociation from (subst su to) c uci

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

instance (Substitutable a, Substitutable b, Substitutable c) => Substitutable (a, b, c) where
  ftv (a, b, c) = ftv a <> ftv b <> ftv c
  subst su (a, b, c) = (subst su a, subst su b, subst su c)

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

newClassInstantiation :: Infer UniqueClassInstantiation
newClassInstantiation = UCI <$> liftIO newUnique

-- Returns a fresh new tyvare
fresh :: Infer T.Type
fresh = Fix . T.TyVar <$> freshTyVar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyVar :: Infer TyVar
freshTyVar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV (letters !! nextVar) mempty

freshTyVarInSubst :: [(T.ClassDef, T.PossibleInstances)] -> SubstCtx TyVar
freshTyVarInSubst cdis = do
  TVG nextVar <- RWS.gets ctxTvargen
  RWS.modify $ \s -> s { ctxTvargen = TVG (nextVar + 1) }
  pure $ T.TyV (letters !! nextVar) cdis

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
type SubstCtx = RWST () [TypeError] SubstState IO     -- substitution

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe T.Type
  }

data SubstState = SubstState
  { ctxSubst :: Subst
  , ctxTvargen :: TVarGen
  }


data TypecheckingState = TypecheckingState
  { tvargen :: TVarGen

  -- current state of substitution.
  , typeSubstitution :: Subst

  , memoFunction :: Memo R.Function T.Function
  , memoDataDefinition :: Memo R.DataDef T.DataDef
  , memoClass :: Memo R.ClassDef T.ClassDef
  , memoInstance :: Memo R.InstDef T.InstDef

  , variables :: Map UniqueVar T.Type

  , memberAccess :: [(T.Type, MemName, T.Type)]  -- ((a :: t1).mem :: t2)
  , classFunctionUnions :: [(T.EnvUnion, T.ClassFunDec, T.Type, T.PossibleInstances)]  -- TODO: currently unused. remove later.
  , associations :: [(T.TypeAssociation, Map T.DataDef T.InstDef)]

  -- HACK?: track instantiations from environments. 
  --  (two different function instantiations will count as two different "variables")
  , instantiations :: Set (T.Variable, T.Type)

  }

emptySEnv :: TypecheckingState
emptySEnv = TypecheckingState
  { tvargen = newTVarGen
  , typeSubstitution = emptySubst

  , memoFunction = emptyMemo
  , memoDataDefinition = emptyMemo
  , memoClass = emptyMemo
  , memoInstance = emptyMemo

  , memberAccess = mempty

  , variables = mempty

  , instantiations = mempty
  , classFunctionUnions = mempty
  , associations = mempty
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

  | DataTypeDoesNotHaveMember T.DataDef MemName
  | DataTypeIsNotARecordType T.DataDef MemName
  | FunctionIsNotARecord T.Type MemName
  | TVarIsNotARecord T.TVar MemName

  | DataDefDoesNotImplementClass T.DataDef T.ClassDef
  | TVarDoesNotConstrainThisClass T.TVar T.ClassDef
  | FunctionTypeConstrainedByClass T.Type T.ClassDef

-- not sure if we have to have a show instance
instance Show TypeError where
  show = \case
    InfiniteType tyv t -> unwords ["InfiniteType", sctx $ T.tTyVar tyv, sctx $ T.tType t]
    TypeMismatch t t' -> printf "Type Mismatch: %s %s" (sctx $ T.tType t) (sctx $ T.tType t')
    MismatchingNumberOfParameters ts ts' -> printf "Mismatching number of parameters: (%d) %s (%d) %s" (length ts) (sctx $ ppList T.tType ts) (length ts') (sctx $ ppList T.tType ts')
    AmbiguousType tyv -> printf "Ambiguous type: %s" (sctx $ T.tTyVar tyv)

    DataTypeDoesNotHaveMember (T.DD ut _ _ _) memname -> printf "Record type %s does not have member %s." (sctx $ Common.ppTypeInfo ut) (sctx $ Common.ppMem memname)
    DataTypeIsNotARecordType (T.DD ut _ _ _) memname -> printf "%s is not a record type and thus does not have member %s." (sctx $ Common.ppTypeInfo ut) (sctx $ Common.ppMem memname)
    FunctionIsNotARecord t _ -> printf "Cannot subscript a function (%s)." (T.tType t)
    TVarIsNotARecord tv _ -> printf "Cannot subscript a type variable. (%s)" (T.tTVar tv)
    DataDefDoesNotImplementClass (T.DD ut _ _ _ ) cd -> printf "Type %s does not implement instance of class %s." (sctx $ Common.ppTypeInfo ut) (sctx $ Common.ppUniqueClass cd.classID)
    TVarDoesNotConstrainThisClass tv cd -> printf "TVar %s is not constrained by class %s." (T.tTVar tv) (Common.ppUniqueClass cd.classID)
    FunctionTypeConstrainedByClass t cd ->
      printf "Function type %t constrained by class %s (function types cannot implement classes, bruh.)" (T.tType t) (Common.ppUniqueClass cd.classID)




-----
-- DEBUG
----

dbgSubst :: Subst -> String
dbgSubst (Subst unions ts) =
  let tvars = Map.toList ts <&> \(ty, t) -> printf "%s => %s" (ctx T.tTyVar ty) (ctx T.tType t)
      unionRels = Map.toList unions <&> \(uid, union) -> printf "%s => %s" (ctx ppUnionID uid) (ctx (T.tEnvUnion . fmap T.tType) union)
  in unlines $ tvars <> ["--"] <> unionRels
