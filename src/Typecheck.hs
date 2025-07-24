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
{-# LANGUAGE NamedFieldPuns #-}

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
import Control.Monad (replicateM, zipWithM_, unless)
import Data.Bitraversable (bitraverse, bisequenceA)
import Data.Foldable (for_, fold, foldlM)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Bifunctor (bimap)
import Data.List ( find )
import Data.Bifoldable (bifoldMap, bifold)
import Data.Traversable (for)


import qualified AST.Resolved as R
import qualified AST.Typed as T

import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe)
import Text.Printf (printf)
import Control.Applicative (liftA3)
import Data.List.NonEmpty (NonEmpty)
import Misc.Memo (memo, Memo(..), emptyMemo)
import qualified AST.Common as Common
import AST.Prelude (Prelude)
import qualified AST.Prelude as Prelude
import AST.Common (Module, AnnStmt, StmtF (..), Type, CaseF (..), ExprF (..), ClassFunDec (..), DataCon (..), DataDef (..), ClassType, ClassTypeF (..), TypeF (..), TVar (..), Function (..), functionEnv, Exports (..), ClassDef (..), InstDef (..), InstFun (..), functionOther, FunDec (..), Decon, DeconF (..), IfStmt (..), Expr, Node (..), DeclaredType (..), XClassFunDec, MutAccess (..))
import AST.Resolved (R)
import AST.Typed ( TC, Scheme(..), TOTF(..) )
import AST.Def ((:.)(..), LitType (..), PP (..), Op (..), Binding (..), sctx, ppDef)
import qualified AST.Def as Def
import Data.String (fromString)
import Debug.Trace (trace)



----------- TO REMEMBER -----------------
-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)

typecheck :: Maybe Prelude -> Module R -> IO ([TypeError], Module TC)
typecheck mprelude rStmts = do
    let tcContext = Ctx { prelude = mprelude, returnType = Nothing }
    let senv = emptySEnv  -- we add typechecking state here, because it might be shared between modules? (especially memoization!)... hol up, is there anything to even share?

    -- Step 1: Generate type substitution (typing context) based on the constraints.
    (tStmts, su, envAdds, errs) <- generateSubstitution tcContext senv rStmts

    Def.phase "Typechecking (Before substitution)"
    Def.ctxPrint tStmts

    ----- Step 1.25
    -- Now add those extra variables to all them envs.
    let envSu = subst su $ EnvAddition envAdds  -- after this, env addition might STILL have some tyvars left over, but this will be fixed by the final substitution (which will just work on the new environments!)
    Def.phase "Env Additions"
    Def.ctxPrint' $ dbgSubst envSu
    let tStmts' = subst envSu tStmts

    ----- Step 1.5: Substitute tyvars in Subst's unions, because they are not actively substituted yet?
    -- HACK: I didn't check it when that happens, so I'll do it at the end.
    --  Unions that are to be substituted may have unsubstituted parameters. This should quickly fix that. However, I'm not sure where this happens. So, this is a TODO to figure out why this happens and when.
    -- ISSUE(function-tvars-in-its-env)
    let Subst suUnions suTVs = su
    let suNoUnions = Subst mempty suTVs
    let suUnions' = subst suNoUnions . subst envSu <$> suUnions
    let su' = Subst suUnions' suTVs


    Def.phase "Typechecking (og subst)"
    Def.ctxPrint' $ dbgSubst su

    Def.phase "Typechecking (fixed subst)"
    Def.ctxPrint' $ dbgSubst su'


    -- Step 2: Substitute the types with the inferred ones.
    let tStmts'' = subst su' tStmts'
    let errs' = errs <> (AmbiguousType <$> Set.toList (ftv tStmts''))


    Def.phase "Typechecking (After Substitution)"
    Def.ctxPrint tStmts''

    pure (errs', tStmts'')


---------------------------
--      INFERENCE        --
---------------------------

generateSubstitution :: Context -> TypecheckingState -> Module R -> IO (Module TC, Subst, EnvAdditions, [TypeError])
generateSubstitution env senv rModule = do
  (tvModule, s, errors) <- runRWST infer env senv

  pure (tvModule, s.typeSubstitution, s.envAdditions, errors)
  where
    infer = do
      -- Typecheck *all* functions, datatypes, etc. We want to typecheck a function even if it's not used (unlike Zig! (soig))
      _ <- inferDatatypes rModule.allDatatypes
      _ <- inferFunctions rModule.allFunctions
      tls <- inferTopLevel rModule.toplevel
      _ <- inferClasses rModule.allClasses
      _ <- inferInstances rModule.allInstances
      exs <- inferExports rModule.exports

      -- run it one last time.
      cia <- substAccessAndAssociations
      Def.ctxPrint cia

      reportAssociationErrors
      su <- RWS.gets typeSubstitution
      -- addSelectedEnvironmentsFromInst
      -- liftIO $ Def.phase "TOP LEVEL BEFORE"
      -- Def.ctxPrint (Def.ppLines pp) tls
      -- stmts <- replaceClassFunsWithInstantiations su cia tls

      -- liftIO $ Def.phase "TOP LEVEL AFTER"
      -- Def.ctxPrint (Def.ppLines pp) stmts

      pure $ T.Mod
        { T.topLevelStatements = tls
        , T.exports = exs
        }

    inferFunctions fns = for fns inferFunction
    inferDatatypes dds = for dds inferDataDef
    inferClasses cls = for cls inferClassDef
    inferInstances insts = for insts inferInstance
    inferTopLevel = inferStmts


-- Typechecks the top level part of the file.
--  Note: for top level, the return value will be set as U8, because of POSIX exit values.
--   Ideally, this type should mimic the target platform.
inferStmts :: (Traversable t) => t (AnnStmt R) -> Infer (t (AnnStmt TC))
inferStmts = traverse conStmtScaffolding  -- go through the block of statements...
  where
    -- for each statement...
    conStmtScaffolding :: AnnStmt R -> Infer (AnnStmt TC)
    conStmtScaffolding = cata (fmap embed . inferAnnStmt)

    -- go through additional layers (in the future also position information)...
    inferAnnStmt :: Base (AnnStmt R) (Infer a) -> Infer (Base (AnnStmt TC) a)
    inferAnnStmt (O (Def.Annotated anns rStmt)) = do
        tstmt <- bitraverse inferExpr id rStmt

        -- Map expr -> type for unification
        let ttstmt = first (\expr@(Fix (N t _)) -> (expr, t)) tstmt
        O . Def.Annotated anns <$> inferStmt ttstmt

    inferStmt :: StmtF R (Expr TC, Type TC) a -> Infer (StmtF TC (Expr TC) a)
    inferStmt stmt = case stmt of

      Assignment v (rexpr, t) -> do
        vt <- var v
        vt `uni` t

        pure $ Assignment v rexpr


      Mutation v loc accesses (expr, t) -> do
        vt <- var v

        case loc of
          Def.Local -> pure ()
          Def.FromEnvironment {} -> 
            addEnv (T.DefinedVariable v) vt

        -- prepare accesses for typechecking.
        taccesses <- for accesses $ \case
              MutRef -> (MutRef,) <$> fresh
              MutField mem -> (MutField mem,) <$> fresh

        let
          foldMutAccess :: Type TC -> (MutAccess TC, Type TC) -> Infer (Type TC)
          foldMutAccess rightType = \case
            (MutRef, accessT) -> do
              ptrT <- mkPtr rightType
              ptrT `uni` accessT
              pure ptrT
            (MutField mem, recordType) -> do
              fieldType <- addMember recordType mem
              fieldType `uni` rightType
              pure recordType

        -- we must build the type access by access, from RIGHT to LEFT.
        --  that's why it's reversed.
        -- ex: <&.dupa= 420
        --    the field 'dupa' has type Int, so
        --     type 420 == addMember fresh "dupa"
        --    then, we deref x, so the current type is the derefed value.
        --     type x `uni` mkPtr t
        --  get it?
        guessedType <- foldlM foldMutAccess t (reverse taccesses)  

        vt `uni` guessedType
        pure $ Mutation v loc taccesses expr


      If (IfStmt { condition = (cond, condt), ifTrue, ifElifs, ifElse }) -> do
        boolt <- findBuiltinType Prelude.boolFind

        condt `uni` boolt

        for_ ifElifs $ \((_, t), _) ->
          t `uni` boolt

        pure $ If $ IfStmt cond ifTrue ((fmap . first) fst ifElifs) ifElse


      Switch (rswitch, switchType) cases -> do
        -- infer the type for the expression inserted into the switch...
        tdecons <- traverse inferCase cases

        for_ tdecons $ \(_, dec) ->
          -- ...each deconstruction should be of that type.
          switchType `uni` dec

        pure $ Switch rswitch (fst <$> tdecons)
        where

          inferCase Case { deconstruction = decon, caseCondition = caseCon, caseBody = body } = do
            tdecon <- inferDecon decon
            let tCaseCon = fst <$> caseCon
            pure (Case tdecon tCaseCon body, Common.typeOfNode tdecon)


      Return rret -> do
        ret <- inferExpr rret
        emret <- RWS.asks returnType

        let opty = maybe (findBuiltinType Prelude.tlReturnFind) pure  -- NOTE: When default return type is nothing, this means that we are parsing prelude. Return type from top level should be "Int" (or, in the future, U8).
        eret <- opty emret
        Common.typeOfNode ret `uni` eret
        pure $ Return ret


      Print (expr, _) ->
        pure $ Print expr


      Pass ->
        pure Pass


      ExprStmt (expr, _) ->
        pure $ ExprStmt expr


      Fun rfn -> do
        fn <- inferFunction rfn

        -- RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

        pure $ Fun fn

      Inst rinst -> do
        inst <- inferInstance rinst

        -- RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

        pure $ Inst inst

      Other () -> pure $ Other ()



inferExpr :: Expr R -> Infer (Expr TC)
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType :: Base (Expr R) (Infer (Expr TC)) -> Infer (Base (Expr TC) (Expr TC))
    inferExprType (N () e) = do
      (e', t) <- inferLayer
      pure $ N t e' where

      inferLayer = case e of

        (Lam (R.LamDec uv env) args body) -> do

          -- add types to lambda parameters
          argts <- traverse var args
          let args' = zip args argts

          -- eval body
          (fenv, body') <- withEnv env $ do
            exprBody <- body

            -- First, finalize substitution by taking care of member access.
            -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
            --  At the end there will be one last member access.
            -- TODO: technically, we can do it all at the end. I should add it to state and replace them at the end (since they are all referred to by the unique instantiation id).
            classInstantiationAssocs <- substAccessAndAssociations
            su <- RWS.gets typeSubstitution
            -- replacedBody <- replaceInExpr su classInstantiationAssocs exprBody

            pure (classInstantiationAssocs, exprBody)

          -- be sure to copy the environment HERE!
          let varsFromNestedFun = case fenv of
                T.Env _ venv _ _ -> Set.fromList $ venv <&> \(v, _, t) -> (v, t)
                _ -> error "FUKKK"

          RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

          ufi <- newFunctionInstantiation  -- i guess we don't really need to save that tho.
          union <- singleEnvUnion Nothing ufi [] fenv
          let ret = Common.typeOfNode body'
          let t = Fix $ TFun union argts ret

          pure (Lam (T.LamDec uv fenv) args' body', t)


        As ae t -> do
          e' <- ae
          t' <- inferType t

          Common.typeOfNode e' `uni` t'

          pure (As e' t', t')


        Lit lt -> do
          t <- case lt of
            LInt _  -> findBuiltinType Prelude.intFind
            LFloat _ -> findBuiltinType Prelude.floatFind
          pure (Lit lt, t)


        Var v loc -> do
          (t, v') <- instantiateVariable loc =<< inferVariable v

          case loc of
            Def.Local -> pure ()
            Def.FromEnvironment {} -> do
              addEnv v' t

          pure (Var v' loc, t)


        Con c emptyEnv -> do
          c' <- inferConstructor c

          t <- instantiateConstructor emptyEnv c'
          pure (Con c' emptyEnv, t)

        RecCon dd insts -> do
          -- currently, all the redefinitions are reported in Resolver.
          -- this might not be the case when implementing ISSUE(anonymous-structs)

          dd' <- inferDatatype dd
          insts' <- Def.sequenceA2 insts
          t <- instantiateRecord dd'

          for_ insts' $ \(name, me) -> do
            mt <- addMember t name
            uni mt (Common.typeOfNode me)

          pure (RecCon dd' insts', t)


        RecUpdate re updates -> do
          te <- re
          updates' <- Def.sequenceA2 updates

          -- the type can be whatever, so we couldn't check these fields in the resolver ISSUE(anonymous-records)
          for_ updates' $ \(mem, me) -> do
            memt <- addMember (Common.typeOfNode te) mem
            uni memt (Common.typeOfNode me)

          pure (RecUpdate te updates', Common.typeOfNode te)

        MemAccess re memname -> do
          te <- re

          -- by now, we don't know the type of the member, because it's possible to define multiple members with the same name.
          t <- addMember (Common.typeOfNode te) memname

          pure (MemAccess te memname, t)

        Op il op ir -> do
          l <- il
          r <- ir

          let lt = Common.typeOfNode l
              rt = Common.typeOfNode r

          t <- if op == NotEquals || op == Equals
            then do
              lt `uni` rt
              findBuiltinType Prelude.boolFind

            else if op == LessThan || op == GreaterThan
            then do
              intt <- findBuiltinType Prelude.intFind
              lt `uni` intt
              rt `uni` intt
              findBuiltinType Prelude.boolFind

            else do
              intt <- findBuiltinType Prelude.intFind
              lt `uni` intt
              rt `uni` intt
              pure intt

          pure (Op l op r, t)


        Call callee args -> do
          args' <- sequenceA args
          let argts = Common.typeOfNode <$> args'
          callee' <- callee

          ret <- fresh
          union <- emptyUnion
          let ft = Fix $ TFun union argts ret

          Common.typeOfNode callee' `uni` ft

          pure (Call callee' args', ret)

        Ref ee -> do
          te <- ee
          let t = Common.typeOfNode te
          ptrType <- mkPtr t 
          pure (Ref te, ptrType)

        Deref ee -> do
          te <- ee
          let t = Common.typeOfNode te

          insidePtr <- fresh
          ptrType <- mkPtr insidePtr
          t `uni` ptrType
          pure (Deref te, insidePtr)



inferVariable :: R.Variable -> Infer T.Variable
inferVariable = \case
  R.DefinedVariable v -> pure $ T.DefinedVariable v

  R.ExternalFunction fn rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    pure $ T.DefinedFunction fn mempty snapshot tempFunctionInstantiation

  R.DefinedFunction fn rsnapshot -> do
    tfn <- inferFunction fn
    snapshot <- inferSnapshot rsnapshot
    pure $ T.DefinedFunction tfn mempty snapshot tempFunctionInstantiation

  R.ExternalClassFunction cfd@(CFD cd _ _ _) rsnapshot -> do
    -- insts <- fmap Map.fromList $ for (Map.toList (rinsts ! )) $ \(rdd, rinst) -> do
    --   dd <- inferDatatype rdd
    --   inst <- case rinst of
    --     R.DefinedInst rists  -> inferInstance rists
    --     R.ExternalInst tinst -> pure tinst
    --   pure (dd, inst)
    snapshot <- inferSnapshot rsnapshot
    let insts = Def.defaultEmpty cd snapshot

    self <- fresh
    self `constrain` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self tempClassInstantiation

  R.DefinedClassFunction rcfd rsnapshot -> do
    cfd@(CFD cd _ _ _) <- inferClassDeclaration rcfd
    -- insts <- fmap Map.fromList $ traverse (bitraverse inferDatatype inferInstance) $ Map.toList rinsts
    snapshot <- inferSnapshot rsnapshot
    let insts = Def.defaultEmpty cd snapshot

    self <- fresh
    self `constrain` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self tempClassInstantiation

tempFunctionInstantiation :: Def.UniqueFunctionInstantiation
tempFunctionInstantiation = error "should not evaluate"

tempClassInstantiation :: Def.UniqueClassInstantiation
tempClassInstantiation = error "should not evaluate"

inferSnapshot :: R.ScopeSnapshot -> Infer T.ScopeSnapshot
inferSnapshot = Def.bitraverseMap inferClass inferPossibleInstances
  where
    inferPossibleInstances :: R.PossibleInstances -> Infer T.PossibleInstances
    inferPossibleInstances = Def.bitraverseMap inferDatatype inferInst

inferVariableProto :: R.VariableProto -> Infer T.VariableProto
inferVariableProto = \case
  R.PDefinedVariable v -> pure $ T.PDefinedVariable v

  R.PExternalFunction fn -> pure $ T.PDefinedFunction fn
  R.PDefinedFunction fn -> T.PDefinedFunction <$> inferFunction fn

  R.PExternalClassFunction cfd -> pure $ T.PDefinedClassFunction cfd
  R.PDefinedClassFunction  cfd -> do
    T.PDefinedClassFunction <$> inferClassDeclaration cfd


inferConstructor :: R.Constructor -> Infer (DataCon TC)
inferConstructor = \case
  R.ExternalConstructor c -> pure c
  R.DefinedConstructor (DC rdd uc _ _) -> do
    (DD _ _ cons _) <- inferDataDef rdd

    -- HACK?: Find constructor through memoized DataDefinition.
    pure $ Def.mustOr (printf "[Compiler Error] Could not find constructor %s." (Def.ctx uc)) $
      find (\(DC _ uc' _ _) -> uc == uc') =<< Def.eitherToMaybe cons


-- pointless remap for class type
-- we keep the original structure to later check if the inst function matches the lass declaration
inferClassType :: ClassType R -> Infer (ClassType TC)
inferClassType = cata $ (.) (fmap embed) $ \case
  Self -> pure Self
  NormalType nt -> fmap NormalType $ case nt of
    TCon (R.DefinedDatatype rdd) rparams () -> do
      dd <- inferDataDef rdd
      params <- sequenceA rparams
      pure $ TCon dd params undefined
    TCon (R.ExternalDatatype dd) rparams () -> do
      params <- sequenceA rparams
      pure $ TCon dd params undefined
    TO rtv -> do
      tv <- inferTVar rtv
      pure $ TO $ TVar tv
    TFun () params ret -> do
      fnUnion <- emptyUnion
      TFun fnUnion <$> sequenceA params <*> ret

inferType :: Type R -> Infer (Type TC)
inferType = cata $ (.) (fmap embed) $ \case
  TCon (R.DefinedDatatype rdd) rparams () -> do
    dd <- inferDataDef rdd
    params <- sequenceA rparams
    let unions = T.extractUnionsFromDataType dd  -- TODO: shouldn't this be cloned???
    pure $ TCon dd params unions

  TCon (R.ExternalDatatype dd) rparams () -> do
    params <- sequenceA rparams
    let unions = T.extractUnionsFromDataType dd  -- TODO: same here...
    pure $ TCon dd params unions

  TO tv -> TO . TVar <$> inferTVar tv

  TFun () rargs rret -> liftA3 TFun emptyUnion (sequenceA rargs) rret

inferTVar :: TVar R -> Infer (TVar TC)
inferTVar rtv = do
  classes <- Def.traverseSet inferClass rtv.tvClasses
  pure $ TV
    { fromTV = rtv.fromTV
    , binding = rtv.binding
    , tvClasses = classes
    }

mkTypeFromClassType :: Type TC -> ClassType TC -> Type TC
mkTypeFromClassType self = cata $ fmap embed $ \case
  Self -> project self
  NormalType nt -> case nt of
    TCon dd params _ -> TCon dd params (T.extractUnionsFromDataType dd)
    TO tv -> TO tv
    TFun emptyFunUnion params ret -> TFun emptyFunUnion params ret



inferDatatype :: R.DataType -> Infer (DataDef TC)
inferDatatype = \case
  R.ExternalDatatype tdd -> pure tdd
  R.DefinedDatatype rdd -> inferDataDef rdd

inferDataDef :: DataDef R -> Infer (DataDef TC)
inferDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $
  \(DD ut rtvars erdcs anns) addMemo -> mdo
    tvars <- traverse inferTVar rtvars
    let dd = DD ut (T.Scheme tvars unions) edcs anns  -- NOTE: TVar correctness (no duplication, etc.) should be checked in Resolver!

    addMemo dd

    edcs <- case erdcs of
      Right rdcs -> fmap Right $ for rdcs $ \(DC _ uc rts dcAnn)-> do
        ts <- traverse inferType rts
        let dc = DC dd uc ts dcAnn
        pure dc

      Left rrecs -> fmap Left $ for rrecs $ \(Def.Annotated recAnn (memname, rt)) -> do
        t <- inferType rt
        pure $ Def.Annotated recAnn (memname, t)

    let unions = case edcs of
          Right dcs -> concatMap T.extractUnionsFromConstructor dcs
          Left drs -> concatMap (\(Def.Annotated _ (_, t)) -> T.mapUnion ut t) drs

    pure dd



inferFunction :: Function R -> Infer (Function TC)
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration

    params <- for rfundec.functionParameters $ \(v, definedType) -> do
      tv <- inferDecon v
      let vt = Common.typeOfNode tv

      case definedType of
        DeclaredType rt -> do
          t <- inferType rt

          vt `uni` t

        TypeNotDeclared -> pure ()
      pure (tv, vt)

    ret <- case rfundec.functionReturnType of
      DeclaredType t -> inferType t
      TypeNotDeclared -> fresh


    -- Set up temporary recursive env (if this function is recursive, this env will be used).
    let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
    let noGeneralizationScheme = Scheme mempty mempty
    let fundec = FD recenv rfundec.functionId params ret $ T.FunOther noGeneralizationScheme []
    let fun = Function { functionDeclaration = fundec, functionBody = body }

    -- Add *ungeneralized* type.
    addMemo fun

    -- Infer body.
    (env, body) <- withEnv rfundec.functionEnv $ withReturn ret $ do
      stmts <- inferStmts rfn.functionBody

      -- First, finalize substitution by taking care of member access.
      -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
      --  At the end there will be one last member access.
      -- TODO: technically, we can do it all at the end. I should add it to state and replace them at the end (since they are all referred to by the unique instantiation id).
      liftIO $ Def.ctxPrint' $ Def.printf "IN FUNCTION %s" (pp fundec.functionId)
      classInstantiationAssocs <- substAccessAndAssociations
      su <- RWS.gets typeSubstitution
      -- replacedStmts <- replaceClassFunsWithInstantiations su classInstantiationAssocs stmts

      pure (classInstantiationAssocs, stmts)

    -- now, replace it with a non-recursive environment.
    let fundec' = fundec { functionEnv = env }
    let fun' = fun { functionDeclaration = fundec' }


    pure fun'

  -- Add *generalized* version.
  addMemo fn

  pure fn

replaceClassFunsWithInstantiations :: Traversable f => Subst -> T.ClassInstantiationAssocs -> f (AnnStmt TC) -> Infer (f (AnnStmt TC))
replaceClassFunsWithInstantiations su cia = traverse $ cata $ \(O (Def.Annotated anns stmt)) -> do
  replacedStmt <- case first (replaceInExpr su cia) stmt of
        Return retExpr -> Return <$> replaceInExpr su cia retExpr
        otherStmt -> bisequenceA otherStmt
  pure $ (embed . O . Def.Annotated anns) replacedStmt

replaceInExpr :: Subst -> T.ClassInstantiationAssocs -> Expr TC -> Infer (Expr TC)
replaceInExpr su cia = cata $ \(N t e) -> fmap embed $ N t <$> case e of
  Var v@(T.DefinedClassFunction _ snapshot self uci) loc ->
    -- let mself = subst su self
    case cia !? (Nothing, uci) of
      Nothing -> pure $ Var v loc
      Just (_, (typeApplication, ifn), _, ufi) -> do
        let ucisInFunction = Set.fromList $ ifn.instFunDec.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ to _ uci) -> (Just (ufi, to), uci)
            appliedUCIs = Map.restrictKeys cia ucisInFunction
        -- ufi <- newFunctionInstantiation
        pure $ Var (T.DefinedFunction (Function ifn.instFunDec ifn.instFunBody) typeApplication snapshot ufi) loc

  -- note that this case should probably be the same as the one above after finding the actual function.
  Var (T.DefinedFunction fn ts snapshot ufi) loc -> do
    let ucisInFunction = Set.fromList $ fn.functionDeclaration.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ to _ uci) -> (Just (ufi, to), uci)
        appliedUCIs = Map.restrictKeys cia ucisInFunction
    pure $ Var (T.DefinedFunction fn ts snapshot ufi) loc

  As x at -> As <$> x <*> pure at

  expr -> sequenceA expr


-- Exports: what the current module will export.
inferExports :: Exports R -> Infer (Exports TC)
inferExports e = do
  dts   <- traverse inferDataDef e.datatypes
  fns   <- traverse inferFunction e.functions
  cls   <- traverse inferClassDef e.classes
  insts <- traverse inferInstance e.instances
  pure $ Exports
    { variables = e.variables
    , functions = fns
    , datatypes = dts
    , classes   = cls
    , instances = insts
    }


inferClass :: R.Class -> Infer (ClassDef TC)
inferClass = \case
  R.DefinedClass cd -> inferClassDef cd
  R.ExternalClass cd -> pure cd

inferClassDef :: ClassDef R -> Infer (ClassDef TC)
inferClassDef = memo memoClass (\mem s -> s { memoClass = mem }) $ \cd _ -> mdo
  let tcd = ClassDef
        { classID = cd.classID
        , classFunctions = funs
        }
  funs <- for cd.classFunctions $ inferClassFunDec tcd . R.DefinedClassFunDec
  pure tcd

inferClassFunDec :: ClassDef TC -> XClassFunDec R -> Infer (ClassFunDec TC)
inferClassFunDec cd = \case
  (R.ExternalClassFunDec cfd) -> pure cfd
  (R.DefinedClassFunDec (CFD _ uv params ret)) -> do
    params' <- for params $ \(decon, rt) -> do
      d <- inferDecon decon
      t <- inferClassType rt

      let dt = Common.typeOfNode d
      self <- fresh
      dt `uni` mkTypeFromClassType self t

      pure (d, t)

    ret' <- inferClassType ret
    pure $ CFD cd uv params' ret'

inferClassDeclaration :: ClassFunDec R -> Infer (ClassFunDec TC)
inferClassDeclaration (CFD rcd uv _ _) = do
  tcd <- inferClassDef rcd
  let mcfd = find (\(CFD _ cuv _ _) -> cuv == uv) tcd.classFunctions
  pure $ Def.mustOr (printf "[COMPILER ERROR]: Could not find function %s in class %s." (pp uv) (pp tcd.classID)) mcfd

inferInst :: R.Inst -> Infer (InstDef TC)
inferInst = \case
  R.ExternalInst inst -> pure inst
  R.DefinedInst inst -> inferInstance inst

inferInstance :: InstDef R -> Infer (InstDef TC)
inferInstance = memo memoInstance (\mem s -> s { memoInstance = mem }) $ \inst _ -> mdo
  klass <- inferClass inst.instClass
  it <- inferDatatype $ fst inst.instType
  tvars <- traverse inferTVar $ snd inst.instType

  let instDef = InstDef
        { instClass = klass
        , instType = (it, tvars)
        , instFuns = fns
        , instConstraints = ()
        }

  fns <- for inst.instFuns $ \rfn -> do
    -- TODO: add check?
    fn <- generalize $ mdo

      -- Infer function declaration.
      let rfundec = rfn.instFunDec

      params <- for rfundec.functionParameters $ \(v, definedType) -> do
        tv <- inferDecon v
        let vt = Common.typeOfNode tv

        case definedType of
          DeclaredType rt -> do
            t <- inferType rt

            vt `uni` t

          TypeNotDeclared -> pure ()
        pure (tv, vt)

      ret <- case rfundec.functionReturnType of
        DeclaredType t -> inferType t
        TypeNotDeclared -> fresh


      -- Set up temporary recursive env (if this function is recursive, this env will be used).
      let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
      let noGeneralizationScheme = Scheme mempty mempty
      let fundec = FD recenv rfundec.functionId params ret $ T.FunOther noGeneralizationScheme []
      let fun = Function { functionDeclaration = fundec, functionBody = body }

      -- Infer body.
      (env, body) <- withEnv rfundec.functionEnv $ withReturn ret $ do
        stmts <- inferStmts rfn.instFunBody

        -- First, finalize substitution by taking care of member access.
        -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
        --  At the end there will be one last member access.
        -- TODO: technically, we can do it all at the end. I should add it to state and replace them at the end (since they are all referred to by the unique instantiation id).
        classInstantiationAssocs <- substAccessAndAssociations
        -- replacedStmts <- replaceClassFunsWithInstantiations su classInstantiationAssocs stmts

        pure (classInstantiationAssocs, stmts)

      -- now, replace it with a non-recursive environment.
      let fundec' = fundec { functionEnv = env }
      let fun' = fun { functionDeclaration = fundec' }
      pure fun'

    -- First, finalize substitution by taking care of member access.
    -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
    --  At the end there will be one last member access.
    -- su <- RWS.gets typeSubstitution
    -- classInstantiationAssocs <- substAccessAndAssociations

    cfd <- inferClassFunDec klass rfn.instClassFunDec
    pure InstFun
      { instFunDec = fn.functionDeclaration
      , instFunBody = fn.functionBody -- rfn.classFunctionPrototypeUniqueVar
      , instDef = instDef
      , instClassFunDec = cfd
      }

  pure instDef


-- Generalizes the function inside.
generalize :: Infer (Function TC) -> Infer (Function TC)
generalize ifn = do
  unsuFn <- ifn

  Def.ctxPrint' "Unsubstituted function:"
  Def.ctxPrint unsuFn

  csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  let fn = subst csu unsuFn
  (su, scheme, assocs) <- constructSchemeForFunctionDeclaration fn.functionDeclaration

  Def.ctxPrint' $ printf "Scheme for %s: %s" (pp fn.functionDeclaration.functionId) (pp scheme)
  let generalizedFn = subst su fn


  let generalizedFnWithScheme = generalizedFn { functionDeclaration = generalizedFn.functionDeclaration { functionOther = T.FunOther { T.functionScheme = scheme, T.functionAssociations = assocs } } }

  -- Also, remember the substitution! (tvars might escape the environment)
  --  TODO: not sure if that's the best way. maybe instead of doing this, just add it in the beginning and resubstitute the function.
  substituting $ do
    let (Subst _ tvars) = su  -- NOTE: safe!
    for_ (Map.toList tvars) $ uncurry bind

  pure generalizedFnWithScheme


substAccessAndAssociations :: Infer T.ClassInstantiationAssocs
substAccessAndAssociations = do
  liftIO $ Def.phase "SUBST ACCESS"
  go where
    go = do
      didAccessProgressedSubstitutions <- substAccess
      classInstantiationAssocs <- substAssociations
      let didAssociationsProgressedSubstitutions = not $ null classInstantiationAssocs
      liftIO $ Def.ctxPrint' $ Def.printf "CIA KEYS: %s" $ pp $ Set.toList $ Map.keysSet classInstantiationAssocs
      liftIO $ Def.ctxPrint classInstantiationAssocs

      -- There should be no more than one UCI for a type. These are already selected.
      if didAccessProgressedSubstitutions || didAssociationsProgressedSubstitutions
        then Map.unionWith (error "more than one assoc for uci should not happen") classInstantiationAssocs <$> go
        else do
          liftIO $ Def.phase "END SUBST ACCESS"
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
  dbgAssociations "before" subAssociations

  (substitutedAssociations, classInstantiationAssocs) <- fmap (bimap filterDesignatedForRemoval (foldr (<>) Map.empty) . unzip) $ for subAssociations $ \t@(T.TypeAssociation from to (CFD _ uv _ _) uci baseUFI envsToAddTo, insts) -> do
    case project from of
        TCon dd _ _ -> case insts !? dd of
          Just inst -> do
            -- select instance function to instantiate.
            let instFun = Def.mustOr (printf "[COMPILER ERROR]: Could not select function %s bruh," (pp uv)) $ find (\InstFun { instClassFunDec = CFD _ cuv _ _ } -> cuv == uv) inst.instFuns

            -- hope it's correct....
            let baseFunctionScopeSnapshot = Map.singleton instFun.instDef.instClass insts  -- FIX: bad interface. we make a singleton, because we know which class it is. also, instance might create constraints of some other class bruh. ill fix it soon.
            -- TODO: FromEnvironment locality only here, because it means we won't add anything extra to the instantiations.
            (instFunType, T.DefinedFunction fn instAssocs _ ufi, env@(T.Env _ _ _ level)) <- instantiateFunction (Just uci) baseFunctionScopeSnapshot $ Function instFun.instFunDec instFun.instFunBody

            to `uni` instFunType
            Def.ctxPrint' $ Def.printf "ENV ASSOC: %s" $ pp env
            addExtraToEnv envsToAddTo env

            pure ((t, True), Map.singleton ((,instFunType) <$> baseUFI, uci) (from, (instAssocs, instFun), level, ufi))

          Nothing -> do
            pure ((t, False), mempty)  -- error.

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        _ -> pure ((t, False), mempty)

  dbgAssociations "after" substitutedAssociations
  RWS.modify $ \s -> s { associations = s.associations <> substitutedAssociations }
  pure classInstantiationAssocs

-- adds last fixups to the environment.
addExtraToEnv :: [Def.EnvID] -> T.Env -> Infer ()
addExtraToEnv _ (T.RecursiveEnv {}) = error "should not happen"
addExtraToEnv envIds (T.Env _ vars _ instEnvStack) =
  let
    envsAndLevels = reverse $ zip (reverse envIds) [0 :: Def.Level ..]

    instLevel = Def.envStackToLevel instEnvStack

    newEnvAdditions = flip foldMap envsAndLevels $ \(eid, currentLevel) ->
      if instLevel <= currentLevel
        then
          let fnLocality = if instLevel < currentLevel
                then Def.FromEnvironment instLevel
                else Def.Local
          in mempty -- [(T.DefinedClassFunction cfd (Map.singleton cd (Map.singleton dd ifn.instDef)) self uci, fnLocality, t)]  -- TEMP: we are redoing the "DefinedClassFunction" (instead of just dropping DefinedFunction), because currently in Mono we rely on this.
        else
          let
            unpackFromEnvironment :: Def.Level -> [(T.Variable, Def.Locality, Type TC)] -> [(T.Variable, Def.Locality, Type TC)]
            unpackFromEnvironment instEnvLevel
              = map (\(v, l, t) ->             -- adjust locality from the context of this environment.
                  let varLevel = case l of
                        Def.Local -> instEnvLevel
                        Def.FromEnvironment lev -> lev
                      newLocality = if varLevel == currentLevel
                        then Def.Local
                        else Def.FromEnvironment varLevel
                  in (v, newLocality, t))
              . filter (\(_, l, _) ->          -- filter variables, which should not even be in this environment.
                  let varLevel = case l of
                        Def.Local -> instEnvLevel
                        Def.FromEnvironment lev -> lev
                  in varLevel <= currentLevel)

            -- usedVarsInThisEnv = Set.fromList $ env <&> \(v, _, t) -> (v, t)
            usedVarsInInst = unpackFromEnvironment instLevel vars
          in Map.singleton eid usedVarsInInst
    -- | instLevel <= currentLevel ->
    --   let fnLocality = if instLevel < currentLevel
    --         then Def.FromEnvironment instLevel
    --         else Def.Local
    --   in [(T.DefinedClassFunction cfd (Map.singleton cd (Map.singleton dd ifn.instDef)) self uci, fnLocality, t)]  -- TEMP: we are redoing the "DefinedClassFunction" (instead of just dropping DefinedFunction), because currently in Mono we rely on this.

    -- -- we need "take out" variables from this function.
    -- | otherwise ->
    --   let
    --     usedVarsInThisEnv = Set.fromList $ env <&> \(v, _, t) -> (v, t)
    --     usedVarsInInst = unpackFromEnvironment instLevel instEnvVars
    --     usedVarsInInstDeduped = filter (\(v, _, t) -> Set.notMember (v, t) usedVarsInThisEnv) usedVarsInInst
    --   in usedVarsInInstDeduped
  in RWS.modify $ \s -> s { envAdditions = Map.unionWith (\new old ->
    -- Some other env addition might have used those variables before, so we have to remove repetitions.
    let oldSet = Set.fromList old
    in old <> filter (`Set.notMember` oldSet) new) newEnvAdditions s.envAdditions }

--  2. report any errors or something.
-- TODO: all of these 3 functions are kinda hindi-style programming. FIX IT AFTER I UNDERSTAND WHAT IM DOING.
reportAssociationErrors :: Infer ()
reportAssociationErrors = do
  assocs <- RWS.gets associations
  su <- RWS.gets typeSubstitution
  let subAssociations = first (subst su) <$> assocs

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for subAssociations $ \t@(T.TypeAssociation from _ (CFD cd _ _ _) _ _ _, insts) -> do
    case project from of
        TCon dd _ _ -> case insts !? dd of
          Just _ -> error "[COMPILER ERROR]: resolvable associated type found. should already be taken care of."

          Nothing -> do
            err $ DataDefDoesNotImplementClass dd cd
            pure (t, True)

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        TFun {} -> do
          err $ FunctionTypeConstrainedByClass from cd
          pure (t, True)

        TO (TVar tv) -> do
          error $ printf "[COMPILER ERROR]: associated type of tvar %s not bound by this function. should not happen?" (pp tv)

        TO (TyVar _) -> do
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }


-- used after generalization to
--  1. extract associations for the function.
rummageThroughAssociations :: Def.UniqueVar -> Subst -> Infer [T.FunctionTypeAssociation]
rummageThroughAssociations funUV su = do
  assocs <- RWS.gets associations
  let subAssociations = first (subst su) <$> assocs

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for subAssociations $ \t@(T.TypeAssociation from _ (CFD cd _ _ _) _ _ _, insts) -> do
    case project from of
        TO (TVar tv) | tv.binding == BindByVar funUV -> do
          -- will be added later to the association list!
          pure (t, True)

        _ ->
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }  -- TODO: what? what am i doing

  -- second: extract associations for the function.
  let functionAssociations = flip mapMaybe subAssociations $ \(T.TypeAssociation from to cfd uci _ _, _) -> case project from of
        TO (TVar tv) | tv.binding == BindByVar funUV ->
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
constructSchemeForFunctionDeclaration :: FunDec TC -> Infer (Subst, Scheme, [T.FunctionTypeAssociation])
constructSchemeForFunctionDeclaration dec = do
      -- IMPORTANT: We only extract types from non-instantiated! The instantiated type might/will contain types from our function and we don't won't that. We only want to know which types are from outside.
      -- So, for a function, use its own type.
      -- For a variable, use the actual type as nothing is instantiated!
  let digOutTyVarsAndUnionsFromEnv :: T.Env -> (Set T.TyVar, Set T.EnvUnion)
      digOutTyVarsAndUnionsFromEnv (T.RecursiveEnv _ _) = mempty
      digOutTyVarsAndUnionsFromEnv (T.Env _ env _ _) = foldMap (\(v, _ ,t) -> digThroughVar t v) env
        where
          digThroughVar :: Type TC -> T.Variable -> (Set T.TyVar, Set T.EnvUnion)
          digThroughVar t = \case
            T.DefinedVariable _ -> digOutTyVarsAndUnionsFromType t
            T.DefinedFunction f _ _ _ -> foldMap (digOutTyVarsAndUnionsFromType . snd) f.functionDeclaration.functionParameters <> digOutTyVarsAndUnionsFromType f.functionDeclaration.functionReturnType
            T.DefinedClassFunction (CFD cd _ _ _) snapshot _ _   -- TODO: I think we don't need to dig through instances?
              -> foldMap digOutFromInst insts
              where
                insts = Def.defaultEmpty cd snapshot

                digOutFromInst :: InstDef TC -> (Set T.TyVar, Set T.EnvUnion)
                digOutFromInst inst = foldMap digOutFromInstFunction inst.instFuns

                digOutFromInstFunction :: InstFun TC -> (Set T.TyVar, Set T.EnvUnion)
                digOutFromInstFunction fn =
                  let fndec = fn.instFunDec
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
      asTVar (T.TyV tyname classInstances) = TV tyname (BindByVar dec.functionId) (Set.fromList $ fst <$> classInstances)

      su = Subst mempty $ Map.fromSet (Fix . TO . TVar . asTVar) tyVarsOnlyFromHere
      unionsOnlyFromHereWithTVars = Set.map (subst su) unionsOnlyFromHere  -- NOTE: Unions might also contain our TyVars, so we must substitute it also.

      tvarsFromTyVars = Set.map asTVar tyVarsOnlyFromHere
      Scheme tvars _ = Scheme (Set.toList $ tvarsFromTyVars <> tvarsDefinedForThisFunction) (Set.toList unionsOnlyFromHereWithTVars)

  -- add associations.
  assocs <- rummageThroughAssociations dec.functionId su -- remember to use the new Subst, which generalizes the associations.
  reportAssociationErrors

  let (_, assocUnions) = foldMap (\(T.FunctionTypeAssociation _ t _ _) -> digOutTyVarsAndUnionsFromType t) assocs
  let assocScheme = Scheme tvars (Set.toList $ unionsOnlyFromHereWithTVars <> assocUnions)

  pure (su, assocScheme, assocs)

digOutTyVarsAndUnionsFromType :: Type TC -> (Set T.TyVar, Set T.EnvUnion)
digOutTyVarsAndUnionsFromType = para $ \case
    TO (TyVar tyv) -> (Set.singleton tyv, mempty)
    TFun union ts t -> (mempty, Set.singleton union) <> foldMap snd ts <> snd t
    TCon _ ts unis -> foldMap snd ts <> foldMap ((mempty,) . Set.singleton) unis
    t -> foldMap snd t


-- goes through the type and finds tvars that are defined for this function.
findTVarsForID :: Def.UniqueVar -> Type TC -> Set (TVar TC)
findTVarsForID euid = cata $ \case
  TO (TVar tv@(TV _ (Def.BindByVar varid) _)) | varid == euid -> Set.singleton tv
  t -> fold t

-- copy of previous function for ClassType
findTVarsForIDInClassType :: Def.UniqueVar -> ClassType TC -> Set (TVar TC)
findTVarsForIDInClassType euid = cata $ \case
  NormalType (TO (TVar tv@(TV _ (Def.BindByVar varid) _)))  | varid == euid -> Set.singleton tv
  t -> fold t


-- Substitute return type for function.
withReturn :: Type TC -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }

getExpectedType :: Type TC -> Def.MemName -> Infer (Maybe (Type TC), Bool)  -- (maybe type, should remove from list?)
getExpectedType t memname = case project t of
  TCon dd@(DD _ (Scheme ogTVs ogUnions) (Left recs) _) tvs unions ->
    case find (\(Def.Annotated _ (name, _)) -> name == memname) recs of
      Just (Def.Annotated _ (_, recType)) -> do
        let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
        let recType' = mapTVs recType
        pure (Just recType', True)

      Nothing -> do
        err $ DataTypeDoesNotHaveMember dd memname
        pure (Nothing, True)

  TO (TyVar _) ->
      -- type not yet known. ignore.
    pure (Nothing, False)

  TCon dd@(DD _ _ (Right _) _) _ _ -> do
    err $ DataTypeIsNotARecordType dd memname
    pure (Nothing, True)

  TFun {} -> do
    err $ FunctionIsNotARecord t memname
    pure (Nothing, True)

  TO (TVar tv) -> do
    err $ TVarIsNotARecord tv memname
    pure (Nothing, True)


inferDecon :: Decon R -> Infer (Decon TC)
inferDecon = cata $ \(N () d) -> fmap embed $ case d of
    CaseVariable uv -> do
      t <- var uv
      pure $ N t $ CaseVariable uv

    CaseRecord dd cases -> do
      dd' <- inferDatatype dd
      t <- instantiateRecord dd'
      cases' <- Def.sequenceA2 cases

      for_ cases' $ \(mem, decon) -> do
        mt <- addMember t mem
        uni mt (Common.typeOfNode decon)

      pure $ N t $ CaseRecord dd' cases'

    CaseConstructor rcon idecons -> do

      -- Ger proper constructor.
      con@(DC dd@(DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts _) <- inferConstructor rcon

      -- Deconstruct decons.
      decons <- sequenceA idecons

      -- Custom instantiation for a deconstruction.
      -- Create a parameter list to this constructor
      (tvs, unions) <- instantiateScheme mempty scheme
      let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
      let ts = mapTVs <$> usts

      let args = Common.typeOfNode <$> decons
      uniMany ts args

      let t = Fix $ TCon dd tvs unions
      pure $ N t $ CaseConstructor con decons


------
-- Instantiation
------

-- TODO: merge it with 'inferVariable'.
instantiateVariable :: Def.Locality -> T.Variable -> Infer (Type TC, T.Variable)
instantiateVariable loc = \case
  T.DefinedVariable v -> var v <&> (,T.DefinedVariable v)
  T.DefinedFunction fn _ snapshot _ -> do
    (t, v, env) <- instantiateFunction Nothing snapshot fn -- notice that we use the UFI from here (inferVariable just creates a temp error type to not use it)

    associations <- RWS.gets associations
    liftIO $ Def.ctxPrint' $ printf "Associations (instantiation): %s" (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation from to _ uci ufi _, _) -> printf "(%s) %s: %s" (pp (uci, ufi)) (pp from) (pp to) :: String)

    -- add instantiations!
    --  only when it's a local function should you add stuff from its environment to instantiations.
    let gatherInstsFromEnvironment :: T.Env -> Set (T.Variable, Type TC)
        gatherInstsFromEnvironment = \case
            T.RecursiveEnv _ _ -> mempty
            T.Env _ vars _ _ -> flip foldMap vars $ \case
              (envVar@(T.DefinedFunction fn _ _ ufi), Def.Local, t) ->
                -- NOTE: we need mapped envs, so we have to dig through the type. but, are we too permissive? should we only choose this current env? or all of them? how do we distinguish the "current" one?
                let currentEnvID = T.envID fn.functionDeclaration.functionEnv
                    envs = case project t of
                      TFun union _ _ -> map (\(_, _, _, env) -> env) $ filter (\(_, ufi', _, env) -> ufi' == ufi) union.union
                      _ -> error "impossible, it's a function type."
                in Set.insert (envVar, t) (foldMap gatherInstsFromEnvironment envs)
              (envVar, _, t) -> Set.singleton (envVar, t)

        theseInsts = if loc == Def.Local
        then gatherInstsFromEnvironment env
        else mempty

    RWS.modify $ \s -> s { instantiations = Set.insert (v, t) $ theseInsts <> s.instantiations }

    pure (t, v)


  T.DefinedClassFunction cfd@(CFD cd funid params ret) snapshot self _ -> do
    -- TODO: a lot of it is duplicated from DefinedFunction. sussy
    let allTypes = ret : map snd params
    let thisFunctionsTVars = foldMap (findTVarsForIDInClassType funid) allTypes

    -- dig out unions from class type (instantiate class type)
    -- all these unions should come from datatypes. so...
    let extractUnions :: ClassType TC -> Set (T.EnvUnion)
        extractUnions = cata $ \case
          NormalType (TCon dd params _) ->
            let ddUnions = Set.fromList $ T.extractUnionsFromDataType dd
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

    let fnType = Fix $ TFun fnUnion (mapTVs . snd <$> params) (mapTVs ret)

    let insts = Def.defaultEmpty cd snapshot
    uci <- newClassInstantiation
    associateType self fnType cfd insts uci Nothing
    -- addClassFunctionUse fnUnion cfd self insts
    Def.ctxPrint' $ printf "INSTANTIATING CLASS FUN %s. INSTS: %s" (pp uci) $ pp $ fmap (\(DD { ddName }) -> ddName) $ Set.toList $ Map.keysSet insts


    pure (fnType, T.DefinedClassFunction cfd snapshot self uci)

-- NOTE: these last two parameters are basically a hack. I don't yet know what to do when we're dealing with an instance function, so we're only doing it here for now. (we should probably do the same thing there, but it's not local, so modifying the state then would be bad. I'll have to think about it.)
instantiateFunction :: Maybe Def.UniqueClassInstantiation -> T.ScopeSnapshot -> Function TC -> Infer (Type TC, T.Variable, T.Env)
instantiateFunction muci snapshot fn = do
    let fundec = fn.functionDeclaration
    let (Scheme schemeTVars schemeUnions) = fundec.functionOther.functionScheme

    (tvs, unions) <- instantiateScheme snapshot fundec.functionOther.functionScheme

    -- Prepare a mapping for the scheme!
    let tvmap = Map.fromList $ zip schemeTVars tvs
    let unionmap = Map.fromList $ zip (T.unionID <$> schemeUnions) unions
    let mapTVs = mapTVsWithMap tvmap unionmap . mapClassSnapshot (Set.fromList schemeTVars) snapshot

    Def.ctxPrint' $ printf "Instantiation of %s" (pp fundec.functionId)
    Def.ctxPrint' $ printf "TVars: %s" (pp schemeTVars)
    Def.ctxPrint' $ printf "Scope Snapshot:\n%s" (T.dbgSnapshot snapshot)

    Def.ctxPrint $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) tvmap
    Def.ctxPrint $ (Def.ppMap . fmap (bimap Def.ppUnionID pp) . Map.toList) unionmap


    -- Create type from function declaration
    ufi <- newFunctionInstantiation

    -- add new associations
    assocs <- for fundec.functionOther.functionAssociations $ \(T.FunctionTypeAssociation tv to cfd@(CFD cd _ _ _) uci) -> do
      let from = mapTVs $ Fix $ TO $ TVar tv
      let mto = mapTVs to
      associateType from mto cfd (fromMaybe mempty $ snapshot !? cd) uci (Just ufi) -- TEMP
      pure mto

    fnUnion <- singleEnvUnion muci ufi assocs fundec.functionEnv
    let fnType = mapTVs $ Fix $ TFun fnUnion (snd <$> fundec.functionParameters) fundec.functionReturnType
    let mappedEnv = case project fnType of  -- we're lazy, so we're not writing another function, we're just unsafely deconstructing the result of that function.
          TFun (T.EnvUnion { T.union = [(_, _, _, env)] }) _ _ -> env
          _ -> error "MUST NOT HAPPEN."

    let v = T.DefinedFunction fn assocs snapshot ufi

    Def.ctxPrint' $ printf "For function %s:\n\tType %s.\n\tAfter instantiation: %s"
      (pp fundec.functionId)
      (printf "%s%s -> %s" (pp fundec.functionEnv) (Def.encloseSepBy "(" ")" ", " $ pp <$> fundec.functionParameters) (pp fundec.functionReturnType) :: String)
      (pp fnType)

    pure (fnType, v, mappedEnv)


associateType :: Type TC -> Type TC -> ClassFunDec TC -> T.PossibleInstances -> Def.UniqueClassInstantiation -> Maybe Def.UniqueFunctionInstantiation -> Infer ()
associateType based result cfd insts uci ufi = do
    Def.ctxPrint' $ Def.printf "ASSOC: %s %s" (pp uci) (pp ufi)
    estack <- RWS.gets envStack
    let ta = T.TypeAssociation based result cfd uci ufi estack

    RWS.modify $ \s -> s { associations = (ta, insts) : s.associations }


-- addClassFunctionUse :: T.EnvUnion -> T.ClassFunDec -> T.Type -> T.PossibleInstances -> Infer ()
-- addClassFunctionUse eu cfd self insts = RWS.modify $ \s -> s { classFunctionUnions = (eu, cfd, self, insts) : s.classFunctionUnions }

instantiateConstructor :: Def.EnvID -> DataCon TC -> Infer (Type TC)
instantiateConstructor envID = \case
  DC dd@(DD _ scheme _ _) _ [] _ -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    pure $ Fix $ TCon dd tvs unions

  (DC dd@(DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts@(_:_) _) -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    let mapTVs = mapTVsWithMap (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions) unions)
    let ts = mapTVs <$> usts

    let ret = Fix $ TCon dd tvs unions

    -- don't forget the empty env!
    let emptyEnv = T.Env envID [] mempty []
    ufi <- newFunctionInstantiation
    union <- singleEnvUnion Nothing ufi [] emptyEnv

    pure $ Fix $ TFun union ts ret

instantiateRecord :: DataDef TC -> Infer (Type TC)
instantiateRecord dd@(DD _ scheme (Left _) _) = do
  (tvs, unions) <- instantiateScheme mempty scheme
  pure $ Fix $ TCon dd tvs unions

instantiateRecord (DD ut scheme (Right _) _) = error $ printf "Attempted to instantiate ADT (%s) as a Record!" (pp ut)


instantiateScheme :: T.ScopeSnapshot -> Scheme -> Infer ([Type TC], [T.EnvUnion])
instantiateScheme insts (Scheme schemeTVars schemeUnions) = do
  -- Prepare a mapping for the scheme!
  tyvs <- traverse (const fresh) schemeTVars  -- scheme
  let tvmap = Map.fromList $ zip schemeTVars tyvs

  -- Unions themselves also need to be mapped with the instantiated tvars!
  let mapOnlyTVsForUnions = mapTVsWithMap tvmap mempty . mapClassSnapshot (Set.fromList schemeTVars) insts
  unions <- traverse (\union -> cloneUnion (mapOnlyTVsForUnions <$> union)) schemeUnions

  -- also, don't forget to constrain new types.
  for_ (zip tyvs schemeTVars) $ \(t, tv) -> do
    for_ tv.tvClasses $ \klass -> do
      let instmap = fromMaybe mempty $ insts !? klass
      t `constrain` (klass, instmap)

  pure (tyvs, unions)


-- Should recursively map all the TVars in the type. (including in the unions.)
mapTVsWithMap :: Map (TVar TC) (Type TC) -> Map Def.UnionID T.EnvUnion -> Type TC -> Type TC
mapTVsWithMap tvmap unionmap =
  let
    mapTVs :: Type TC -> Type TC
    mapTVs = cata $ (.) embed $ \case
      t@(TO (TVar tv)) -> maybe t project (tvmap !? tv)
      TFun union ts tret -> TFun (fromMaybe (mapUnion union) (unionmap !? union.unionID)) ts tret
      TCon dd ts unions -> TCon dd ts $ unions <&> \union -> fromMaybe (mapUnion union) (unionmap !? union.unionID)
      t -> t

    mapUnion :: T.EnvUnion -> T.EnvUnion
    mapUnion u =
      let newUnion = u.union <&> \(muci, ufi, ts, env) -> (muci, ufi, mapTVs <$> ts, mapEnv tvmap unionmap env)
      in u { T.union = newUnion }
  in mapTVs

mapEnv :: Map (TVar TC) (Type TC) -> Map Def.UnionID T.EnvUnion -> T.Env -> T.Env
mapEnv tvmap unionmap = \case
    T.Env eid vars localities level -> T.Env eid (vars <&> fmap (mapTVsWithMap tvmap unionmap) . \(v, l, t) -> (mapVar v, l, t)) localities level
    e -> e
  where
    mapVar :: T.Variable -> T.Variable
    mapVar = \case
      T.DefinedClassFunction cfd snap self uci ->
        T.DefinedClassFunction cfd snap (mapTVsWithMap tvmap unionmap self) uci
      T.DefinedFunction fn assocs snap ufi -> T.DefinedFunction fn (mapTVsWithMap tvmap unionmap <$> assocs) snap ufi
      v -> v


-- This replaces the snapshot (available instances) for classes with a tvar in the set. Might be merged with mapTVsWithMap, but I'll have to make sure it's always used in the same context.
mapClassSnapshot :: Set (TVar TC) -> T.ScopeSnapshot -> Type TC -> Type TC
mapClassSnapshot tvs snapshot = mapType
  where
    mapType :: Type TC -> Type TC
    mapType = cata $ (.) embed $ \case
      TFun union args ret -> TFun (mapUnion union) args ret
      TCon dd ts unions -> TCon dd ts (mapUnion <$> unions)
      t -> t

    mapUnion :: T.EnvUnion -> T.EnvUnion
    mapUnion u =
      let newUnion = flip Def.fmap2 (T.union $ mapType <$> u) $ \case
            T.Env eid vars localities level -> T.Env eid (vars <&> \(v, l, t) -> (mapVar v, l, t)) localities level
            e -> e
      in u { T.union = newUnion }

    mapVar :: T.Variable -> T.Variable
    mapVar = (\case
      T.DefinedClassFunction cfd _ self@(Fix (TO (T.TVar tv))) uci | Set.member tv tvs -> T.DefinedClassFunction cfd snapshot self uci
      v -> v) . fmap mapType


-- Constructs an environment from all the instantiations.
--  We need the instantiations, because not all instantiations of a function can come up in the environment.
--  But, when there is a TVar in the type, it means all instantiated types of TVars must be there.
withEnv :: R.Env -> Infer (T.ClassInstantiationAssocs, a) -> Infer (T.Env, a)
withEnv renv x = do
  let eid = renv.envID
  Def.ctxPrint' $ printf "BEGIN ENV: %s" (pp renv)

  -- 1. clear environment - we only collect things from this scope.
  outOfEnvInstantiations <- RWS.gets instantiations

  -- 2. execute in scope.
  RWS.modify $ \s -> s { instantiations = Set.empty, envStack = eid : s.envStack }
  (ucis, x') <- x
  modifiedInstantiations <- RWS.gets instantiations


  -- 3. then filter the stuff that actually is from the environment
  --  TODO: this might not be needed, since we conditionally add an instantiation if it's FromEnvironment.
  renvQuery <- Map.fromList <$> traverse (\(v, l) -> (,l) <$> inferVariableProto v) (R.fromEnv renv)
  let newEnvVars
  --       = mapMaybe (\case
  --         { v@(T.DefinedClassFunction _ snapshot _ uci, loc, t) -> case ucis !? (Nothing, uci) of
  --           { Just (_, (typeApplication, ifn), level, ufi) -> if trace (printf "ENV REPLACE: %s: %d > %d" (pp ifn.instFunDec.functionId) renv.level level) (renv.level <= level)  -- BAD: literally same thing as replace function.
  --             then Nothing  -- throw away if the instance is from this function.
  --             else Just (T.DefinedFunction (Function ifn.instFunDec ifn.instFunBody) mempty typeApplication snapshot ufi, loc, t)
  --           ; Nothing -> Just v
  --           }
  --         ; v -> Just v
  --         })
        = mapMaybe (\(v, t) -> Map.lookup (T.asProto v) renvQuery <&> (v,,t)) $ Set.toList modifiedInstantiations

  Def.ctxPrint' $ Def.printf "OLD ENV: %s\nMODIFIED INSTANTIATIONS: %s\nRESULTING ENV: %s" (pp renv) (pp $ Set.toList modifiedInstantiations) (pp newEnvVars)


  -- 4. and put that filtered stuff back. ? NO. ONLY IN ENV DEFS. SO WE COPY THAT ENVIRONMENT THERE NIGGA. inferFunction can be called for normal variables.
  -- let usedInstantiations = Set.fromList $ fmap (\(v, _, t) -> (v, t)) newEnv
  RWS.modify $ \s -> s { instantiations = outOfEnvInstantiations, envStack = tail s.envStack }  -- NOTE: `tail` instead of `drop`, because if an empty list here must be a bug in the code.

  let newEnv = T.Env eid newEnvVars renvQuery renv.envStackLevel
  pure (newEnv, x')


addEnv :: T.Variable -> Type TC -> Infer ()
addEnv v t = RWS.modify $ \s -> s { instantiations = Set.insert (v, t) s.instantiations }


var :: Def.UniqueVar -> Infer (Type TC)
var v = do
  vars <- RWS.gets variableTypes
  case vars !? v of
    Just t -> pure t
    Nothing -> do
      t <- fresh
      RWS.modify $ \s -> s { variableTypes = Map.insert v t s.variableTypes }
      pure t


addMember :: Type TC -> Def.MemName -> Infer (Type TC)
addMember ogType memname = do
  t <- fresh  -- we don't know its type yet.
  RWS.modify $ \s -> s { memberAccess = (ogType, memname, t) : s.memberAccess }

  pure t


findBuiltinType :: Prelude.PreludeFind -> Infer (Type TC)
findBuiltinType (Prelude.PF tc pf) = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> pure $ pf p
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap tc (\(DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(DD _ scheme _ _) -> do
          (tvs, unions) <- instantiateScheme mempty scheme
          pure $ Fix $ TCon dd tvs unions
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."

mkPtr :: Type TC -> Infer (Type TC)
mkPtr insidePtr = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> pure $ p.mkPtr insidePtr
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap Prelude.ptrTypeName (\(DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(DD _ scheme _ _) -> do
          (tvs@[innerTyVar], unions) <- instantiateScheme mempty scheme
          innerTyVar `uni` insidePtr
          pure $ Fix $ TCon dd tvs unions

        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show Prelude.ptrTypeName <> "'."



-------------------------------
--        UNIFICATION

uni :: Type TC -> Type TC -> Infer ()
uni t1 t2 = do
  substituting $ do
    su <- RWS.gets ctxSubst
    let (t1', t2') = subst su (t1, t2)
    unify t1' t2'

uniMany :: [Type TC] -> [Type TC] -> Infer ()
uniMany ts1 ts2 =
  substituting $ do
    su <- RWS.gets ctxSubst
    let (ts1', ts2') = subst su (ts1, ts2)
    unifyMany ts1' ts2'

constrain :: Type TC -> (ClassDef TC, T.PossibleInstances) -> Infer ()
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

unify :: Type TC -> Type TC -> SubstCtx ()
unify ttl ttr = do
  su <- RWS.gets ctxSubst
  let (tl, tr) = subst su (ttl, ttr)
  case bimap project project $ subst su (tl, tr) of
    (l, r) | l == r -> pure ()
    (TO (TyVar tyv), _) -> do
      tyv `bind` tr
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint tr klass

    (_, TO (TyVar tyv)) -> do
      tyv `bind` tl
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint tl klass

    (TFun lenv lps lr, TFun renv rps rr) -> do
      unifyMany lps rps
      unify lr rr
      lenv `unifyFunEnv` renv

    (TCon t ta unions, TCon t' ta' unions') | t == t' -> do
      unifyMany ta ta'
      zipWithM_ unifyFunEnv unions unions'

    (_, _) -> do
      err $ TypeMismatch tl tr

unifyMany :: [Type TC] -> [Type TC] -> SubstCtx ()
unifyMany [] [] = nun
unifyMany (tl:ls) (tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
  unify tl tr
  unifyMany ls rs

unifyMany tl tr = err $ MismatchingNumberOfParameters tl tr

addConstraint :: Type TC -> (ClassDef TC, T.PossibleInstances) -> SubstCtx ()
addConstraint t (klass, instances) = case project t of
      TCon dd _ _ -> do
        let mSelectedInst = instances !? dd
        case mSelectedInst of
          Nothing -> do
            err $ DataDefDoesNotImplementClass dd klass

          Just _ -> do
            -- Don't do anything? like, we only have to confirm that the instance gets applied, right?
            pure ()

      TO (TVar tv) -> do
        unless (Set.member klass tv.tvClasses) $ do
          err $ TVarDoesNotConstrainThisClass tv klass

      TO (TyVar tyv) -> do
        -- create new tyvar with both classes merged!
        let cids = (klass, instances) : tyv.tyvConstraints
        newtyv <- freshTyVarInSubst cids
        tyv `bind` Fix (TO (TyVar newtyv))

      TFun {} ->
        err $ FunctionTypeConstrainedByClass t klass

bind :: T.TyVar -> Type TC -> SubstCtx ()
bind tyv (Fix (TO (TyVar tyv'))) | tyv == tyv' = nun
bind tyv t | occursCheck tyv t =
              err $ InfiniteType tyv t
           | otherwise = do
  RWS.modify $ \su -> su
    { ctxSubst =
        let singleSubst  = Subst mempty (Map.singleton tyv t)
            Subst unions types = subst singleSubst su.ctxSubst  -- NOTE: safe!
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

occursCheck :: Substitutable a => T.TyVar -> a -> Bool
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
  ftv :: a -> Set T.TyVar
  subst :: Subst -> a -> a


instance Substitutable Subst where
  ftv (Subst unions types) = ftv (Map.elems unions) <> Map.keysSet types <> ftv (Map.elems types)
  ftv (EnvAddition _) = mempty

  subst su (Subst unions types) = Subst (Map.map (subst su) unions) (Map.map (subst su) types)
  subst su (EnvAddition envAdds) = EnvAddition $ Def.fmap2 (\(v, l, t) -> (subst su v, l, subst su t)) envAdds



instance Substitutable (T.Mod TC) where
  -- TODO: We're not yet ftv-ing Datatypes, because it might lead to loops. Same with functions. I'll probably need another memoization system.
  ftv m = ftv m.topLevelStatements <> ftv m.exports -- <> ftv m.datatypes
  subst su m = T.Mod
    { T.topLevelStatements = subst su <$> m.topLevelStatements
    , T.exports = subst su m.exports

    -- , T.functions = subst su <$> m.functions
    -- , T.datatypes = m.datatypes -- subst su <$> m.datatypes
    -- , T.classes = subst su <$> m.classes
    -- , T.instances = subst su <$> m.instances
    }

instance Substitutable Int where
  ftv = mempty
  subst su = id

instance Substitutable (ClassDef TC) where
  ftv = mempty  -- no FTVs in declarations. will need to get ftvs from associated types and default functions when they'll be implemented.
  subst su cd = cd  -- TODO: not sure if there is anything to sueid bstitute.

instance Substitutable (InstDef TC) where
  ftv inst = foldMap ftv inst.instFuns
  subst su inst = inst
    { instFuns = subst su inst.instFuns
    }

instance Substitutable (InstFun TC) where
  ftv ifn = ftv ifn.instFunDec <> ftv ifn.instFunBody
  subst su ifn = ifn
    { instFunDec = subst su ifn.instFunDec
    , instFunBody = subst su ifn.instFunBody
    }

instance Substitutable (Exports TC) where
  ftv e = ftv e.functions
  subst su e = e { functions = subst su e.functions }

instance Substitutable (AnnStmt TC) where
  ftv = cata $ \(O (Def.Annotated _ stmt)) -> case first ftv stmt of
    Return ret -> ftv ret
    Mutation _ _ accesses e -> ftv accesses <> e
    s -> bifold s

  subst su = cata $ embed . sub
    where
      sub (O (Def.Annotated ann stmt)) = O . Def.Annotated ann $ case stmt of
        Switch cond cases ->
          let cond' = subst su cond
              cases' = subst su cases
          in Switch cond' cases'
        Fun env -> Fun $ subst su env
        Inst inst -> Inst $ subst su inst
        Return ret -> Return  $ subst su ret
        Mutation v other accesses e -> Mutation v other (subst su accesses) (subst su e)
        s -> first (subst su) s

instance Substitutable (MutAccess TC) where
  ftv = const mempty
  subst _ = id

instance (Substitutable expr, Substitutable stmt) => Substitutable (CaseF TC expr stmt) where
  ftv kase = ftv kase.deconstruction <> ftv kase.caseCondition <> ftv kase.caseBody
  subst su kase = Case (subst su kase.deconstruction) (subst su kase.caseCondition) (subst su kase.caseBody)

instance Substitutable (Decon TC) where
  ftv = cata $ \(N t d) -> ftv t <> case d of
    CaseVariable _ -> mempty
    CaseConstructor _ ftvs -> mconcat ftvs
    CaseRecord _ ftvs -> foldMap snd ftvs
  subst su = hoist $ \(N t d) -> N (subst su t) $ case d of
    CaseVariable v -> CaseVariable (subst su v)
    CaseConstructor uc ds -> CaseConstructor uc ds
    CaseRecord dd ds -> CaseRecord dd ds

instance Substitutable (Expr TC) where
  ftv = cata $ \(N et ee) -> ftv et <> case ee of
    As e t -> e <> ftv t
    Lam env params body -> ftv env <> ftv params <> body
    Var v _ -> ftv v
    e -> fold e
  subst su = hoist $ \(N et ee) -> N (subst su et) (case ee of
    As e t -> As e (subst su t)
    Lam env params body -> Lam (subst su env) (subst su params) body
    Var v loc -> Var (subst su v) loc
    e -> e)

instance Substitutable T.LamDec where
  ftv (T.LamDec _ env) = ftv env
  subst su (T.LamDec uv env) = T.LamDec uv (subst su env)

instance Substitutable T.Variable where
  ftv _ = mempty
  subst su (T.DefinedFunction fn assocs ss ufi) = T.DefinedFunction (subst su fn) (subst su assocs) ss ufi  -- note the bad resubstituting.
  subst su (T.DefinedClassFunction cfd insts self uci) = T.DefinedClassFunction cfd (Def.fmap2 (subst su) insts) (subst su self) uci
  subst _ x = x


instance Substitutable Def.UniqueVar where
  ftv _ = mempty
  subst _ = id

instance Substitutable Def.UniqueClassInstantiation where
  ftv _ = mempty
  subst _ = id

instance Substitutable Def.MemName where
  ftv _ = mempty
  subst _ = id

instance Substitutable Def.UniqueFunctionInstantiation where
  ftv _ = mempty
  subst _ = id



instance Substitutable (Function TC) where
  ftv fn = ftv fn.functionBody \\ ftv fn.functionDeclaration
  subst su fn = Function { functionDeclaration = subst su fn.functionDeclaration, functionBody = subst su fn.functionBody }

instance Substitutable (FunDec TC) where
  ftv (FD _ _ params ret other) = ftv params <> ftv ret <> ftv other.functionAssociations -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 
  subst su (FD env fid params ret other) = FD (subst su env) fid (subst su params) (subst su ret) (subst su other)

instance Substitutable T.FunOther where
  ftv other = ftv other.functionAssociations
  subst su other = T.FunOther other.functionScheme (subst su other.functionAssociations)

instance Substitutable T.TypeAssociation where
  ftv (T.TypeAssociation from to _ _ _ _) = ftv from <> ftv to
  subst su (T.TypeAssociation from to c uci ufi envs) = T.TypeAssociation (subst su from) (subst su to) c uci ufi envs

-- -- FIX: FUCK
-- instance Substitutable a => Substitutable (IORef a) where
--   ftv ioref = ftv $ unsafePerformIO $ IORef.readIORef ioref
--   subst su ioref = unsafePerformIO $ do
--     IORef.modifyIORef ioref (subst su)
--     pure ioref

instance Substitutable T.FunctionTypeAssociation where
  ftv (T.FunctionTypeAssociation _ to _ _) = ftv to
  subst su (T.FunctionTypeAssociation from to c uci) = T.FunctionTypeAssociation from (subst su to) c uci

instance Substitutable (Type TC) where
  ftv = cata $ \case
    TO (TyVar tyv) -> Set.singleton tyv
    t -> fold t

  subst su = cata $ embed . \case
    TO (TyVar tyv) -> case su of
      Subst _ tyvm -> case tyvm !? tyv of
        Nothing -> TO $ T.TyVar tyv
        Just t -> project t

      _ -> TO (TyVar tyv)

    -- we might need to substitute the union thing
    TFun ogUnion ts t ->

      -- might need to replace the union
      let union = subst su ogUnion

      in TFun union ts t

    TCon ut cons unions -> TCon ut cons (subst su unions)

    t -> t

instance Substitutable (T.EnvUnionF (Type TC)) where
  ftv (T.EnvUnion _ envs) = ftv envs
  subst su@(Subst unions _) (T.EnvUnion uid envs) = do
    case unions !? uid of
      Just suUnion -> suUnion
      Nothing -> T.EnvUnion uid $ subst su envs

  subst su (T.EnvUnion uid envs) = T.EnvUnion uid $ subst su envs


instance Substitutable (T.EnvF (Type TC)) where
  ftv (T.Env _ vars _ _) = foldMap (\(_, _, t) -> ftv t) vars
  ftv (T.RecursiveEnv _ _) = mempty

  -- redundant work. memoize this shit also.
  subst su (T.Env eid env locs currentEnvStack) = T.Env eid (newEnvVars <> optionalAddition) locs currentEnvStack
    where
      newEnvVars = foldMap (tryExpandEnvironmentOfClass . (\(v, l, t) -> (subst su v, l, subst su t))) env 

      currentLevel = Def.envStackToLevel currentEnvStack

      optionalAddition :: [(T.Variable, Def.Locality, Type TC)]
      optionalAddition = case su of
        EnvAddition adds ->
          let oldVars = Set.fromList newEnvVars
          in filter (`Set.notMember` oldVars) $ fmap (\(v, l, t) -> (subst su v, l, subst su t)) $ fromMaybe mempty $ adds !? eid
        _ -> mempty

      tryExpandEnvironmentOfClass :: (T.Variable, Def.Locality, Type TC) -> [(T.Variable, Def.Locality, Type TC)]
      tryExpandEnvironmentOfClass = \case
        vlt@(T.DefinedClassFunction cfd@(CFD cd _ _ _) snap self@(Fix (TCon dd _ _)) uci, _, t) ->
          -- failable: select instantiated function env. this might have been after errors, so we're not assuming anything.
          let mvars = do
                insts <- snap !? cd
                currentInst <- insts !? dd
                currentFun <- find (\ifn -> ifn.instClassFunDec == cfd) currentInst.instFuns

                unT <- case project t of
                  TFun union _ _ -> Just union.union
                  _ -> Nothing
                (_, ufi, assocs, e) <- find (\case { (Just uci', _, _, _) -> uci == uci'; _ -> False }) unT
                pure (currentFun, currentInst, ufi, assocs, e)
          in case mvars of
            -- this probably is not needed anymore!
            Just (ifn, currentInst, ufi, assocs, T.Env instEnvID instEnvVars _ instEnvStack)
              -- this function is from this or "higher" environment.
              -- | Def.envStackToLevel instEnvStack <= currentLevel ->
              | instEnvStack `Def.isHigherOrSameLevel` currentEnvStack ->
              -- | Set.member instEnvID (Set.fromList (eid : currentEnvStack)) ->
                let fnLocality = if Def.envStackToLevel instEnvStack < currentLevel
                      then Def.FromEnvironment (Def.envStackToLevel instEnvStack)
                      else Def.Local
                in [(T.DefinedClassFunction cfd snap self uci, fnLocality, t)]  -- TEMP: we are redoing the "DefinedClassFunction" (instead of just dropping DefinedFunction), because currently in Mono we rely on this.
                -- NOTE: NOTICE THAT WE TAKE currentInst instead of using the recursive instance. This is because we don't substitute recursive instances (because we have no memoization).

              -- we need "take out" variables from this function.
              -- NOTE: we add the `eid` to currentEnvStack, because if inst is actually INSIDE the function, it would have `eid` in its env stack. We need it, because (due to how insts are resolved) we might have an instance from a completely different place, which will need to leave alone and create an env mod for it.
              | (eid : currentEnvStack) `Def.isHigherOrSameLevel` instEnvStack -> []  -- NOTE: this is taken care of in `addExtraToEnv` and `EnvAdditions`

              | otherwise -> [vlt]  -- do not touch it. might be a class function from a different scope and will need to be "completed."
                -- let
                --   usedVarsInThisEnv = Set.fromList $ env <&> \(v, _, t) -> (v, t)
                --   usedVarsInInst = unpackFromEnvironment instLevel instEnvVars
                --   usedVarsInInstDeduped = filter (\(v, _, t) -> Set.notMember (v, t) usedVarsInThisEnv) usedVarsInInst
                -- in usedVarsInInstDeduped

            _ -> [vlt]  -- there was an error probably.
        vlt -> [vlt]
      -- (\(v, l, t) -> (subst su v, l, subst su t))
      -- RELATED TO "nonlocal instances and their environments"
      unpackFromEnvironment :: Def.Level -> [(T.Variable, Def.Locality, Type TC)] -> [(T.Variable, Def.Locality, Type TC)]
      unpackFromEnvironment instEnvLevel
        = map (\(v, l, t) ->             -- adjust locality from the context of this environment.
            let varLevel = case l of
                  Def.Local -> instEnvLevel
                  Def.FromEnvironment lev -> lev
                newLocality = if varLevel == currentLevel
                  then Def.Local
                  else Def.FromEnvironment varLevel
            in (v, newLocality, t))
        . filter (\(_, l, _) ->          -- filter variables, which should not even be in this environment.
            let varLevel = case l of
                  Def.Local -> instEnvLevel
                  Def.FromEnvironment lev -> lev
            in varLevel <= currentLevel)

  subst su env = subst su <$> env


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

instance (Substitutable a, Substitutable b, Substitutable c, Substitutable d) => Substitutable (a, b, c, d) where
  ftv (a, b, c, d) = ftv a <> ftv b <> ftv c <> ftv d
  subst su (a, b, c, d) = (subst su a, subst su b, subst su c, subst su d)

instance Substitutable a => Substitutable (Maybe a) where
  ftv = maybe mempty ftv
  subst su = fmap (subst su)




-----------------
----- Smol

-- Make new union ID.
newUnionID :: MonadIO io => io Def.UnionID
newUnionID = Def.UnionID <$> liftIO newUnique

newClassInstantiation :: Infer Def.UniqueClassInstantiation
newClassInstantiation = Def.UCI <$> liftIO newUnique

newFunctionInstantiation :: Infer Def.UniqueFunctionInstantiation
newFunctionInstantiation = Def.UFI <$> liftIO newUnique

-- Returns a fresh new tyvare
fresh :: Infer (Type TC)
fresh = Fix . TO . T.TyVar <$> freshTyVar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyVar :: Infer T.TyVar
freshTyVar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV (letters !! nextVar) mempty

freshTyVarInSubst :: [(ClassDef TC, T.PossibleInstances)] -> SubstCtx T.TyVar
freshTyVarInSubst cdis = do
  TVG nextVar <- RWS.gets ctxTvargen
  RWS.modify $ \s -> s { ctxTvargen = TVG (nextVar + 1) }
  pure $ T.TyV (letters !! nextVar) cdis

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']


singleEnvUnion :: Maybe Def.UniqueClassInstantiation -> Def.UniqueFunctionInstantiation -> [Type TC] -> T.Env -> Infer T.EnvUnion
singleEnvUnion uci ufi tassocs env = do
  uid <- newUnionID
  pure T.EnvUnion { T.unionID = uid, T.union = [(uci, ufi, tassocs, env)] }

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
  , returnType :: Maybe (Type TC)
  }

data SubstState = SubstState
  { ctxSubst :: Subst
  , ctxTvargen :: TVarGen
  }


data TypecheckingState = TypecheckingState
  { tvargen :: TVarGen

  -- current state of substitution.
  , typeSubstitution :: Subst

  , memoFunction :: Memo (Function R) (Function TC)
  , memoDataDefinition :: Memo (DataDef R) (DataDef TC)
  , memoClass :: Memo (ClassDef R) (ClassDef TC)
  , memoInstance :: Memo (InstDef R) (InstDef TC)

  , variableTypes :: Map Def.UniqueVar (Type TC)

  , memberAccess :: [(Type TC, Def.MemName, Type TC)]  -- ((a :: t1).mem :: t2)
  , classFunctionUnions :: [(T.EnvUnion, ClassFunDec TC, Type TC, T.PossibleInstances)]  -- TODO: currently unused. remove later.
  , associations :: [(T.TypeAssociation, Map (DataDef TC) (InstDef TC))]

  -- HACK?: track instantiations from environments. 
  --  (two different function instantiations will count as two different "variables")
  , instantiations :: Set (T.Variable, Type TC)

  , envStack :: [Def.EnvID]
  , envAdditions :: Map Def.EnvID [(T.Variable, Def.Locality, Type TC)]
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

  , variableTypes = mempty

  , instantiations = mempty
  , classFunctionUnions = mempty
  , associations = mempty

  , envStack = mempty
  , envAdditions = mempty
  }



newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst
  -- normal subst
  = Subst (Map Def.UnionID T.EnvUnion) (Map T.TyVar (Type TC))

  -- later used to append extra stuff to environments.
  | EnvAddition EnvAdditions

emptySubst :: Subst
emptySubst = Subst mempty mempty


type EnvAdditions = Map Def.EnvID [(T.Variable, Def.Locality, Type TC)]


data TypeError
  = InfiniteType T.TyVar (Type TC)
  | TypeMismatch (Type TC) (Type TC)
  | MismatchingNumberOfParameters [Type TC] [Type TC]
  | AmbiguousType T.TyVar

  | DataTypeDoesNotHaveMember (DataDef TC) Def.MemName
  | DataTypeIsNotARecordType (DataDef TC) Def.MemName
  | FunctionIsNotARecord (Type TC) Def.MemName
  | TVarIsNotARecord (TVar TC) Def.MemName

  | DataDefDoesNotImplementClass (DataDef TC) (ClassDef TC)
  | TVarDoesNotConstrainThisClass (TVar TC) (ClassDef TC)
  | FunctionTypeConstrainedByClass (Type TC) (ClassDef TC)

-- not sure if we have to have a show instance
instance Show TypeError where
  show = \case
    InfiniteType tyv t -> unwords ["InfiniteType", sctx $ pp tyv, sctx $ pp t]
    TypeMismatch t t' -> printf "Type Mismatch: %s %s" (sctx $ pp t) (sctx $ pp t')
    MismatchingNumberOfParameters ts ts' -> printf "Mismatching number of parameters: (%d) %s (%d) %s" (length ts) (sctx $ Def.ppList pp ts) (length ts') (sctx $ Def.ppList pp ts')
    AmbiguousType tyv -> printf "Ambiguous type: %s" (sctx $ pp tyv)

    DataTypeDoesNotHaveMember (DD ut _ _ _) memname -> printf "Record type %s does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
    DataTypeIsNotARecordType (DD ut _ _ _) memname -> printf "%s is not a record type and thus does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
    FunctionIsNotARecord t _ -> printf "Cannot subscript a function (%s)." (pp t)
    TVarIsNotARecord tv _ -> printf "Cannot subscript a type variable. (%s)" (pp tv)
    DataDefDoesNotImplementClass (DD ut _ _ _) cd -> printf "Type %s does not implement instance of class %s." (sctx $ pp ut) (sctx $ pp cd.classID)
    TVarDoesNotConstrainThisClass tv cd -> printf "TVar %s is not constrained by class %s." (pp tv) (pp cd.classID)
    FunctionTypeConstrainedByClass t cd ->
      printf "Function type %s constrained by class %s (function types cannot implement classes, bruh.)" (pp t) (pp cd.classID)




-----
-- DEBUG
----

dbgSubst :: Subst -> String
dbgSubst (Subst unions ts) =
  let tvars = Map.toList ts <&> \(ty, t) -> printf "%s => %s" (Def.ctx ty) (Def.ctx t)
      unionRels = Map.toList unions <&> \(uid, union) -> printf "%s => %s" (Def.ctx uid) (Def.ctx union)
  in unlines $ tvars <> ["--"] <> unionRels

dbgSubst (EnvAddition envAdds) = fromString $ Def.ctx $ Def.ppMap $ fmap (bimap pp pp) $ Map.toList envAdds

dbgAssociations :: MonadIO io => String -> [(T.TypeAssociation, Map (DataDef TC) (InstDef TC))] -> io ()
dbgAssociations title associations = liftIO $ Def.ctxPrint' $ printf "Associations (%s): %s" title (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation from to _ uci ufi _, _) -> printf "(%s) %s: %s" (pp (uci, ufi)) (pp from) (pp to) :: String)

