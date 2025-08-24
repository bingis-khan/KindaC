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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Typecheck (typecheck, TypeError(..)) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map.Strict (Map, (!?))
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.RWS.Strict (RWST (RWST), runRWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (Base, cata, embed, hoist, project, para)
import Control.Monad (replicateM, zipWithM_, unless, when, (<=<), (>=>))
import Data.Bitraversable (bitraverse)
import Data.Foldable (for_, fold, foldlM)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Bifunctor (bimap)
import Data.List ( find, partition )
import Data.Bifoldable (bifoldMap, bifold)
import Data.Traversable (for)


import qualified AST.Resolved as R
import qualified AST.Typed as T

import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe, catMaybes)
import Control.Applicative (liftA3)
import Data.List.NonEmpty (NonEmpty)
import Misc.Memo (memo, Memo(..), emptyMemo)
import qualified AST.Common as Common
import AST.Prelude (Prelude)
import qualified AST.Prelude as Prelude
import AST.Common (Module, AnnStmt, StmtF (..), Type, CaseF (..), ExprF (..), ClassFunDec (..), DataCon (..), DataDef (..), ClassType, ClassTypeF (..), TypeF (..), TVar (..), Function (..), functionEnv, Exports (..), ClassDef (..), InstDef (..), InstFun (..), functionOther, FunDec (..), Decon, DeconF (..), IfStmt (..), Expr, ExprNode (..), DeclaredType (..), XClassFunDec, MutAccess (..), LitType (..), asksNode)
import AST.Resolved (R)
import AST.Typed ( TC, Scheme(..), TOTF(..), T )
import AST.Def ((:.)(..), PP (..), Binding (..), BinOp (..), pf, PrintContext, pc, ppDef, fmap2, traverse2)
import qualified AST.Def as Def
import Data.String (fromString)
import Error (Error (..), renderError)
import AST.Typed (FunOther(..))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Monad.Trans.Class (lift)
import Text.Megaparsec (sourceColumn)
import Text.Megaparsec.Pos (unPos)
import Text.Megaparsec (sourceLine)
import CompilerContext (CompilerContext (CompilerContext))
import qualified CompilerContext
import Control.Monad.Trans.Reader (Reader)
import qualified Control.Monad.Trans.Reader as Reader
import CompilerContext (CompilerState(..))
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.IntMap.Strict as IntMap



----------- TO REMEMBER -----------------
-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)

------------- Another rewrite
-- Two phases:
--  1. assign types
--    TODO: (we'll have to think of where to put the envaddition!!!!)
--  2. expand environment n replace types (this won't happen here, but at the end of compiler context kekek)

typecheck :: Maybe Prelude -> Module R -> CompilerContext ([TypeError], Module TC)
typecheck mprelude rStmts = {-# SCC typecheck #-} do
    let tcContext = Ctx { prelude = mprelude, returnType = Nothing, shouldPrintUnification = Nothing }
    let senv = emptySEnv  -- we add typechecking state here, because it might be shared between modules? (especially memoization!)... hol up, is there anything to even share?

    -- Step 1: Generate type substitution (typing context) based on the constraints.
    (tStmts, errs) <- generateSubstitution tcContext senv rStmts

    Def.phase "Typechecking (Before substitution)"
    pc tStmts

    ----- Step 1.25
    -- Now add those extra variables to all them envs.
    -- let envSu = subst su $ EnvAddition envAdds  -- after this, env addition might STILL have some tyvars left over, but this will be fixed by the final substitution (which will just work on the new environments!)
    Def.phase "State of unis"
    pc =<< CompilerContext.getTypeUni


    ----- Step 1.5: Substitute tyvars in Subst's unions, because they are not actively substituted yet?
    -- HACK: I didn't check it when that happens, so I'll do it at the end.
    --  Unions that are to be substituted may have unsubstituted parameters. This should quickly fix that. However, I'm not sure where this happens. So, this is a TODO to figure out why this happens and when.
    -- ISSUE(function-tvars-in-its-env)
    -- let Subst suUnions suTVs = su
    -- let suNoUnions = Subst mempty suTVs
    -- let suUnions' = subst suNoUnions . subst envSu <$> suUnions
    -- let su' = Subst suUnions' suTVs


    -- Def.phase "Typechecking (og subst)"
    -- pc $ dbgSubst su

    -- Def.phase "Typechecking (fixed subst)"
    -- pc $ dbgSubst su'


    -- Step 2: Substitute the types with the inferred ones.
    -- let tStmts'' = subst su' tStmts'
    ftvs <- Set.map snd <$> findFTV tStmts
    let errs' = errs <> (AmbiguousType (error "what location should i put here???") <$> Set.toList ftvs)


    Def.phase "Typechecking (After Substitution)"
    -- pc tStmts''



    pure (errs', tStmts)


---------------------------
--      INFERENCE        --
---------------------------

generateSubstitution :: Context -> TypecheckingState -> Module R -> CompilerContext (Module TC, [TypeError])
generateSubstitution env senv rModule = do
  (tvModule, s, errors) <- runRWST infer env senv

  pure (tvModule, errors)
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
      -- pc cia

      assocs <- RWS.gets associations
      pf "LAST ASSOCS: %" (pp $ fst <$> assocs) :: Infer ()
      -- su <- RWS.gets typeSubstitution
      reportAssociationErrors
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
    inferAnnStmt :: (PP a, Substitutable a) => Base (AnnStmt R) (Infer a) -> Infer (Base (AnnStmt TC) a)
    inferAnnStmt (O (O (Def.Annotated anns (Def.Located location rStmt)))) = printUni (unPos location.startPos.sourceLine) anns $ do
        tstmt <- bitraverse inferExpr id rStmt

        -- Map expr -> type for unification
        let ttstmt = first (\expr@(Fix (N en _)) -> (expr, en.t)) tstmt
        stmt'''@(O (O (Def.Annotated _ (Def.Located _ stmt''''')))) <- O . O . Def.Annotated anns . Def.Located location <$> inferStmt location ttstmt
        -- su <- RWS.gets typeSubstitution
        whenPrintingUni $ pf "STMT: %" stmt'''
        -- whenPrintingUni $ pf "STMT: %" (subst su (stmt'''''))
        pure stmt'''

    inferStmt :: Def.Location -> StmtF R (Expr TC, Type TC) a -> Infer (StmtF TC (Expr TC) a)
    inferStmt location stmt = case stmt of

      Assignment v varLocation (rexpr@(Fix (N en _)), t) -> do
        vt <- var v
        (varLocation, vt) `uni` (Just en.loc, t)

        pure $ Assignment v varLocation rexpr


      Mutation v varLocation loc accesses (expr@(Fix (N ne _)), t) -> do
        vt <- var v

        case loc of
          Def.Local -> pure ()
          Def.FromEnvironment {} ->
            addEnv (T.DefinedVariable v) vt

        -- prepare accesses for typechecking.
        taccesses <- for accesses $ \case
              MutRef loc -> (MutRef loc,) <$> fresh
              MutField loc mem -> (MutField loc mem,) <$> fresh

        let
          maybeConcat :: Maybe Def.Location -> Def.Location -> Def.Location
          maybeConcat Nothing = id
          maybeConcat (Just s) = (s <>)

          foldMutAccess :: (Type TC, Maybe Def.Location) -> (MutAccess TC, Type TC) -> Infer (Type TC, Maybe Def.Location)
          foldMutAccess (rightType, mloc) = \case
            (MutRef location, accessT) -> do
              ptrT <- mkPtr rightType
              let newLoc = maybeConcat mloc location
              (location, ptrT) `uni` (Just newLoc, accessT)
              pure (ptrT, Just newLoc)
            (MutField location mem, recordType) -> do
              fieldType <- addMember location recordType mem
              let newLoc = maybeConcat mloc location
              (location, fieldType) `uni` (Just newLoc, rightType)
              pure (recordType, Just newLoc)

        -- we must build the type access by access, from RIGHT to LEFT.
        --  that's why it's reversed.
        -- ex: <&.dupa= 420
        --    the field 'dupa' has type Int, so
        --     type 420 == addMember fresh "dupa"
        --    then, we deref x, so the current type is the derefed value.
        --     type x `uni` mkPtr t
        --  get it?
        (guessedType, _) <- foldlM foldMutAccess (t, Nothing) (reverse taccesses)

        (varLocation, vt) `uni` (Just ne.loc, guessedType)
        pure $ Mutation v varLocation loc taccesses expr


      If (IfStmt { condition = (cond, condt), ifTrue, ifElifs, ifElse }) -> do
        boolt <- findBuiltinType Prelude.boolFind

        (asksNode T.loc cond, condt) `uni` (Nothing, boolt)

        for_ ifElifs $ \((elifCond, t), _) ->
          (asksNode T.loc elifCond, t) `uni` (Nothing, boolt)

        pure $ If $ IfStmt cond ifTrue ((fmap . first) fst ifElifs) ifElse


      Switch (rswitch, switchType) cases -> do
        -- infer the type for the expression inserted into the switch...
        tdecons <- traverse inferCase cases

        for_ tdecons $ \(_, dect) ->
          -- ...each deconstruction should be of that type.
          let tempLoc = asksNode T.loc rswitch
          in (asksNode T.loc rswitch, switchType) `uni` (Just tempLoc, dect)

        pure $ Switch rswitch (fst <$> tdecons)
        where

          inferCase Case { deconstruction = decon, caseCondition = caseCon, caseBody = body } = do
            tdecon <- inferDecon decon
            let tCaseCon = fst <$> caseCon
            pure (Case tdecon tCaseCon body, asksNode T.t tdecon)


      Return rret -> do
        pf "uu"
        ret <- inferExpr rret
        emret <- RWS.asks returnType
        pf "miau"
        eret <- maybe (findBuiltinType Prelude.tlReturnFind) pure emret  -- NOTE: When default return type is nothing, this means that we are parsing prelude. Return type from top level should be "Int" (or, in the future, U8).
        pf "ooo"
        asksNode (\ne -> (ne.loc, ne.t)) ret `uni` (Nothing, eret)
        pf "aaaa"
        pure $ Return ret

      While (cond, condt) body -> do
        boolt <- findBuiltinType Prelude.boolFind
        (asksNode T.loc cond, condt) `uni` (Nothing, boolt)

        pure $ While cond body


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
    inferExprType (N location e) = do
      pf "before layer"
      (e', t) <- inferLayer
      pf "after layer"
      pure $ N (T.ExprNode t location) e' where

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
            -- su <- RWS.gets typeSubstitution
            -- replacedBody <- replaceInExpr su classInstantiationAssocs exprBody

            pure (classInstantiationAssocs, exprBody)

          -- be sure to copy the environment HERE!
          let varsFromNestedFun = case fenv of
                T.Env _ venv _ _ -> Set.fromList $ venv <&> \(v, _, t) -> (v, t)
                _ -> error "FUKKK"

          RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

          ufi <- newFunctionInstantiation  -- i guess we don't really need to save that tho.
          union <- singleEnvUnion Nothing ufi [] fenv
          let ret = asksNode T.t body'
          t <- mkType $ TFun union argts ret

          pure (Lam (T.LamDec uv fenv) args' body', t)


        As ae t -> do
          e' <- ae
          t' <- inferType t

          askUni e' `uni` (error "when type defs have location information, add it here", t')

          pure (As e' t', t')


        Lit lt -> do
          t <- case lt of
            LInt {} -> findBuiltinType Prelude.intFind
            LFloat {} -> findBuiltinType Prelude.floatFind
            LString {} -> findBuiltinType Prelude.constStrFind
          pure (Lit $ Common.relit id lt, t)


        Var v loc -> do
          (t, v') <- instantiateVariable location loc =<< inferVariable location v

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
            mt <- addMember location t name
            askUni me `uni` (Nothing, mt)

          pure (RecCon dd' insts', t)


        RecUpdate re updates -> do
          te <- re
          updates' <- Def.sequenceA2 updates

          -- the type can be whatever, so we couldn't check these fields in the resolver ISSUE(anonymous-records)
          for_ updates' $ \(mem, me) -> do
            memt <- addMember (error "add location to member") (asksNode T.t te) mem
            askUni me `uni` (Just (error "add location to member"), memt)

          pure (RecUpdate te updates', asksNode T.t te)

        MemAccess re memname -> do
          te <- re

          -- by now, we don't know the type of the member, because it's possible to define multiple members with the same name.
          t <- addMember location (asksNode T.t te) memname

          pure (MemAccess te memname, t)

        BinOp il op ir -> do
          l <- il
          r <- ir

          let lt = askUni l
              rt = askUni r

          t <- if op == NotEquals || op == Equals
            then do
              lt `uni` first Just rt
              findBuiltinType Prelude.boolFind

            else if op `elem` [LessThan, LessEqual, GreaterThan, GreaterEqual]
            then do
              intt <- findBuiltinType Prelude.intFind
              lt `uni` justType intt
              rt `uni` justType intt
              findBuiltinType Prelude.boolFind

            else if op `elem` [And, Or]
            then do
              boolt <- findBuiltinType Prelude.boolFind
              lt `uni` justType boolt
              rt `uni` justType boolt
              pure boolt

            else do
              -- should be a better error. for example "in addition, ..."
              intt <- findBuiltinType Prelude.intFind
              lt `uni` justType intt
              rt `uni` justType intt
              pure intt

          pure (BinOp l op r, t)


        Call callee args -> do
          pf "call"
          args' <- sequenceA args
          let argts = askType <$> args'
          -- argfs <- for argts $ const fresh  -- fresh variables for better errors.
          pf "what"
          callee' <- callee

          pf "ca"
          ret <- fresh
          union <- emptyUnion
          pf "cb"
          ft <- mkType $ TFun union argts ret

          -- pretty bad errors for calls.
          pf "cc"
          askUni callee' `uni` (Just location, ft)  -- first unify the whole function shape.

          -- then, unify specific arguments.
          -- WHAT: or I would do it, but it don't work for one test. why???? there's something funny going on with the typechecker again?
          -- for_ (zip argts ((Nothing,) <$> argfs)) $ uncurry uni

          -- TODO: in the future, make a special function for calls, which will signal nice errors.

          pure (Call callee' args', ret)

        UnOp Def.Not ee -> do
          boolType <- findBuiltinType Prelude.boolFind
          re <- ee
          let t = askUni re

          t `uni` justType boolType

          pure (UnOp Def.Not re, boolType)

        UnOp Def.Negation ee -> do
          intType <- findBuiltinType Prelude.intFind
          re <- ee
          let t = askUni re

          t `uni` justType intType
          pure (UnOp Def.Negation re, intType)

        UnOp Def.Ref ee -> do
          te <- ee
          let t = askType te
          ptrType <- mkPtr t
          pure (UnOp Def.Ref te, ptrType)

        UnOp Def.Deref ee -> do
          te <- ee
          let t = askUni te

          insidePtr <- fresh
          ptrType <- mkPtr insidePtr
          (location, ptrType) `uni` first Just t
          pure (UnOp Def.Deref te, insidePtr)



inferVariable :: Def.Location -> R.Variable -> Infer T.Variable
inferVariable location = \case
  R.DefinedVariable v -> pure $ T.DefinedVariable v
  R.ExternalVariable v _ -> pure $ T.DefinedVariable v  -- TODO: CURRENTLY BROKEN. THE TYPE SHOULD BE PASSED.

  R.ExternalFunction fn rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    pure $ T.DefinedFunction fn mempty snapshot tempFunctionInstantiation

  R.DefinedFunction fn rsnapshot -> do
    tfn <- inferFunction fn
    snapshot <- inferSnapshot rsnapshot
    pure $ T.DefinedFunction tfn mempty snapshot tempFunctionInstantiation

  R.ExternalClassFunction cfd@(CFD cd _ _ _ () _) rsnapshot -> do
    -- insts <- fmap Map.fromList $ for (Map.toList (rinsts ! )) $ \(rdd, rinst) -> do
    --   dd <- inferDatatype rdd
    --   inst <- case rinst of
    --     R.DefinedInst rists  -> inferInstance rists
    --     R.ExternalInst tinst -> pure tinst
    --   pure (dd, inst)
    snapshot <- inferSnapshot rsnapshot
    let insts = Def.defaultEmpty cd snapshot

    self <- fresh
    let constr = constrain location
    self `constr` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self tempClassInstantiation

  R.DefinedClassFunction rcfd rsnapshot -> do
    cfd@(CFD cd _ _ _ () _) <- inferClassDeclaration rcfd
    -- insts <- fmap Map.fromList $ traverse (bitraverse inferDatatype inferInstance) $ Map.toList rinsts
    snapshot <- inferSnapshot rsnapshot
    let insts = Def.defaultEmpty cd snapshot

    self <- fresh
    let constr = constrain location
    self `constr` (cd, insts)

    pure $ T.DefinedClassFunction cfd snapshot self tempClassInstantiation

tempFunctionInstantiation :: Def.UniqueFunctionInstantiation
tempFunctionInstantiation = error "should not evaluate"

tempClassInstantiation :: Def.UniqueClassInstantiation
tempClassInstantiation = error "should not evaluate"

inferSnapshot :: R.ScopeSnapshot -> Infer (T.ScopeSnapshot TC)
inferSnapshot = Def.bitraverseMap inferClass inferPossibleInstances
  where
    inferPossibleInstances :: R.PossibleInstances -> Infer (T.PossibleInstances TC)
    inferPossibleInstances = Def.bitraverseMap inferDatatype inferInst

inferVariableProto :: R.VariableProto -> Infer T.VariableProto
inferVariableProto = \case
  R.PDefinedVariable v -> pure $ T.PDefinedVariable v
  R.PExternalVariable v _ -> pure $ T.PDefinedVariable v

  R.PExternalFunction fn -> pure $ T.PDefinedFunction fn
  R.PDefinedFunction fn -> T.PDefinedFunction <$> inferFunction fn

  R.PExternalClassFunction cfd -> pure $ T.PDefinedClassFunction cfd
  R.PDefinedClassFunction  cfd -> do
    T.PDefinedClassFunction <$> inferClassDeclaration cfd


inferConstructor :: R.Constructor -> Infer (DataCon TC)
inferConstructor = resetUniPrint . \case
  R.ExternalConstructor c -> pure c
  R.DefinedConstructor (DC rdd uc _ _) -> do
    (DD _ _ cons _) <- inferDataDef rdd

    -- HACK?: Find constructor through memoized DataDefinition.
    pure $ Def.mustOr (pf "[Compiler Error] Could not find constructor %." uc) $
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
      pure $ TCon dd params []  -- maybe should be undefined??
    TCon (R.ExternalDatatype dd) rparams () -> do
      params <- sequenceA rparams
      pure $ TCon dd params []  -- maybe should be undefined??
    TO (R.TClass rcd) -> do
      cd <- inferClass rcd
      t <- fresh
      let constr = constrain (error "todo (should come from class type)")
      t `constr` (cd, mempty)  -- NOTE: we MUST ensure that this turns into a TVar. If not, it should be an error...? 
      -- pure $ error "should not evaluate." <$ project t
      undefined

    TO (R.TVar rtv) -> do
      tv <- inferTVar rtv
      pure $ TO $ TVar tv
    TFun () params ret -> do
      fnUnion <- emptyUnion
      TFun fnUnion <$> sequenceA params <*> ret

inferType :: Type R -> Infer (Type TC)
inferType = cata $ \case
  TCon (R.DefinedDatatype rdd) rparams () -> do
    dd <- inferDataDef rdd
    params <- sequenceA rparams
    (newParams, unions) <- instantiateScheme mempty dd.ddScheme

    (Def.TmpNoLocation, newParams) `uniMany` (Nothing, params) -- just in case unify em

    mkType $ TCon dd params unions

  TCon (R.ExternalDatatype dd) rparams () -> do
    params <- sequenceA rparams
    (newParams, unions) <- instantiateScheme mempty dd.ddScheme

    (Def.TmpNoLocation, newParams) `uniMany` (Nothing, params) -- just in case unify em
    mkType $ TCon dd params unions

  TO (R.TClass rcd) -> do
    cd <- inferClass rcd
    t <- fresh
    let constr = constrain (error "todo")
    t `constr` (cd, mempty)  -- NOTE: we MUST ensure that this turns into a TVar. If not, it should be an error...? 
    pure t

  TO (R.TVar tv) -> do
    tvar <- TO . TVar <$> inferTVar tv
    mkType tvar

  TFun () rargs rret -> mkType =<< liftA3 TFun emptyUnion (sequenceA rargs) rret

inferTVar :: TVar R -> Infer (TVar TC)
inferTVar rtv = do
  classes <- Def.traverseSet inferClass rtv.tvClasses
  pure $ TV
    { fromTV = rtv.fromTV
    , binding = rtv.binding
    , tvClasses = classes
    }

mkTypeFromClassType :: Type TC -> ClassType TC -> Infer (Type TC)
mkTypeFromClassType self = cata $ \case
  Self -> pure self
  NormalType nt -> mkType =<< case nt of  -- TODO: maybe I should extractUnions in inferClassType??? why am I not doing it?
    TCon dd params _ -> do
      params' <- sequenceA params
      TCon dd params' <$> extractUnionsFromDataType dd  -- i think it's safe here to extractUnions, since it'll get instantiated anyway?
    TO tv -> pure $ TO tv
    TFun emptyFunUnion params ret -> liftA2 (TFun emptyFunUnion) (sequenceA params) ret


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

    unions <- case edcs of
          Right dcs -> trafold extractUnionsFromConstructor dcs
          Left drs -> trafold (\(Def.Annotated _ (_, t)) -> mapUnion ut t) drs

    pure dd



inferFunction :: Function R -> Infer (Function TC)
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration
    let anns = fst rfundec.functionOther

    params <- for rfundec.functionParameters $ \(v, definedType) -> do
      tv <- inferDecon v
      let vt = askType tv

      case definedType of
        DeclaredType rt -> do
          t <- inferType rt

          askUni tv `uni` (Just (error "error location for types!"), t)

        TypeNotDeclared -> pure ()
      pure (tv, vt)

    ret <- case rfundec.functionReturnType of
      DeclaredType t -> inferType t
      TypeNotDeclared -> fresh


    -- Set up temporary recursive env (if this function is recursive, this env will be used).
    let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
    let noGeneralizationScheme = Scheme mempty mempty
    let fundec = FD recenv rfundec.functionId params ret $ T.FunOther noGeneralizationScheme [] anns (snd rfundec.functionOther)
    let fun = Function { functionDeclaration = fundec, functionBody = body }

    -- Add *ungeneralized* type.
    addMemo fun

    -- Infer body.
    (env, body) <- withEnv rfundec.functionEnv $ withReturn ret $ do
      pf "AYOOOO"
      stmts <- inferStmts rfn.functionBody

      -- First, finalize substitution by taking care of member access.
      -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
      --  At the end there will be one last member access.
      -- TODO: technically, we can do it all at the end. I should add it to state and replace them at the end (since they are all referred to by the unique instantiation id).
      pf "IN FUNCTION %s" (pp fundec.functionId) :: Infer ()
      classInstantiationAssocs <- substAccessAndAssociations
      -- su <- RWS.gets typeSubstitution
      -- replacedStmts <- replaceClassFunsWithInstantiations su classInstantiationAssocs stmts

      pure (classInstantiationAssocs, stmts)

    -- now, replace it with a non-recursive environment.
    let fundec' = fundec { functionEnv = env }
    let fun' = fun { functionDeclaration = fundec' }


    pure fun'

  -- Add *generalized* version.
  addMemo fn

  pure fn

-- replaceClassFunsWithInstantiations :: Traversable f => Subst -> T.ClassInstantiationAssocs -> f (AnnStmt TC) -> Infer (f (AnnStmt TC))
-- replaceClassFunsWithInstantiations su cia = traverse $ cata $ \(O (Def.Annotated anns stmt)) -> do
--   replacedStmt <- case first (replaceInExpr su cia) stmt of
--         Return retExpr -> Return <$> replaceInExpr su cia retExpr
--         otherStmt -> bisequenceA otherStmt
--   pure $ (embed . O . Def.Annotated anns) replacedStmt

-- replaceInExpr :: Subst -> T.ClassInstantiationAssocs -> Expr TC -> Infer (Expr TC)
-- replaceInExpr su cia = cata $ \(N t e) -> fmap embed $ N t <$> case e of
--   Var v@(T.DefinedClassFunction _ snapshot self uci) loc ->
--     -- let mself = subst su self
--     case cia !? (Nothing, uci) of
--       Nothing -> pure $ Var v loc
--       Just (_, (typeApplication, ifn), _, ufi) -> do
--         let ucisInFunction = Set.fromList $ ifn.instFunDec.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ to _ uci) -> (Just (ufi, to), uci)
--             appliedUCIs = Map.restrictKeys cia ucisInFunction
--         -- ufi <- newFunctionInstantiation
--         pure $ Var (T.DefinedFunction (Function ifn.instFunDec ifn.instFunBody) typeApplication snapshot ufi) loc

--   -- note that this case should probably be the same as the one above after finding the actual function.
--   Var (T.DefinedFunction fn ts snapshot ufi) loc -> do
--     let ucisInFunction = Set.fromList $ fn.functionDeclaration.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ to _ uci) -> (Just (ufi, to), uci)
--         appliedUCIs = Map.restrictKeys cia ucisInFunction
--     pure $ Var (T.DefinedFunction fn ts snapshot ufi) loc

--   As x at -> As <$> x <*> pure at

--   expr -> sequenceA expr


-- Exports: what the current module will export.
inferExports :: Exports R -> Infer (Exports TC)
inferExports e = do
  vars  <- traverse (\(v, _) -> (v,) <$> var v) e.variables
  dts   <- traverse inferDataDef e.datatypes
  fns   <- traverse inferFunction e.functions
  cls   <- traverse inferClassDef e.classes
  insts <- for e.instances $ \case
    R.DefinedInst rinst -> inferInstance rinst
    R.ExternalInst tinst -> pure tinst
  pure $ Exports
    { variables = vars
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
  (R.DefinedClassFunDec (CFD _ uv params ret () headerLocation)) -> do
    params' <- for params $ \(decon, rt) -> do
      d <- inferDecon decon
      t <- inferClassType rt

      let dt = askUni d
      self <- fresh
      ct <- mkTypeFromClassType self t
      dt `uni` (Just (error "location for types (in function parameters!)"), ct)

      pure (d, t)

    ret' <- inferClassType ret
    pure $ CFD cd uv params' ret' () headerLocation

inferClassDeclaration :: ClassFunDec R -> Infer (ClassFunDec TC)
inferClassDeclaration (CFD rcd uv _ _ () _) = do
  tcd <- inferClassDef rcd
  let mcfd = find (\(CFD _ cuv _ _ () _) -> cuv == uv) tcd.classFunctions
  pure $ Def.mustOr (pf "[COMPILER ERROR]: Could not find function %s in class %s." (pp uv) (pp tcd.classID)) mcfd

inferInst :: R.Inst -> Infer (InstDef TC)
inferInst = \case
  R.ExternalInst inst -> pure inst
  R.DefinedInst inst -> inferInstance inst

inferInstance :: InstDef R -> Infer (InstDef TC)
inferInstance = memo memoInstance (\mem s -> s { memoInstance = mem }) $ \inst _ -> mdo
  pf "instanceeee"
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
    pf "fn"
    cfd@(CFD _ _ cparams cret _ classFunHeaderLocation) <- inferClassFunDec klass rfn.instClassFunDec

    -- TODO: add check?
    fn <- generalize $ mdo
      pf "lam generalize"
      self <- mkType $ TCon it tvs unions  -- TODO: when we stop ignoring tvars, properly instantiate them here.
      pf "miau"

      -- Infer function declaration.
      let rfundec = rfn.instFunDec
      let anns = fst rfundec.functionOther

      pf "before params"
      params <- for (zipWith (\(d, p) cp -> (d, p, cp)) rfundec.functionParameters (snd <$> cparams)) $ \(v, definedType, ct) -> do  -- NOTE: they SHOULD be exact, but if there was an error and we get a placeholder function, it'll error out on user error, which is bad.
        pf "param"
        tv <- inferDecon v
        let vt = askType tv

        -- map with CLASS TYPE FIRST!
        -- let tct = mkTypeFromClassType self ct
        -- vt `uni` tct

        case definedType of
          DeclaredType rt -> do
            t <- inferType rt

            askUni tv `uni` (Just (error "error location for defined types"), t)

          TypeNotDeclared -> pure ()
        pure (tv, vt)

      pf "ret?"
      ret <- case rfundec.functionReturnType of
        DeclaredType t -> inferType t
        TypeNotDeclared -> fresh

      -- now unify it with the base class function type.
      (tvs, unions) <- instantiateScheme mempty it.ddScheme
      classFun <- instantiateClassFunction cfd self

      union <- emptyUnion
      genFun <- mkType $ TFun union (snd <$> params) ret

      let instFunHeaderLocation = snd rfn.instFunDec.functionOther
      (instFunHeaderLocation, genFun) `uni` (Just classFunHeaderLocation, classFun)


      -- Set up temporary recursive env (if this function is recursive, this env will be used).
      let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
      let noGeneralizationScheme = Scheme mempty mempty
      let fundec = FD recenv rfundec.functionId params ret $ T.FunOther noGeneralizationScheme [] anns (snd rfundec.functionOther)
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

    pure InstFun
      { instFunDec = fn.functionDeclaration
      , instFunBody = fn.functionBody -- rfn.classFunctionPrototypeUniqueVar
      , instDef = instDef
      , instClassFunDec = cfd
      }

  pure instDef


-- -- error if inst function's type is different.
-- --  in its own function, because in the future the error will be more detailed.
-- ensureClassFunctionHasSameShapeAsInstance :: ClassFunDec TC -> Function TC -> Infer ()
-- ensureClassFunctionHasSameShapeAsInstance cfd@(CFD _ _ cparams cret _) fn = do
--   let
--     checkDifference :: ClassType TC -> Type TC -> [(ClassType TC, Type TC)]
--     checkDifference (Fix Self) _ = mempty  -- Assumption: self is correct (due to previous typechecking stuff). I don't bother checking it to write less code now :]
--     checkDifference (Fix (NormalType lct)) rt = case (lct, project rt) of
--       (TO _, TO _) -> undefined

--     FD _ _ params ret _ = fn.functionDeclaration
--     cts = cret : fmap snd cparams
--     ts  = ret : fmap snd params
--     -- I assume parameter list length was checked before.
--     diffs = fold $ zipWith checkDifference cts ts

--   unless (null diffs) $
--     err $ InstanceFunctionTypeNotMatchingClass cfd fn diffs


-- Generalizes the function inside.
generalize :: Infer (Function TC) -> Infer (Function TC)
generalize ifn = do
  fn <- ifn

  pf "Unsubstituted function:"
  pc fn

  -- csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  (scheme, assocs) <- constructSchemeForFunctionDeclaration fn.functionDeclaration

  pf "Scheme for %s: %s" (pp fn.functionDeclaration.functionId) (pp scheme) :: Infer ()
  pf "Assocs for %s: %s" (pp fn.functionDeclaration.functionId) (pp assocs) :: Infer ()


  let generalizedFnWithScheme = fn { functionDeclaration = fn.functionDeclaration { functionOther = T.FunOther { T.functionScheme = scheme, T.functionAssociations = assocs, T.functionAnnotations = fn.functionDeclaration.functionOther.functionAnnotations, T.functionLocation = fn.functionDeclaration.functionOther.functionLocation } } }

  pf "Substituted function %:" fn.functionDeclaration.functionId
  pc generalizedFnWithScheme
  pc =<< lift CompilerContext.getTypeUni

  -- Also, remember the substitution! (tvars might escape the environment)
  --  TODO: not sure if that's the best way. maybe instead of doing this, just add it in the beginning and resubstitute the function.
  -- let (Subst _ tvars) = su  -- NOTE: safe!
  -- for_ (Map.toList tvars) $ uncurry (bind undefined)


  pure generalizedFnWithScheme


substAccessAndAssociations :: Infer T.ClassInstantiationAssocs
substAccessAndAssociations = do
  Def.phase "SUBST ACCESS"
  go where
    go = do
      didAccessProgressedSubstitutions <- substAccess
      classInstantiationAssocs <- substAssociations
      let didAssociationsProgressedSubstitutions = not $ null classInstantiationAssocs
      pf "CIA KEYS: %" $ pp $ Set.toList $ Map.keysSet classInstantiationAssocs
      -- pc classInstantiationAssocs

      -- There should be no more than one UCI for a type. These are already selected.
      if didAccessProgressedSubstitutions || didAssociationsProgressedSubstitutions
        then Map.unionWith (error "more than one assoc for uci should not happen") classInstantiationAssocs <$> go
        else do
          Def.phase "END SUBST ACCESS"
          pure mempty


-- substitutes members n shiii (this is done in conjunction with associated types).
-- returns True if substitutions were done.
substAccess :: Infer Bool
substAccess = do
  membersAccessed <- RWS.gets memberAccess
  substitutedMembers <- fmap filterDesignatedForRemoval $ for membersAccessed $ \(ogt, memname, t, location) -> do
    (mexpectedType, shouldRemove) <- getExpectedType location ogt memname
    case mexpectedType of
      Nothing -> pure ()
      Just expectedType -> (location, t) `uni` (Nothing, expectedType)
    pure ((ogt, memname, t, location), shouldRemove)

  RWS.modify $ \s -> s { memberAccess = substitutedMembers }
  pure (length substitutedMembers < length membersAccessed)


-- returns True if substitutions were done.
substAssociations :: Infer T.ClassInstantiationAssocs
substAssociations = do
  assocs <- RWS.gets associations
  RWS.modify $ \s -> s { associations = mempty }

  (substitutedAssociations, classInstantiationAssocs) <- fmap (bimap filterDesignatedForRemoval (foldr (<>) Map.empty) . unzip) $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) (toLocation, to) (CFD cd uv _ _ () _) uci baseUFI envsToAddTo, insts) -> do
    unFrom <- getType from
    case unFrom of
        TCon dd _ _ -> case insts !? cd >>= (!? dd) of
          Just inst -> do
            -- select instance function to instantiate.
            let instFun = Def.mustOr (pf "[COMPILER ERROR]: Could not select function %s bruh," (pp uv)) $ find (\InstFun { instClassFunDec = CFD _ cuv _ _ () _ } -> cuv == uv) inst.instFuns

            -- hope it's correct....
            -- let baseFunctionScopeSnapshot = Map.singleton instFun.instDef.instClass insts  -- FIX: bad interface. we make a singleton, because we know which class it is. also, instance might create constraints of some other class bruh. ill fix it soon.
            -- TODO: FromEnvironment locality only here, because it means we won't add anything extra to the instantiations.
            let notExternalBecauseWeDontKnow = False
            (instFunType, T.DefinedFunction fn instAssocs _ ufi, env@(T.Env _ _ _ level)) <- instantiateFunction notExternalBecauseWeDontKnow fromLocation (Just uci) insts $ Function instFun.instFunDec instFun.instFunBody

            pf "fun assoc uni %: %" fn.functionDeclaration.functionId =<< presentFunctionType fn
            mto <- presentType to
            ifnt <- presentType instFunType
            pf "uni: % %" mto ifnt
            (toLocation, to) `uni` justType instFunType
            pf "ENV ASSOC: %" env
            addExtraToEnv envsToAddTo env

            -- su <- RWS.gets typeSubstitution

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
  in lift $ CompilerContext $ RWS.modify $ \s -> s { CompilerContext.globalEnvAddition = Map.unionWith (\new old ->
    -- Some other env addition might have used those variables before, so we have to remove repetitions.
    let oldSet = Set.fromList old
    in old <> filter (`Set.notMember` oldSet) new) newEnvAdditions s.globalEnvAddition }

--  2. report any errors or something.
-- TODO: all of these 3 functions are kinda hindi-style programming. FIX IT AFTER I UNDERSTAND WHAT IM DOING.
reportAssociationErrors :: Infer ()
reportAssociationErrors = do
  assocs <- RWS.gets associations
  -- su <- RWS.gets typeSubstitution

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) _ (CFD cd _ _ _ () _) _ _ _, insts) -> do
    getType from >>= \case
        TCon dd _ _ -> case insts !? cd >>= (!? dd) of
          Just _ -> error "[COMPILER ERROR]: resolvable associated type found. should already be taken care of."

          Nothing -> do
            err $ DataDefDoesNotImplementClass (fromLocation) dd cd
            pure (t, True)

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        TFun {} -> do
          from' <- presentType from
          err $ FunctionTypeConstrainedByClass fromLocation from' cd
          pure (t, True)

        TO (TVar tv) -> do
          error $ pf "[COMPILER ERROR]: associated type of tvar %s not bound by this function. should not happen?" (pp tv)

        TO (TyVar _) -> do
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }


-- used after generalization to
--  1. extract associations for the function.
rummageThroughAssociations :: Def.UniqueVar -> Set (Type TC, T.TyVar) -> Infer ([T.FunctionTypeAssociation TC], Map T.TyVar (TVar TC))
rummageThroughAssociations funUV tyvars = do
  assocs <- RWS.gets associations
  let
    -- Then substitute it.
    asTVar (T.TyV _ tyname classInstances) = TV tyname (BindByVar funUV) (Set.fromList $ fst <$> classInstances)

  -- do subst here!!! IMPORTANT!!!
  for_ tyvars $ \(tid, tyvar) -> do
    tvarID <- mkType $ TO $ TVar $ asTVar tyvar
    bind (error "todo") (tid, tyvar) tvarID

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) _ (CFD cd _ _ _ () _) _ _ _, insts) -> do
    getType from >>= \case
        TO (TVar tv) | tv.binding == BindByVar funUV -> do
          -- will be added later to the association list!
          pure (t, True)

        _ ->
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }  -- TODO: what? what am i doing

  -- second: extract associations for the function.
  functionAssociationsAndFutureTVars <- fmap catMaybes $ for assocs $ \(T.TypeAssociation (fromLocation, from) (toLocation, to) cfd uci _ _, _) -> do
    getType from >>= \case
        TO (TVar tv) | tv.binding == BindByVar funUV ->
          fmap Just $ (T.FunctionTypeAssociation tv to cfd uci,) <$> lift (findFTV to)
        _ -> pure Nothing

  let functionAssociations = fst <$> functionAssociationsAndFutureTVars
  let newTyVars = foldMap snd functionAssociationsAndFutureTVars

  if null functionAssociations
    then pure ([], Map.fromSet asTVar $ Set.map snd tyvars)
    else do
      (newAssocs, tvs) <- rummageThroughAssociations funUV newTyVars
      pure (functionAssociations <> newAssocs, Map.fromSet asTVar (Set.map snd tyvars) <> tvs)


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
--  BRUH: RN INSTEAD OF GENERATING SUBSTITUTION, JUST REPLACE THE TYVARS!
constructSchemeForFunctionDeclaration :: FunDec TC -> Infer (Scheme TC, [T.FunctionTypeAssociation TC])
constructSchemeForFunctionDeclaration dec = do
      -- IMPORTANT: We only extract types from non-instantiated! The instantiated type might/will contain types from our function and we don't want that. We only want to know which types are from outside.
      -- So, for a function, use its own type.
      -- For a variable, use the actual type as nothing is instantiated!
  let digOutTyVarsAndUnionsFromEnv :: T.Env -> Infer (Set (T.TypeID, T.TyVar), Map T.EnvUnion ([Type TC], Type TC))
      digOutTyVarsAndUnionsFromEnv (T.RecursiveEnv _ _) = pure mempty
      digOutTyVarsAndUnionsFromEnv (T.Env _ env _ _) = fmap fold $ traverse (\(v, _ ,t) -> digThroughVar t v) env
        where
          digThroughVar :: Type TC -> T.Variable -> Infer (Set (T.TypeID, T.TyVar), Map T.EnvUnion ([Type TC], Type TC))
          digThroughVar t = \case
            T.DefinedVariable _ -> digOutTyVarsAndUnionsFromType t
            T.DefinedFunction f _ _ _ -> do
              params <- traverse (digOutTyVarsAndUnionsFromType . snd) f.functionDeclaration.functionParameters
              ret <- digOutTyVarsAndUnionsFromType f.functionDeclaration.functionReturnType  -- should we dig through external functions?
              pure $ fold params <> ret

            T.DefinedClassFunction (CFD cd _ _ _ () _) snapshot _ _   -- TODO: I think we don't need to dig through instances?
              -> pure mempty

  (tyVarsOutside, unionsOutside) <- digOutTyVarsAndUnionsFromEnv dec.functionEnv
  (tyVarsDeclaration, unionsDeclaration) <- liftA2 (<>) (fmap fold $ traverse (digOutTyVarsAndUnionsFromType . snd) dec.functionParameters) (digOutTyVarsAndUnionsFromType dec.functionReturnType)

      -- TypesDefinedHere = FnType \\ Environment
  let tyVarsOutside' = Set.map snd tyVarsOutside
  let tyVarsOnlyFromHere = Set.filter ((`Set.notMember` tyVarsOutside') . snd) tyVarsDeclaration
      unionsOnlyFromHere = unionsDeclaration Map.\\ unionsOutside

      -- ALGO: ASSOCIATIONS

      -- function to find tvars defined for this function!
      definedTVars = findTVarsForID dec.functionId

  tvarsDefinedForThisFunction <- liftA2 (<>) (trafold (definedTVars . snd) dec.functionParameters) (definedTVars dec.functionReturnType)

  pf "FunDec for %: %" (pp dec.functionId) (pp dec)
  pf "UNIONS for %: % = % \\\\ %" (pp dec.functionId) (pp $ Map.keysSet unionsOnlyFromHere) (pp $ Map.keysSet unionsDeclaration) (pp $ Map.keysSet unionsOutside)
  pf "ASSOCS when %:" (pp dec.functionId)
  associations <- RWS.gets associations
  pf "Associations (???): %" (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation (fromLocation, from) to _ uci ufi _, _) -> pf "(%) %: %" (pp (uci, ufi)) (pp from) (pp to) :: String)

  -- add associations.
  (assocs, tvmap) <- rummageThroughAssociations dec.functionId tyVarsOnlyFromHere -- remember to use the new Subst, which generalizes the associations.
  pf "after rummaging: %" assocs
  reportAssociationErrors

  -- BIG THING HERE!!!!
  -- do the substitution like THIS.
  pf "after binding"

  let
      Scheme tvars _ = Scheme (Set.toList $ Set.fromList (Map.elems tvmap) <> tvarsDefinedForThisFunction) (fmap (\(u, (ts, t)) -> (u, ts, t)) $ Map.toList unionsOnlyFromHere)

  (_, assocUnions) <- trafold (\(T.FunctionTypeAssociation _ t _ _) -> digOutTyVarsAndUnionsFromType t) assocs
  let assocScheme = Scheme tvars (fmap (\(u, (params, ret)) -> (u, params, ret)) $ Map.toList $ unionsOnlyFromHere <> assocUnions)

  pure (assocScheme, assocs)

digOutTyVarsAndUnionsFromType :: Type TC -> Infer (Set (T.TypeID, T.TyVar), Map T.EnvUnion ([Type TC], Type TC))
digOutTyVarsAndUnionsFromType = getType' >=> traverse2 (\t -> (t,) <$> digOutTyVarsAndUnionsFromType t) &=> \(tid, t) -> case t of
    TO (TyVar tyv) -> (Set.singleton (tid, tyv), mempty)
    TFun union ts t -> (mempty, Map.singleton union (fst <$> ts, fst t)) <> foldMap snd ts <> snd t
    TCon _ ts unis -> foldMap snd ts <> foldMap ((mempty,) . (\(u, params, ret) -> Map.singleton u (params, ret))) unis
    t -> foldMap snd t


-- goes through the type and finds tvars that are defined for this function.
findTVarsForID :: Def.UniqueVar -> Type TC -> Infer (Set (TVar TC))
findTVarsForID euid = go where
  go tid = getType tid >>= \case
      TO (TVar tv@(TV _ (Def.BindByVar varid) _)) | varid == euid -> pure $ Set.singleton tv
      t' -> trafold go t'

-- copy of previous function for ClassType
findTVarsForIDInClassType :: Def.UniqueVar -> ClassType TC -> Set (TVar TC)
findTVarsForIDInClassType euid = cata $ \case
  NormalType (TO (TVar tv@(TV _ (Def.BindByVar varid) _)))  | varid == euid -> Set.singleton tv
  t -> fold t


-- Substitute return type for function.
withReturn :: Type TC -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }

getExpectedType :: Def.Location -> Type TC -> Def.MemName -> Infer (Maybe (Type TC), Bool)  -- (maybe type, should remove from list?)
getExpectedType location t memname = getType t >>= \case
  TCon dd@(DD _ (Scheme ogTVs ogUnions) (Left recs) _) tvs unions ->
    case find (\(Def.Annotated _ (name, _)) -> name == memname) recs of
      Just (Def.Annotated _ (_, recType)) -> do
        ogUnions' <- for ogUnions $ \(uid, _, _) -> getUnion uid
        let mapTVs = mapTVsWithMap mempty mempty (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions') $ fmap (\(u, _, _) -> u) unions)
        recType' <- ump $ mapTVs recType
        pure (Just recType', True)

      Nothing -> do
        err $ DataTypeDoesNotHaveMember location dd memname
        pure (Nothing, True)

  TO (TyVar _) ->
      -- type not yet known. ignore.
    pure (Nothing, False)

  TCon dd@(DD _ _ (Right _) _) _ _ -> do
    err $ DataTypeIsNotARecordType location dd memname
    pure (Nothing, True)

  TFun {} -> do
    t' <- presentType t
    err $ FunctionIsNotARecord location t' memname
    pure (Nothing, True)

  TO (TVar tv) -> do
    err $ TVarIsNotARecord location tv memname
    pure (Nothing, True)


inferDecon :: Decon R -> Infer (Decon TC)
inferDecon = cata $ \(N location d) -> fmap embed $ case d of
    CaseIgnore -> do
      t <- fresh
      pure $ N (T.ExprNode { T.t = t, T.loc = location }) CaseIgnore

    CaseVariable uv -> do
      t <- var uv
      pure $ N (T.ExprNode { T.t = t, T.loc = location }) $ CaseVariable uv

    CaseRecord dd cases -> do
      dd' <- inferDatatype dd
      t <- instantiateRecord dd'
      cases' <- Def.sequenceA2 cases

      for_ cases' $ \(mem, decon) -> do
        mt <- addMember location t mem
        askUni decon `uni` (Nothing, mt)

      pure $ N (T.ExprNode { T.t = t, T.loc = location }) $ CaseRecord dd' cases'

    CaseConstructor rcon idecons -> do

      -- Ger proper constructor.
      con@(DC dd@(DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts _) <- inferConstructor rcon

      -- Deconstruct decons.
      decons <- sequenceA idecons

      -- Custom instantiation for a deconstruction.
      -- Create a parameter list to this constructor
      (tvs, unions) <- instantiateScheme mempty scheme
      ogUnions' <- for ogUnions $ \(uid, _, _) -> getUnion uid
      let mapTVs = mapTVsWithMap mempty mempty (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip (T.unionID <$> ogUnions') $ fmap (\(u, _, _) -> u) unions)
      ts <- ump $ traverse mapTVs usts

      let args = askType <$> decons
      (location, args) `uniMany` (Just (error "todo: add location information to datatype declaration"), ts)

      t <- mkType $ TCon dd tvs unions
      pure $ N (T.ExprNode { T.t = t, T.loc = location }) $ CaseConstructor con decons


------
-- Instantiation
------

-- TODO: merge it with 'inferVariable'.
instantiateVariable :: Def.Location -> Def.Locality -> T.Variable -> Infer (Type TC, T.Variable)
instantiateVariable location loc = resetUniPrint . \case
  T.DefinedVariable v -> var v <&> (,T.DefinedVariable v)
  T.DefinedFunction fn _ snapshot _ -> do
    (t, v, env) <- instantiateFunction False location Nothing snapshot fn -- notice that we use the UFI from here (inferVariable just creates a temp error type to not use it)

    associations <- RWS.gets associations
    pf "Associations (instantiation): %" (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation (fromLocation, from) to _ uci ufi _, _) -> pf "(%) %: %" (pp (uci, ufi)) (pp from) (pp to) :: String)

    -- add instantiations!
    --  only when it's a local function should you add stuff from its environment to instantiations.
    let gatherInstsFromEnvironment :: T.Env -> Infer (Set (T.Variable, Type TC))
        gatherInstsFromEnvironment = \case
            T.RecursiveEnv _ _ -> pure mempty
            T.Env _ vars _ _ -> flip trafold vars $ \case
              (envVar@(T.DefinedFunction fn _ _ ufi), Def.Local, t) -> do
                -- NOTE: we need mapped envs, so we have to dig through the type. but, are we too permissive? should we only choose this current env? or all of them? how do we distinguish the "current" one?
                let currentEnvID = T.envID fn.functionDeclaration.functionEnv
                (baset, envs) <- getType' t >>= \(baset, tt) -> case tt of
                  TFun union _ _ -> (baset,) <$> (getUnion union <&> \u -> map (\(_, _, _, env) -> env) $ filter (\(_, ufi', _, env) -> ufi' == ufi) u.union)
                  _ -> error "impossible, it's a function type."
                Set.insert (envVar, baset) <$> (trafold gatherInstsFromEnvironment envs)
              (envVar, _, t) -> pure $ Set.singleton (envVar, t)

    theseInsts <- if loc == Def.Local
      then gatherInstsFromEnvironment env
      else pure mempty

    RWS.modify $ \s -> s { instantiations = Set.insert (v, t) $ theseInsts <> s.instantiations }

    pure (t, v)


  T.DefinedClassFunction cfd@(CFD cd funid params ret () _) snapshot self _ -> do
    fnType <- instantiateClassFunction cfd self
    let insts = snapshot
    uci <- newClassInstantiation
    associateType (location, self) (location, fnType) cfd insts uci Nothing
    -- addClassFunctionUse fnUnion cfd self insts
    pf "INSTANTIATING CLASS FUN %(%). INSTS: %" (pp funid) (pp uci) $ fmap (fmap (\(DD { ddName }) -> ddName) . Set.toList . Map.keysSet) $ Map.elems insts :: Infer ()


    pure (fnType, T.DefinedClassFunction cfd snapshot self uci)

instantiateClassFunction :: ClassFunDec TC -> Type TC -> Infer (Type TC)
instantiateClassFunction (CFD _ funid params ret () _) self = do
    -- TODO: a lot of it is duplicated from DefinedFunction. sussy
    -- TODO TODO: NOT SURE IF IT'S ALL NECESSARY!!!!!!!!!!!!!!!!!!!!!!!!
    -- SHOULD EXPLAIN EACH LINE BECAUSE SOMETHING FEELS OFF
    let allTypes = ret : map snd params
    let thisFunctionsTVars = foldMap (findTVarsForIDInClassType funid) allTypes

    -- dig out unions from class type (instantiate class type)
    -- all these unions should come from datatypes. so...
    let extractUnions :: ClassType TC -> Infer (Map T.EnvUnion ([Type TC], Type TC))
        extractUnions = cata $ \case
          NormalType (TCon dd params _) -> do
            ddUnions <- Map.fromList . fmap (\(u, ts, t) -> (u, (ts, t))) <$> extractUnionsFromDataType dd
            paramUnions <- seqfold params
            pure $ ddUnions <> paramUnions
          ct -> seqfold ct

    thisFunctionsUnions <- trafold extractUnions allTypes

    let schemeTVars = Set.toList thisFunctionsTVars
    let schemeUnions = Map.toList thisFunctionsUnions <&> \(u, (params, ret)) -> (u, params, ret)
    let scheme = Scheme schemeTVars schemeUnions

    (itvs, iunions) <- instantiateScheme mempty scheme
    let tvmap = Map.fromList $ zip schemeTVars itvs
    ogUnions' <- for schemeUnions $ \(u, _, _) -> getUnion u
    let unionmap = Map.fromList $ zip (T.unionID <$> ogUnions') $ iunions <&> \(u, _, _) -> u
    let mapTVs = mapTVsWithMap mempty mempty tvmap unionmap <=< lift . mkTypeFromClassType self

    fnType <- mkType =<< ump (liftA3 TFun (lift emptyUnion) (traverse (mapTVs . snd) params) (mapTVs ret))
    pure fnType


-- NOTE: these last two parameters are basically a hack. I don't yet know what to do when we're dealing with an instance function, so we're only doing it here for now. (we should probably do the same thing there, but it's not local, so modifying the state then would be bad. I'll have to think about it.)
instantiateFunction :: T.IsFromExternalModule -> Def.Location -> Maybe Def.UniqueClassInstantiation -> T.ScopeSnapshot TC -> Function TC -> Infer (Type TC, T.Variable, T.Env)
instantiateFunction isExternal assocLocation muci snapshot fn = do
    let fundec = fn.functionDeclaration
    let (Scheme schemeTVars schemeUnions) = fundec.functionOther.functionScheme

    pf "Before schemin: %" fundec.functionId
    pf "Before schemin: %" =<< presentFunctionType fn
    (tvs, unions) <- instantiateScheme snapshot fundec.functionOther.functionScheme
    punions <- traverse (\(u, _, _) -> getUnion u) unions
    pf "TypeUni for % after scheme instantiation: %" fundec.functionId =<< lift CompilerContext.getTypeUni
    pf "GOT SCHEME: % %" tvs punions

    -- Prepare a mapping for the scheme!
    let tvmap = Map.fromList $ zip schemeTVars tvs
    schemeUnions' <- for schemeUnions $ \(u, _, _) -> getUnion u
    let unionmap = Map.fromList $ zip (T.unionID <$> schemeUnions') $ unions <&> \(u, _, _) -> u
    dontMapThoseTypes <- definedVarTypes fundec.functionEnv
    pf "DONT MAP EM: %" dontMapThoseTypes
    let
      mapTVs :: Type TC -> UltraMap (Type TC)
      mapTVs = mapTVsWithMap mempty dontMapThoseTypes tvmap unionmap <=< lift . mapClassSnapshot mempty dontMapThoseTypes (Set.fromList schemeTVars) snapshot

    pf "Instantiation of %" (pp fundec.functionId) :: Infer ()
    pf "TVars: %" (pp schemeTVars)  :: Infer ()
    pf "Unions: %" =<< traverse (\(u, _, _) -> getUnion u) schemeUnions
    pf "Scope Snapshot:\n%" (T.dbgSnapshot snapshot) :: Infer ()
    pf "after schemin: %" =<< presentFunctionType fn

    pc $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) tvmap
    pc $ (Def.ppMap . fmap (bimap Def.ppUnionID pp) . Map.toList) unionmap


    -- Create type from function declaration
    ufi <- newFunctionInstantiation

    -- add new associations
    (fnType, v) <- ultraMapThing $ do
      assocs <- for fundec.functionOther.functionAssociations $ \(T.FunctionTypeAssociation tv to cfd@(CFD cd _ _ _ () _) uci) -> do
        let from = fromMaybe (error "couldn't map tvar in function type association") $ tvmap !? tv
        lift $ pf "FROM: %" from
        mto <- mapTVs to
        lift $ pf "TO: %" =<< presentType mto
        lift $ associateType (assocLocation, from) (assocLocation, mto) cfd snapshot uci (Just ufi) -- TEMP
        pure mto

      lift $ pf "after assocs: %" =<< presentFunctionType fn

      fnUnion <- lift $ singleEnvUnion muci ufi assocs fundec.functionEnv
      fnType <- mapTVs =<< lift (mkType (TFun fnUnion (snd <$> fundec.functionParameters) fundec.functionReturnType))

      let v = T.DefinedFunction fn assocs snapshot ufi
      pure (fnType, v)

    mappedEnv <- getType fnType >>= \case  -- we're lazy, so we're not writing another function, we're just unsafely deconstructing the result of that function.
          TFun union _ _ -> getUnion union <&> \case
            (T.EnvUnion { T.union = [(_, _, _, env)] }) -> env
            _ -> error "MUST NOT HAPPEN."
          _ -> error "MUST NOT HAPPEN."

    pc =<< lift CompilerContext.getTypeUni
    gfn <- presentFunctionType fn
    pf "For function %:\n\tScheme unions: % -> %\n\tType %.\n\tAfter instantiation: %"
      (pp fundec.functionId)
      schemeUnions'
      punions
      gfn
      =<< presentType fnType

    pure (fnType, v, mappedEnv)


-- check which types should NOT be instantiated (for cuckedUnions)
--  should we go that deep?
definedVarTypes :: T.Env -> Infer (Set (Type TC))
definedVarTypes = doEnv where
  doEnv = \case
    T.RecursiveEnv {} -> pure mempty
    T.Env _ vars _ _ -> do
      let (dvars, others) = partition (\(v, _, _) -> case v of { T.DefinedVariable {} -> True; _ -> False }) vars
      dvarBaseTypes <- trafold (\(_, _, t) -> Set.singleton . fst <$> getType' t) dvars
      -- otherTypes <- fmap fold $ traverse doType $ map (\(_, _, t) -> t) others
      pure $ dvarBaseTypes  -- maybe i shouldn't go deeper?

  doType :: Type TC -> Infer (Set (Type TC))
  doType = getType >=> traverse doType >=> \case
    TFun union ts t -> doUnion union <&> (<> fold ts <> t)
    TCon _ ts unions -> (fold ts <>) <$> trafold (doUnion . (\(u, _, _) -> u)) unions
    _ -> pure mempty

  doUnion :: T.EnvUnion -> Infer (Set (Type TC))
  doUnion = getUnion >=> \u -> trafold (\(_, _, _, env) -> doEnv env) u.union

associateType :: (Def.Location, Type TC) -> (Def.Location, Type TC) -> ClassFunDec TC -> T.ScopeSnapshot TC -> Def.UniqueClassInstantiation -> Maybe Def.UniqueFunctionInstantiation -> Infer ()
associateType (fromLocation, based) (toLocation, result) cfd insts uci ufi = do
    pf "ASSOC: %s %s" (pp uci) (pp ufi)
    estack <- RWS.gets envStack
    let ta = T.TypeAssociation (fromLocation, based) (toLocation, result) cfd uci ufi estack

    RWS.modify $ \s -> s { associations = (ta, insts) : s.associations }


-- addClassFunctionUse :: T.EnvUnion -> T.ClassFunDec -> T.Type -> T.PossibleInstances -> Infer ()
-- addClassFunctionUse eu cfd self insts = RWS.modify $ \s -> s { classFunctionUnions = (eu, cfd, self, insts) : s.classFunctionUnions }

instantiateConstructor :: Def.EnvID -> DataCon TC -> Infer (Type TC)
instantiateConstructor envID = resetUniPrint . \case
  DC dd@(DD _ scheme _ _) _ [] _ -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    mkType $ TCon dd tvs unions

  (DC dd@(DD _ scheme@(Scheme ogTVs ogUnions) _ _) _ usts@(_:_) _) -> do
    (tvs, unions) <- instantiateScheme mempty scheme
    ogUnions' <- for ogUnions $ \(u, _, _) -> T.unionID <$> getUnion u
    let mapTVs = mapTVsWithMap mempty mempty (Map.fromList $ zip ogTVs tvs) (Map.fromList $ zip ogUnions' $ fmap (\(u, _, _) -> u) unions)
    ts <- ump $ traverse mapTVs usts

    ret <- mkType $ TCon dd tvs unions

    -- don't forget the empty env!
    let emptyEnv = T.Env envID [] mempty []
    ufi <- newFunctionInstantiation
    union <- singleEnvUnion Nothing ufi [] emptyEnv

    mkType $ TFun union ts ret

instantiateRecord :: DataDef TC -> Infer (Type TC)
instantiateRecord dd@(DD _ scheme (Left _) _) = do
  (tvs, unions) <- instantiateScheme mempty scheme
  mkType $ TCon dd tvs unions

instantiateRecord (DD ut scheme (Right _) _) = error $ pf "Attempted to instantiate ADT (%s) as a Record!" (pp ut)


instantiateScheme :: T.ScopeSnapshot TC -> Scheme TC -> Infer ([Type TC], [(T.EnvUnion, [Type TC], Type TC)])
instantiateScheme insts (Scheme schemeTVars schemeUnions) = do
  -- Prepare a mapping for the scheme!
  tyvs <- traverse (const fresh) schemeTVars  -- scheme
  let tvmap = Map.fromList $ zip schemeTVars tyvs

  -- Unions themselves also need to be mapped with the instantiated tvars!
  newUnionIDs <- traverse (const (lift CompilerContext.nextUnionUniID)) schemeUnions
  normalizedIDs <- traverse (\(u, _, _) -> fst <$> getUnion' u) schemeUnions 
  let premade = Map.fromList $ zip normalizedIDs newUnionIDs
  pf "PREMADE: %" premade
  let mapOnlyTVsForUnions = mapTVsWithMap premade mempty tvmap mempty <=< lift . mapClassSnapshot (Map.keysSet premade) mempty (Set.fromList schemeTVars) insts
  unions <- ump $ for (zip newUnionIDs schemeUnions) $ \(newUID, (union, params, ret)) -> do
    let union' = lift . cloneUnion newUID =<< traverse mapOnlyTVsForUnions =<< lift (getUnion union)
    liftA3 (,,) union' (traverse mapOnlyTVsForUnions params) (mapOnlyTVsForUnions ret)

  -- NOTE not needed now?
  -- funny FIX (it should be done better.)
  -- since we might need to substitute inside the new unions, and there might be chain dependency, just resubstitute until nothing changes in the type
  -- let resubstitute unions =
  --       let
  --         unionMap = Map.fromList $ zip unionIDs (unions <&> \(u, _, _) -> u)
  --         subUnions = undefined unions
  --       in if unions /= subUnions
  --         then resubstitute subUnions
  --         else subUnions
  -- let subUnions = resubstitute unions


  -- also, don't forget to constrain new types.
  for_ (zip tyvs schemeTVars) $ \(t, tv) -> do
    for_ tv.tvClasses $ \klass -> do
      let instmap = fromMaybe mempty $ insts !? klass
      let constr = constrain (error "todo")
      t `constr` (klass, instmap)

  pure (tyvs, unions)


-- very bad... memo for mapping types.
type UltraMap a = StateT (Map (Type TC) (Type TC), Map T.EnvUnion T.EnvUnion) Infer a
ultraMapThing :: UltraMap a -> Infer a
ultraMapThing umx = State.evalStateT umx mempty

ump = ultraMapThing


-- Should recursively map all the TVars in the type. (including in the unions.)
-- TODO: this function became retarded
--   premade - premap unions when unions depend on each other during instantiation.
--   exclude - for cucked unions, we must not instantiate types. it works i guess. maybe i should do something better.
mapTVsWithMap :: Map T.EnvUnion T.EnvUnion -> Set (Type TC) -> Map (TVar TC) (Type TC) -> Map Def.UnionID (T.EnvUnion) -> Type TC -> UltraMap (Type TC)
mapTVsWithMap premade exclude tvmap unionmap =
  let
    mapTVs :: Type TC -> UltraMap (Type TC)
    mapTVs = tryMemoType $ \baseTid ttt -> traverse mapTVs ttt >>= \case
        TO (TVar tv) -> error "bruh"  -- lift $ getType $ fromMaybe baseTid (tvmap !? tv)
        TFun union ts tret -> do
          uid <- T.unionID <$> lift (getUnion union)
          union' <- maybe (mapUnion union) pure (unionmap !? uid)  -- TODO: put this in tryMemoUnion...
          pure $ TFun union' ts tret
        TCon dd ts unions -> do
          unions' <- for unions $ \(union, params, ret) -> do
            uid <- T.unionID <$> lift (getUnion union)
            liftA3 (,,) (maybe (mapUnion union) pure (unionmap !? uid)) (traverse mapTVs params) (mapTVs ret)
          pure $ TCon dd ts unions'
        TO tt -> pure $ TO tt

    mapUnion :: T.EnvUnion -> UltraMap T.EnvUnion
    mapUnion = tryMemoUnion $ \_ u -> do
        newUnion <- for u.union $ \(muci, ufi, ts, env) -> do
              ts' <- traverse mapTVs ts
              env' <- mapEnv premade exclude tvmap unionmap env
              pure (muci, ufi, ts', env')
        pure $ u { T.union = newUnion }

    tryMemoType :: (Type TC -> TypeF TC T.TypeID -> UltraMap (TypeF TC T.TypeID)) -> Type TC -> UltraMap (Type TC)
    tryMemoType fux tid = lift (getType' tid) >>= \(baseTid, t) -> if baseTid `Set.member` exclude
      then pure tid
      else do
        State.gets fst >>= \tvs -> case tvs !? baseTid of
          Just newU -> pure newU
          Nothing -> do
                t' <- case t of
                  TO (TVar tv) -> pure $ fromMaybe baseTid (tvmap !? tv)  -- HACK! to not duplicate changed tvars accidentally
                  _ -> do
                    evaldType <- fux baseTid t
                    if t == evaldType
                      then pure tid
                      else do
                            newT <- lift $ mkType evaldType
                            pure newT

                State.modify $ first $ Map.insert baseTid t'
                pure t'

    tryMemoUnion :: (T.EnvUnion -> T.EnvUnionF TC T.TypeID -> UltraMap (T.EnvUnionF TC T.TypeID)) -> T.EnvUnion -> UltraMap T.EnvUnion
    tryMemoUnion fux uid = do
      (baseUid, u) <- lift $ getUnion' uid
      State.gets snd >>= \us -> case premade !? baseUid of
          Just premadeUnion -> pure premadeUnion
          Nothing -> case us !? baseUid of
            Just newU -> pure newU
            Nothing -> do
              evaldUnion <- fux baseUid u
              if u == evaldUnion
                then pure uid
                else do
                  newU <- lift $ mkUnion evaldUnion
                  State.modify $ fmap $ Map.insert baseUid newU
                  pure newU

  in mapTVs

mapEnv :: Map T.EnvUnion T.EnvUnion -> Set (Type TC) -> Map (TVar TC) (Type TC) -> Map Def.UnionID T.EnvUnion -> T.Env -> UltraMap T.Env
mapEnv premade exclude tvmap unionmap = \case
    T.Env eid vars localities level -> do
      vars' <- for vars $ \(v, loc, t) -> do
        v' <- mapVar v
        t' <- mapTVsWithMap premade exclude tvmap unionmap t
        pure (v', loc, t')
      pure $ T.Env eid vars' localities level
    e -> pure e
  where
    mapVar :: T.Variable -> UltraMap T.Variable
    mapVar = \case
      T.DefinedClassFunction cfd snap self uci -> do
        mappedSelf <- mapTVsWithMap premade exclude tvmap unionmap self
        pure $ T.DefinedClassFunction cfd snap mappedSelf uci
      T.DefinedFunction fn assocs snap ufi -> do
        mappedAssocs <- for assocs $ mapTVsWithMap premade exclude tvmap unionmap
        pure $ T.DefinedFunction fn mappedAssocs snap ufi
      v -> pure v


-- This replaces the snapshot (available instances) for classes with a tvar in the set. Might be merged with mapTVsWithMap, but I'll have to make sure it's always used in the same context.
mapClassSnapshot :: Set T.EnvUnion -> Set (Type TC) -> Set (TVar TC) -> T.ScopeSnapshot TC -> Type TC -> Infer (Type TC)
mapClassSnapshot excludedUnions exclude tvs snapshot = mapType
  where
    mapType :: Type TC -> Infer (Type TC)
    mapType = getType' >=> \(tid, tt) -> if tid `Set.member` exclude
      then pure tid
      else traverse mapType tt >>= \case
        TFun union args ret -> do
          union' <- mapUnion union
          mkType $ TFun union' args ret
        TCon dd ts unions -> do
          unions' <- traverse (\(u, params, ret) -> mapUnion u <&> (, params, ret)) unions
          mkType $ TCon dd ts unions'
        _ -> pure tid

    mapUnion :: T.EnvUnion -> Infer T.EnvUnion
    mapUnion uid = getUnion' uid >>= \(baseUid, uu) -> if baseUid `Set.member` excludedUnions
      then pure baseUid
      else traverse mapType uu >>= \u -> do
        newUnion <- for u.union $ traverse $ \case
            T.Env eid vars localities level -> do
              vars' <- traverse (\(v, l, t) -> mapVar v <&> (, l, t)) vars
              pure $ T.Env eid vars' localities level
            e -> pure e
        nextUnion baseUid $ u { T.union = newUnion }

    mapVar :: T.Variable -> Infer T.Variable
    mapVar = traverse mapType >=> \case
      ogclass@(T.DefinedClassFunction cfd _ selfID uci) -> getType selfID <&> \case
        TO (T.TVar tv) | Set.member tv tvs -> T.DefinedClassFunction cfd snapshot selfID uci
        _ -> ogclass
      v -> pure v


-- Constructs an environment from all the instantiations.
--  We need the instantiations, because not all instantiations of a function can come up in the environment.
--  But, when there is a TVar in the type, it means all instantiated types of TVars must be there.
withEnv :: R.Env -> Infer (T.ClassInstantiationAssocs, a) -> Infer (T.Env, a)
withEnv renv x = do
  let eid = renv.envID
  pf "BEGIN ENV: %" (pp renv)

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

  pf "OLD ENV: %s\nMODIFIED INSTANTIATIONS: %s\nRESULTING ENV: %s" (pp renv) (pp $ Set.toList modifiedInstantiations) (pp newEnvVars)


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


addMember :: Def.Location -> Type TC -> Def.MemName -> Infer (Type TC)
addMember loc ogType memname = do
  t <- fresh  -- we don't know its type yet.
  RWS.modify $ \s -> s { memberAccess = (ogType, memname, t, loc) : s.memberAccess }

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
          mkType $ TCon dd tvs unions
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."

mkPtr :: Type TC -> Infer (Type TC)
mkPtr insidePtr = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> mkType $ p.mkPtr insidePtr
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap Prelude.ptrTypeName (\(DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(DD _ scheme _ _) -> do
          (tvs@[innerTyVar], unions) <- instantiateScheme mempty scheme
          (error "should it even fail?", innerTyVar) `uni` (Nothing, insidePtr)
          mkType $ TCon dd tvs unions

        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show Prelude.ptrTypeName <> "'."


mkType :: TypeF TC T.TypeID -> Infer T.TypeID
mkType t = lift $ do
  tid <- CompilerContext.nextTypeID
  CompilerContext.modifyTypeUni $ IntMap.insert tid.fromTypeID $ Right t
  pure tid

mkUnion :: T.EnvUnionF TC T.TypeID -> Infer T.EnvUnion
mkUnion u = lift $ do
  uid <- CompilerContext.nextUnionUniID
  CompilerContext.modifyUniUni $ IntMap.insert uid.fromUnionUniID $ Right u
  pure uid

mkUnion' :: T.EnvUnionF TC T.TypeID -> Infer T.EnvUnion
mkUnion' u = lift $ do
  newUid <- newUnionID
  uid <- CompilerContext.nextUnionUniID
  CompilerContext.modifyUniUni $ IntMap.insert uid.fromUnionUniID $ Right $ u { T.unionID = newUid }
  pure uid

-- adds more stuff to the union and adds a reference for the old one to the union.
nextUnion :: T.EnvUnion -> T.EnvUnionF TC T.TypeID -> Infer T.EnvUnion
nextUnion oldUnionID union = lift $ do
  nextUnionID <- CompilerContext.nextUnionUniID
  CompilerContext.modifyUniUni
    $ IntMap.insert oldUnionID.fromUnionUniID (Left nextUnionID.fromUnionUniID)
    . IntMap.insert nextUnionID.fromUnionUniID (Right union)
  pure nextUnionID


-------------------------------
--        UNIFICATION

uni :: (Def.Location, Type TC)-> (Maybe Def.Location, Type TC) -> Infer ()
uni (l1, t1) (l2, t2) = do
  pf "% `uni` %" t1 t2
  -- whenPrintingUni $ pf "%" (dbgSubst su)
  (l1, t1) `unify` (l2, t2)

  -- whenPrintingUni $ pf "% `subst AFTER uni` %" (subst su' t1) (subst su' t2)

uniMany :: (Def.Location, [Type TC]) -> (Maybe Def.Location, [Type TC]) -> Infer ()
uniMany ts1 ts2 = do
  whenPrintingUni $ pf "uni many!"
  unifyMany ts1 ts2

whenPrintingUni :: Def.Context -> Infer ()
whenPrintingUni x = do
  shouldPrint <- RWS.asks shouldPrintUnification
  case shouldPrint of
    Nothing -> pure ()
    Just line -> Def.unsilenceablePrintInContext $ pf "%: %" line x

-- maybe later get the location from the type?
constrain :: Def.Location -> Type TC -> (ClassDef TC, T.PossibleInstances TC) -> Infer ()
constrain location t cdi = 
    addConstraint location t cdi


------

unify :: (Def.Location, Type TC) -> (Maybe Def.Location, Type TC) -> Infer ()
unify (locl, tttl) (locr, tttr) = do
  (ttl, tl) <- getType' tttl
  (ttr, tr) <- getType' tttr
  pf "% ?? %" tl tr
  if ttl == ttr
    then pure ()
    else case (tl, tr) of
    (l, r) | l == r -> pure ()
    (TO (TyVar tyv), _) -> do
      let bind' = bind (Left (locl, locr))
      (ttl, tyv) `bind'` ttr
      pf "miaaaaau"
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint locl ttr klass

    (_, TO (TyVar tyv)) -> do
      let bind' = bind (Right (locr, locl))
      (ttr, tyv) `bind'` ttl
      for_ tyv.tyvConstraints $ \klass ->
        addConstraint locl ttl klass

    (TFun lenv lps lr, TFun renv rps rr) -> do
      unifyMany (locl, lps) (locr, rps)
      unify (locl, lr) (locr, rr)
      lenv `unifyFunEnv` renv

    (TCon t ta unions, TCon t' ta' unions') | t == t' -> do
      unifyMany (locl, ta) (locr, ta')
      zipWithM_ unifyFunEnv (unions <&> \(u, _, _) -> u) (unions' <&> \(u, _, _) -> u)  -- i don't think we need to unify the types associated with EnvUnion, right???

    (_, _) -> do
      ttl' <- presentType ttl
      ttr' <- presentType ttr
      err $ TypeMismatch (locl, ttl') (locr, ttr')

unifyMany :: (Def.Location, [Type TC]) -> (Maybe Def.Location, [Type TC]) -> Infer ()
unifyMany (_, []) (_, []) = nun
unifyMany (ll, tl:ls) (lr, tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
  unify (ll, tl) (lr, tr)
  unifyMany (ll, ls) (lr, rs)

unifyMany tl tr = do
  tl' <- traverse presentType $ snd tl
  tr' <- traverse presentType $ snd tr
  err $ MismatchingNumberOfParameters (fst tl, tl') (fst tr, tr')

addConstraint :: Def.Location -> Type TC -> (ClassDef TC, T.PossibleInstances TC) -> Infer ()
addConstraint location ttid (klass, instances) = do
  pf "adding constraint"
  (tid, t) <- getType' ttid
  case t of
      TCon dd _ _ -> do
        let mSelectedInst = instances !? dd
        case mSelectedInst of
          Nothing -> do
            err $ DataDefDoesNotImplementClass location dd klass

          Just _ -> do
            -- Don't do anything? like, we only have to confirm that the instance gets applied, right?
            pure ()

      TO (TVar tv) -> do
        unless (Set.member klass tv.tvClasses) $ do
          err $ TVarDoesNotConstrainThisClass location tv klass

      TO (TyVar tyv) -> do
        -- create new tyvar with both classes merged!
        let cids = (klass, instances) : tyv.tyvConstraints
        newtyv <- freshTyVarInSubst cids
        newtyvid <- lift CompilerContext.nextTypeID
        lift $ CompilerContext.modifyTypeUni $
            IntMap.insert newtyvid.fromTypeID $ Right $ TO $ TyVar newtyv
        pf "TVAR MAKER: New tyvar %. In %." newtyv tyv
        let bind' = bind (Left (location, Nothing))
        (tid, tyv) `bind'` newtyvid

      TFun {} -> do
        t <- presentType tid
        err $ FunctionTypeConstrainedByClass location t klass

bind :: Either (Def.Location, Maybe Def.Location) (Maybe Def.Location, Def.Location) -> (T.TypeID, T.TyVar) -> Type TC -> Infer ()
bind loc (tyvid, tyv) tid = do
  t <- getType tid
  case t of
    TO (TyVar tyv') | tyv == tyv' -> nun  -- TODO: this is just in case, because same fresh variables should have the same TypeIDs.
    _ -> do
      tyVarOccursInRightType <- occursCheck tyv tid
      tid' <- presentType tid
      if tyVarOccursInRightType
        then err $ InfiniteType loc tyv tid'
        else do
          pf "bind: % -> %" tyvid tid
          lift $ CompilerContext.modifyTypeUni $ IntMap.insert tyvid.fromTypeID (Left tid.fromTypeID)

unifyFunEnv :: T.EnvUnion -> T.EnvUnion -> Infer ()
unifyFunEnv lenv renv = do
  unionID <- newUnionID
  unionUniID <- lift CompilerContext.nextUnionUniID


  (baseLEnv, lenv'@T.EnvUnion { T.unionID = _ }) <- getUnion' lenv
  (baseREnv, renv'@T.EnvUnion { T.unionID = _ }) <- getUnion' renv
  let union2envset = Set.fromList . (\(T.EnvUnion { T.union = union }) -> union)
      envset2union = Set.toList
      funEnv = envset2union $ union2envset lenv' <> union2envset renv'

  let env = T.EnvUnion { T.unionID = unionID, T.union = funEnv }
  lift $ CompilerContext.modifyUniUni
    $ IntMap.insert unionUniID.fromUnionUniID (Right env)       -- insert union itself
    . IntMap.insert baseLEnv.fromUnionUniID (Left unionUniID.fromUnionUniID)   -- insert ref
    . IntMap.insert baseREnv.fromUnionUniID (Left unionUniID.fromUnionUniID)   -- insert ref


getUnion :: T.EnvUnion -> Infer (T.EnvUnionF TC T.TypeID)
getUnion = fmap snd . getUnion'

getUnion' :: T.EnvUnion -> Infer (T.EnvUnion, T.EnvUnionF TC T.TypeID)
getUnion' uid = do
  tu <- lift CompilerContext.getTypeUni
  pure $ T.getUnionFromUni tu uid

getType :: Type TC -> Infer (TypeF TC T.TypeID)
getType = fmap snd . getType'

getType' :: Type TC -> Infer (Type TC, TypeF TC T.TypeID)
getType' tid = do
  tu <- lift CompilerContext.getTypeUni
  pure $ T.getTypeFromUni tu tid

presentType :: Type TC -> Infer Def.Context
presentType = getType >=> traverse presentType >=> \case
  TCon tc ts unions -> do
    us <- traverse (\(u, _, _) -> presentUnion u) unions
    pure $ pf "(% % %)" (ppDef tc) ts us
  TFun union ts t -> presentUnion union <&> \u -> pf "(%% -> %)" u ts t
  TO (TVar tv) -> pure $ pp tv
  TO (TyVar tyv) -> pure $ pp tyv

presentUnion :: T.EnvUnion -> Infer Def.Context
presentUnion = getUnion >=> traverse presentType >=> \u ->
  pure $ pf "%%" u.unionID (Def.encloseSepBy "{" "}" ", " $ u.union <&> \(_, _, assocs, env) -> pf "(%, %)" assocs env :: Def.Context)

presentFunctionType :: Function TC -> Infer Def.Context
presentFunctionType fn = do
  env <- traverse presentType fn.functionDeclaration.functionEnv
  params <- traverse presentType (snd <$> fn.functionDeclaration.functionParameters)
  ret <- presentType fn.functionDeclaration.functionReturnType
  pure $ pf "%% -> %" env params ret

occursCheck :: T.TyVar -> Type TC -> Infer Bool
occursCheck tyv t = do
  pf "OCCURS?!"
  tyvs <- fmap (Set.map snd) $ lift $ findFTV t
  pure $ Set.member tyv tyvs

err :: Monad m => TypeError -> RWST r [TypeError] s m ()
err te = RWS.tell [te]


-- Sikanokonokonokokośtantan
nun :: Infer ()
nun = pure ()






-------------------
-- Substitutable --
-------------------

-- data SubstCache = SubstCache
--   { functions :: ()
--   , instances :: ()
--   , classes :: ()
--   , unions :: ()
--   }

newtype FTV a = FTV { fromFTV :: Reader T.TypeUni a } deriving (Functor, Applicative, Monad)

instance Semigroup a => Semigroup (FTV a) where
  fl <> fr = liftA2 (<>) fl fr
    
instance Monoid a => Monoid (FTV a) where
  mempty = pure mempty


findFTV :: Substitutable a => a -> CompilerContext (Set (Type TC, T.TyVar))
findFTV x = do
  typeUni <- CompilerContext $ RWS.gets CompilerContext.globalTypeUni
  let tyvars = Reader.runReader (fromFTV $ ftv x) typeUni
  pure tyvars

class Substitutable a where
  ftv :: a -> FTV (Set (Type TC, T.TyVar))



instance Substitutable (T.Mod TC) where
  -- TODO: We're not yet ftv-ing Datatypes, because it might lead to loops. Same with functions. I'll probably need another memoization system.
  ftv m = ftv m.topLevelStatements <> ftv m.exports -- <> ftv m.datatypes

instance Substitutable Int where
  ftv = mempty

instance Substitutable (ClassDef TC) where
  ftv = mempty  -- no FTVs in declarations. will need to get ftvs from associated types and default functions when they'll be implemented.

instance Substitutable (InstDef TC) where
  -- TODO: substitute ALL
  ftv inst = foldMap ftv inst.instFuns

instance Substitutable (InstFun TC) where
  -- PERF: substitute ALL
  ftv ifn = ftv ifn.instFunDec <> ftv ifn.instFunBody

instance Substitutable (Exports TC) where
  -- PERF: substitute ALL
  ftv e = ftv e.functions

instance Substitutable (AnnStmt TC) where
  ftv = cata $ \(O (O (Def.Annotated _ (Def.Located _ stmt)))) -> bifold $ first ftv stmt

instance Substitutable a => Substitutable (StmtF TC (Expr TC) a) where
  ftv stmt = case bimap ftv ftv stmt of
    Return ret -> ftv ret
    Mutation _ _ _ accesses e -> ftv accesses <> e
    s -> bifold s

instance Substitutable (MutAccess TC) where
  ftv = const mempty

instance (Substitutable expr, Substitutable stmt) => Substitutable (CaseF TC expr stmt) where
  ftv kase = ftv kase.deconstruction <> ftv kase.caseCondition <> ftv kase.caseBody

instance Substitutable (Decon TC) where
  ftv = cata $ \(N t d) -> ftv t <> case d of
    CaseVariable _ -> mempty
    CaseConstructor _ ftvs -> mconcat ftvs
    CaseRecord _ ftvs -> foldMap snd ftvs
    CaseIgnore -> mempty

instance Substitutable (Expr TC) where
  ftv = cata $ \(N et ee) -> ftv et <> case ee of
    As e t -> e <> ftv t
    Lam env params body -> ftv env <> ftv params <> body
    Var v _ -> ftv v
    e -> fold e

instance Substitutable (T.ExprNode TC) where
  ftv en = ftv en.t

instance Substitutable T.TypeID where
  ftv tid = FTV Reader.ask >>= \tuni ->
    let ftvType ttid =
          let (baseid, tt) = fmap2 ftvType $ T.getTypeFromUni tuni ttid
          in case tt of
              TO (TyVar tyv) -> pure $ Set.singleton (baseid, tyv)
              t -> seqfold t
    in ftvType tid


instance Substitutable (T.LamDec TC) where
  ftv (T.LamDec _ env) = ftv env

instance Substitutable t => Substitutable (T.VariableF TC t) where
  ftv _ = mempty


instance Substitutable Def.UniqueVar where
  ftv _ = mempty

instance Substitutable Def.UniqueClassInstantiation where
  ftv _ = mempty

instance Substitutable Def.MemName where
  ftv _ = mempty

instance Substitutable Def.UniqueFunctionInstantiation where
  ftv _ = mempty

instance Substitutable Def.Location where
  ftv = const mempty


instance Substitutable (Function TC) where
  ftv fn = liftA2 (\\) (ftv fn.functionBody) (ftv fn.functionDeclaration)

instance Substitutable (FunDec TC) where
  ftv (FD _ _ params ret other) = ftv params <> ftv ret <> ftv other.functionAssociations -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 

instance Substitutable (T.FunOther TC) where
  ftv other = ftv other.functionAssociations

instance Substitutable T.TypeAssociation where
  ftv (T.TypeAssociation from to _ _ _ _) = ftv from <> ftv to

-- -- FIX: FUCK
-- instance Substitutable a => Substitutable (IORef a) where
--   ftv ioref = ftv $ unsafePerformIO $ IORef.readIORef ioref
--   subst su ioref = unsafePerformIO $ do
--     IORef.modifyIORef ioref (subst su)
--     pure ioref

instance Substitutable (T.FunctionTypeAssociation TC) where
  ftv (T.FunctionTypeAssociation _ to _ _) = ftv to

-- instance Substitutable a => Substitutable (TypeF TC a) where
--   ftv = \case
--     TO (TyVar tyv) -> pure $ Set.singleton (tyv)
--     t -> trafold ftv t


instance Substitutable t => Substitutable (T.EnvUnionF TC t) where
  ftv (T.EnvUnion _ envs) = ftv envs


instance Substitutable t => Substitutable (T.EnvF TC t) where
  ftv (T.Env _ vars _ _) = foldMap (\(_, _, t) -> ftv t) vars
  ftv (T.RecursiveEnv _ _) = mempty

  -- redundant work. memoize this shit also.
  -- subst su (T.Env eid env locs currentEnvStack) = T.Env eid (newEnvVars <> optionalAddition) locs currentEnvStack
  --   where
  --     newEnvVars = undefined  -- TODO nocheckin  -- foldMap (tryExpandEnvironmentOfClass . (\(v, l, t) -> (subst su v, l, subst su t))) env

  --     currentLevel = Def.envStackToLevel currentEnvStack

  --     optionalAddition = undefined
  --     -- TODO nocheckin
  --     -- optionalAddition :: [(T.Variable, Def.Locality, Type TC)]
  --     -- optionalAddition = case su of
  --     --   EnvAddition adds ->
  --     --     let oldVars = Set.fromList newEnvVars
  --     --     in filter (`Set.notMember` oldVars) $ fmap (\(v, l, t) -> (subst su v, l, subst su t)) $ fromMaybe mempty $ adds !? eid
  --     --   _ -> mempty

  --     -- tryExpandEnvironmentOfClass :: (T.Variable, Def.Locality, Type TC) -> [(T.Variable, Def.Locality, Type TC)]
  --     -- tryExpandEnvironmentOfClass = \case
  --     --   vlt@(T.DefinedClassFunction cfd@(CFD cd _ _ _ () _) snap self@(Fix (TCon dd _ _)) uci, _, t) ->
  --     --     -- failable: select instantiated function env. this might have been after errors, so we're not assuming anything.
  --     --     let mvars = do
  --     --           insts <- snap !? cd
  --     --           currentInst <- insts !? dd
  --     --           currentFun <- find (\ifn -> ifn.instClassFunDec == cfd) currentInst.instFuns

  --     --           unT <- case project t of
  --     --             TFun union _ _ -> Just union.union
  --     --             _ -> Nothing
  --     --           (_, ufi, assocs, e) <- find (\case { (Just uci', _, _, _) -> uci == uci'; _ -> False }) unT
  --     --           pure (currentFun, currentInst, ufi, assocs, e)
  --     --     in case mvars of
  --     --       -- this probably is not needed anymore!
  --     --       Just (ifn, currentInst, ufi, assocs, T.Env instEnvID instEnvVars _ instEnvStack)
  --     --         -- this function is from this or "higher" environment.
  --     --         -- | Def.envStackToLevel instEnvStack <= currentLevel ->
  --     --         | instEnvStack `Def.isHigherOrSameLevel` currentEnvStack ->
  --     --         -- | Set.member instEnvID (Set.fromList (eid : currentEnvStack)) ->
  --     --           let fnLocality = if Def.envStackToLevel instEnvStack < currentLevel
  --     --                 then Def.FromEnvironment (Def.envStackToLevel instEnvStack)
  --     --                 else Def.Local
  --     --           in [(T.DefinedClassFunction cfd snap self uci, fnLocality, t)]  -- TEMP: we are redoing the "DefinedClassFunction" (instead of just dropping DefinedFunction), because currently in Mono we rely on this.
  --     --           -- NOTE: NOTICE THAT WE TAKE currentInst instead of using the recursive instance. This is because we don't substitute recursive instances (because we have no memoization).

  --     --         -- we need "take out" variables from this function.
  --     --         -- NOTE: we add the `eid` to currentEnvStack, because if inst is actually INSIDE the function, it would have `eid` in its env stack. We need it, because (due to how insts are resolved) we might have an instance from a completely different place, which will need to leave alone and create an env mod for it.
  --     --         | (eid : currentEnvStack) `Def.isHigherOrSameLevel` instEnvStack -> []  -- NOTE: this is taken care of in `addExtraToEnv` and `EnvAdditions`

  --     --         | otherwise -> [vlt]  -- do not touch it. might be a class function from a different scope and will need to be "completed."
  --     --           -- let
  --     --           --   usedVarsInThisEnv = Set.fromList $ env <&> \(v, _, t) -> (v, t)
  --     --           --   usedVarsInInst = unpackFromEnvironment instLevel instEnvVars
  --     --           --   usedVarsInInstDeduped = filter (\(v, _, t) -> Set.notMember (v, t) usedVarsInThisEnv) usedVarsInInst
  --     --           -- in usedVarsInInstDeduped

  --     --       _ -> [vlt]  -- there was an error probably.
  --     --   vlt -> [vlt]
  --     -- (\(v, l, t) -> (subst su v, l, subst su t))
  --     -- RELATED TO "nonlocal instances and their environments"
  --     unpackFromEnvironment :: Def.Level -> [(T.Variable, Def.Locality, Type TC)] -> [(T.Variable, Def.Locality, Type TC)]
  --     unpackFromEnvironment instEnvLevel
  --       = map (\(v, l, t) ->             -- adjust locality from the context of this environment.
  --           let varLevel = case l of
  --                 Def.Local -> instEnvLevel
  --                 Def.FromEnvironment lev -> lev
  --               newLocality = if varLevel == currentLevel
  --                 then Def.Local
  --                 else Def.FromEnvironment varLevel
  --           in (v, newLocality, t))
  --       . filter (\(_, l, _) ->          -- filter variables, which should not even be in this environment.
  --           let varLevel = case l of
  --                 Def.Local -> instEnvLevel
  --                 Def.FromEnvironment lev -> lev
  --           in varLevel <= currentLevel)

  -- subst su env = subst su <$> env


instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv

instance Substitutable a => Substitutable (NonEmpty a) where
  ftv = foldMap ftv

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv

instance (Substitutable a, Substitutable b, Substitutable c) => Substitutable (a, b, c) where
  ftv (a, b, c) = ftv a <> ftv b <> ftv c

instance (Substitutable a, Substitutable b, Substitutable c, Substitutable d) => Substitutable (a, b, c, d) where
  ftv (a, b, c, d) = ftv a <> ftv b <> ftv c <> ftv d

instance Substitutable a => Substitutable (Maybe a) where
  ftv = maybe mempty ftv




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
fresh = do
  tid <- lift CompilerContext.nextTypeID
  tyv <- freshTyVar
  pf "fresh: % %" tid tyv
  lift $ CompilerContext.modifyTypeUni $
    IntMap.insert tid.fromTypeID $ Right $ TO $ TyVar tyv
  pure tid

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyVar :: Infer T.TyVar
freshTyVar = do
  uniq <- liftIO newUnique
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV uniq (letters !! nextVar) mempty

freshTyVarInSubst :: [(ClassDef TC, T.PossibleInstances TC)] -> Infer T.TyVar
freshTyVarInSubst cdis = do
  uniq <- liftIO newUnique
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV uniq (letters !! nextVar) cdis

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']


singleEnvUnion :: Maybe Def.UniqueClassInstantiation -> Def.UniqueFunctionInstantiation -> [Type TC] -> T.Env -> Infer T.EnvUnion
singleEnvUnion uci ufi tassocs env = do
  uid <- newUnionID
  mkUnion $ T.EnvUnion { T.unionID = uid, T.union = [(uci, ufi, tassocs, env)] }

cloneUnion :: T.EnvUnion -> T.EnvUnionF TC (Type TC) -> Infer T.EnvUnion
cloneUnion uuid union = do
  uid <- newUnionID
  lift $ CompilerContext.modifyUniUni $ IntMap.insert uuid.fromUnionUniID $ Right $ union { T.unionID = uid }
  pure uuid

-- Creates an empty union.
emptyUnion :: Infer T.EnvUnion
emptyUnion = do
  uid <- newUnionID
  mkUnion $ T.EnvUnion uid []


findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList

classFunDecToClassType :: ClassFunDec R -> ClassType R
classFunDecToClassType (CFD _ _ params ret _ _) =
  Fix $ NormalType $ TFun undefined undefined undefined


------------------------------------------
--          DATATYPES n shiiii
------------------------------------------

-- TODO: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer = RWST Context [TypeError] TypecheckingState CompilerContext  -- normal inference

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe (Type TC)
  , shouldPrintUnification :: Maybe Int  -- should be in PrintContext, but we cannot modify the inner monad. we require a redesign!
  }


data TypecheckingState = TypecheckingState
  { tvargen :: TVarGen

  , memoFunction :: Memo (Function R) (Function TC)
  , memoDataDefinition :: Memo (DataDef R) (DataDef TC)
  , memoClass :: Memo (ClassDef R) (ClassDef TC)
  , memoInstance :: Memo (InstDef R) (InstDef TC)

  , variableTypes :: Map Def.UniqueVar (Type TC)

  , memberAccess :: [(Type TC, Def.MemName, Type TC, Def.Location)]  -- ((a :: t1).mem :: t2)
  , classFunctionUnions :: [(T.EnvUnion, ClassFunDec TC, Type TC, T.PossibleInstances TC)]  -- TODO: currently unused. remove later.
  , associations :: [(T.TypeAssociation, T.ScopeSnapshot TC)]

  -- HACK?: track instantiations from environments. 
  --  (two different function instantiations will count as two different "variables")
  , instantiations :: Set (T.Variable, Type TC)

  , envStack :: [Def.EnvID]
  }

emptySEnv :: TypecheckingState
emptySEnv = TypecheckingState
  { tvargen = newTVarGen

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
  }



newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


newtype TypeIDGen = TIG Int

newTypeIDGen :: TypeIDGen
newTypeIDGen = TIG 0

newtype UnionUniIDGen = UUIDG Int

newUnionIDGen :: UnionUniIDGen
newUnionIDGen = UUIDG 0




type PType = Def.Context
data TypeError
  = InfiniteType (Either (Def.Location, Maybe Def.Location) (Maybe Def.Location, Def.Location)) T.TyVar (PType)
  | TypeMismatch (Def.Location, PType) (Maybe Def.Location, PType)
  | MismatchingNumberOfParameters (Def.Location, [PType]) (Maybe Def.Location, [PType])
  | AmbiguousType Def.Location T.TyVar

  | DataTypeDoesNotHaveMember Def.Location (DataDef TC) Def.MemName
  | DataTypeIsNotARecordType Def.Location (DataDef TC) Def.MemName
  | FunctionIsNotARecord Def.Location (PType) Def.MemName
  | TVarIsNotARecord Def.Location (TVar TC) Def.MemName

  | DataDefDoesNotImplementClass Def.Location (DataDef TC) (ClassDef TC)
  | TVarDoesNotConstrainThisClass Def.Location (TVar TC) (ClassDef TC)
  | FunctionTypeConstrainedByClass Def.Location (PType) (ClassDef TC)
  | InstanceFunctionTypeNotMatchingClass (Def.Location, ClassFunDec TC) (Def.Location, Function TC) [(ClassType TC, PType)]


instance Error TypeError where
  toError source = \case
    InfiniteType _ tyv t -> error "InfiniteType" --undefined 
    TypeMismatch (loc, t) (mloc', t') -> renderError source (pf "type mismatch between % and %" (pp t) (pp t')) $ case mloc' of
      Nothing -> ln (loc, Just $ pf "this one has type %" (pp t))
      Just loc' -> lns [(loc, Just $ pf "this one has type %" (pp t)), (loc', Just $ pf "this one has type %" (pp t'))]

    MismatchingNumberOfParameters (loc, ts) (mloc, ts') ->
      let additionalLocation = case mloc of
            Nothing -> mempty
            Just l -> [(l, Nothing)]

      in renderError source (pf "mismatching number of parameters: % vs %" ts ts') $ ln $ (loc, Nothing)  -- right now the right location is bogus,so there is no need to show it.
    AmbiguousType _ tyv -> pf "Ambigous type %" tyv --printf "Ambiguous type: %s" (sctx $ pp tyv)

    DataTypeDoesNotHaveMember location dd memname -> renderError source (pf "datatype % does not have member %" (ppDef dd) memname) $ ln (location, Nothing) --printf "Record type %s does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
    DataTypeIsNotARecordType location dd memname -> renderError source (pf "attempt to subscript % with %, but it's not a record type" (ppDef dd) (pp memname)) $ ln (location, Nothing) --printf "%s is not a record type and thus does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
    FunctionIsNotARecord _ t _ -> error "FunctionIsNotARecord" --printf "Cannot subscript a function (%s)." (pp t)
    TVarIsNotARecord _ tv _ -> error "TVarIsNotARecord" --printf "Cannot subscript a type variable. (%s)" (pp tv)
    DataDefDoesNotImplementClass loc dd cd -> renderError source (pf "datatype % does not implement class %" (ppDef dd) (ppDef cd)) $ ln (loc, Nothing) --printf "Type %s does not implement instance of class %s." (sctx $ pp ut) (sctx $ pp cd.classID)
    TVarDoesNotConstrainThisClass location tv cd -> renderError source (pf "tvar % is not constrained by class %" tv (ppDef cd)) $ ln (location, Nothing) --printf "TVar %s is not constrained by class %s." (pp tv) (pp cd.classID)
    FunctionTypeConstrainedByClass _ t cd -> error "FunctionTypeConstrainedByClass"
    _ -> undefined
--      printf "Function type %s constrained by class %s (function types cannot implement classes, bruh.)" (pp t) (pp cd.classID)

-- copied verbatim from Resolver. I mean, the error interface should change anyway, so whatever.
ln :: a -> NonEmpty a
ln = NonEmpty.singleton

lns :: [a] -> NonEmpty a
lns = NonEmpty.fromList

fs :: String -> Text
fs = fromString

-- not sure if we have to have a show instance
-- instance Show TypeError where
--   show = \case
--     InfiniteType tyv t -> unwords ["InfiniteType", sctx $ pp tyv, sctx $ pp t]
--     TypeMismatch t t' -> printf "Type Mismatch: %s %s" (sctx $ pp t) (sctx $ pp t')
--     MismatchingNumberOfParameters ts ts' -> printf "Mismatching number of parameters: (%d) %s (%d) %s" (length ts) (sctx $ Def.ppList pp ts) (length ts') (sctx $ Def.ppList pp ts')
--     AmbiguousType tyv -> printf "Ambiguous type: %s" (sctx $ pp tyv)

--     DataTypeDoesNotHaveMember (DD ut _ _ _) memname -> printf "Record type %s does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
--     DataTypeIsNotARecordType (DD ut _ _ _) memname -> printf "%s is not a record type and thus does not have member %s." (sctx $ pp ut) (sctx $ pp memname)
--     FunctionIsNotARecord t _ -> printf "Cannot subscript a function (%s)." (pp t)
--     TVarIsNotARecord tv _ -> printf "Cannot subscript a type variable. (%s)" (pp tv)
--     DataDefDoesNotImplementClass (DD ut _ _ _) cd -> printf "Type %s does not implement instance of class %s." (sctx $ pp ut) (sctx $ pp cd.classID)
--     TVarDoesNotConstrainThisClass tv cd -> printf "TVar %s is not constrained by class %s." (pp tv) (pp cd.classID)
--     FunctionTypeConstrainedByClass t cd ->
--       printf "Function type %s constrained by class %s (function types cannot implement classes, bruh.)" (pp t) (pp cd.classID)



-- zipWith which ensures lists are equal.
--   I want to encode this at the function/assertion level.
{-# NOINLINE [1] exactZipWith #-}  -- See Note [Fusion for zipN/zipWithN]
exactZipWith :: (a->b->c) -> [a]->[b]->[c]
exactZipWith f = go
  where
    go (x:xs) (y:ys) = f x y : go xs ys
    go [] [] = []

    go [] _ = error "right list is longer"
    go _ [] = error "left list is longer"



--- Extra ExprNode operations

askUni :: Fix (ExprNode TC nodeF) -> (Def.Location, Type TC)
askUni = asksNode $ \ne -> (ne.loc, ne.t)

askType :: Fix (ExprNode TC nodeF) -> Type TC
askType = asksNode T.t

-- shitty convenienve function for the right side of `uni`
-- askUniR :: Expr TC -> (Maybe Def.Location, Type TC)
-- askUniR = first Just . askUni

justType :: Type TC -> (Maybe Def.Location, Type TC)
justType = (Nothing,)


-----
-- DEBUG
----


printUni :: Int -> [Def.Ann] -> Infer a -> Infer a
printUni line anns ix = if Def.ADebugUnification `elem` anns
  then do
    oldAssocLength <- RWS.gets $ length . associations
    x <- RWS.local (\r -> r { shouldPrintUnification = Just line }) ix
    -- also other shit
    assocs <- RWS.gets associations
    let newAssocs = take (length assocs - oldAssocLength) assocs
    Def.unsilenceablePrintInContext $ pf "Assocs generated right now: %" $ fst <$> newAssocs
    pure x
  else ix

resetUniPrint :: Infer a -> Infer a
resetUniPrint ix = RWS.local (\r -> r { shouldPrintUnification = Nothing }) ix


dbgAssociations :: String -> [(T.TypeAssociation, T.ScopeSnapshot TC)] -> Infer ()
dbgAssociations title associations = pf "Associations (%): %" title (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation from to _ uci ufi _, _) -> pf "(%) %: %" (pp (uci, ufi)) (pp from) (pp to) :: String)




-- This is currently how we extract unions from types.
-- This needs to be done, because custom types need to track which unions were used.
-- TODO: this should probably be made better. Maybe store those unions in DataDef?
extractUnionsFromDataType :: DataDef TC -> Infer [(T.EnvUnion, [Type TC], Type TC)]
extractUnionsFromDataType (DD _ _ (Right dcs) _) =
  trafold extractUnionsFromConstructor dcs

extractUnionsFromDataType dd@(DD ut _ (Left drs) _) =
  flip trafold drs $ \(Def.Annotated _ (_, t)) -> mapUnion ut t

extractUnionsFromConstructor :: DataCon TC -> Infer [(T.EnvUnion, [Type TC], Type TC)]
extractUnionsFromConstructor (DC (DD ut _ _ _) _ ts _) = trafold (mapUnion ut) ts

-- TODO: clean up all the mapUnion shit. think about proper structure.
mapUnion :: Def.UniqueType -> Type TC -> Infer [(T.EnvUnion, [Type TC], Type TC)]
mapUnion ut = getType >=> \case
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  TCon (DD tut _ _ _) paramts conUnions
    -- breaks cycle with self referential datatypes.
    | tut == ut -> trafold (mapUnion ut) paramts
    | otherwise -> (conUnions <>) <$> trafold (mapUnion ut) paramts

  TFun u args ret -> liftA2 (\l r -> (u, args, ret) : l <> r) (trafold (mapUnion ut) args) (mapUnion ut ret)
  TO _ -> pure []


trafold :: (Monoid b, Traversable t, Applicative f) => (a -> f b) -> t a -> f b
trafold f = fmap fold . traverse f

seqfold :: (Monoid b, Traversable t, Applicative f) => t (f b) -> f b
seqfold  = fmap fold . sequenceA


-- the COCK operator
infixr 1 &=>
(&=>) :: Functor m => (a -> m b) -> (b -> c) -> a -> m c
(&=>) f g = fmap g . f

instance Foldable ((,,,) a b c) where
  foldMap f (_, _, _, x) = f x

instance Traversable ((,,,) a b c) where
  traverse f (a, b, c, x) = (a, b, c,) <$> f x
