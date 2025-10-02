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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStrict #-}

module Typecheck (typecheck, TypeError(..)) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.Trans.RWS.Strict (runRWST, RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (Base, cata, embed)
import Control.Monad (replicateM, zipWithM_, unless, (<=<), (>=>))
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
import Data.Maybe (fromMaybe, mapMaybe, catMaybes, isJust)
import Control.Applicative (liftA3)
import Data.List.NonEmpty (NonEmpty, (<|))
import Misc.Memo (memo, Memo(..), emptyMemo)
import qualified AST.Common as Common
import AST.Prelude (Prelude)
import qualified AST.Prelude as Prelude
import AST.Common (Module, AnnStmt, StmtF (..), Type, CaseF (..), ExprF (..), ClassFunDec (..), DataCon (..), DataDef (..), ClassType, ClassTypeF (..), TypeF (..), TVar (..), Function (..), functionEnv, Exports (..), ClassDef (..), InstDef (..), InstFun (..), functionOther, FunDec (..), Decon, DeconF (..), IfStmt (..), Expr, ExprNode (..), DeclaredType (..), XClassFunDec, MutAccess (..), LitType (..), asksNode)
import AST.Resolved (R)
import AST.Typed ( TC, Scheme(..), TOTF(..), Match, MatchF (..) )
import AST.Def ((:.)(..), PP (..), Binding (..), BinOp (..), ppDef, fmap2, traverse2, Log, LogType (T_AST, T_Uni), PrintfType, TypeID, ClassInstID (..))
import qualified AST.Def as Def
import Data.String (fromString)
import Error (Error (..), renderError)
import AST.Typed (FunOther(..))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Monad.Trans.Class (lift)
import Text.Megaparsec.Pos (unPos)
import Text.Megaparsec (sourceLine)
import InterModular (InterModular, imLift)
import qualified InterModular
import Control.Monad.Trans.Reader (Reader)
import qualified Control.Monad.Trans.Reader as Reader
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.IntMap.Strict as IntMap
import qualified TypingContext as TC
import Stats (tStmtNum, tExprNum, numSeparateUnifications, numTVMaps, numCSMaps)
import BaseCtx (countUp)
import Control.Monad.Trans.RST (RST)
import qualified Control.Monad.Trans.RST as RST
import AST.Resolved (FunOther(..))

pc :: (PP a, Log p, p ~ x unit, unit ~ ()) => a -> p
pc = Def.pc T_AST

pf :: PrintfType r => String -> r
pf = Def.printf T_AST


phase :: (Log pctx, x () ~ pctx) => String -> pctx
phase = Def.phase T_AST


----------- TO REMEMBER -----------------
-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)

typecheck :: Maybe Prelude -> Module R -> InterModular ([TypeError], Module TC)
typecheck mprelude rStmts = {-# SCC typecheck #-} do
    let tcContext = Ctx { prelude = mprelude, returnType = Nothing }
    let senv = emptySEnv  -- we add typechecking state here, because it might be shared between modules? (especially memoization!)... hol up, is there anything to even share?

    -- Step 1: Generate type substitution (typing context) based on the constraints.
    (tStmts, errs) <- generateSubstitution tcContext senv rStmts

    phase "State of unis"
    pc =<< InterModular.getTypeUni

    -- check if there are any free variables to ERROR ON.
    -- TODO: after i test it out, replace ftvs without any typeclasses with Units. Only error on tyvars with typeclasses.
    ftvs <- Set.map snd <$> findFTV tStmts
    let errs' = errs <> (AmbiguousType Def.TmpNoLocation <$> Set.toList ftvs)

    
    phase "Typechecking (AST)"
    pc tStmts

    pure (errs', tStmts)


---------------------------
--      INFERENCE        --
---------------------------

generateSubstitution :: Context -> TypecheckingState -> Module R -> InterModular (Module TC, [TypeError])
generateSubstitution env senv rModule = do
  (tvModule, _, errors) <- runRWST infer env senv

  pure (tvModule, errors)
  where
    infer = do
      pf "starting subst"
      -- Typecheck *all* functions, datatypes, etc. We want to typecheck a function even if it's not used (unlike Zig! (soig))
      _ <- inferDatatypes rModule.allDatatypes
      _ <- inferFunctions rModule.allFunctions
      tls <- inferTopLevel rModule.toplevel
      _ <- inferClasses rModule.allClasses
      _ <- inferInstances rModule.allInstances
      exs <- inferExports rModule.exports

      -- run it one last time for top level
      _ <- substAccessAndAssociations

      assocs <- RWS.gets associations
      pf "LAST ASSOCS: %" (pp $ fst <$> assocs) :: Infer ()
      reportAssociationErrors

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
    inferAnnStmt :: (PP a) => Base (AnnStmt R) (Infer a) -> Infer (Base (AnnStmt TC) a)
    inferAnnStmt (O (O (Def.Annotated anns (Def.Located location rStmt)))) = printUni (unPos location.startPos.sourceLine) anns $ do
        upStmt
        tstmt <- bitraverse inferExpr id rStmt

        -- Map expr -> type for unification
        let ttstmt = first (\expr@(Fix (N en _)) -> (expr, en.t)) tstmt
        stmt'''@(O (O (Def.Annotated _ (Def.Located _ _)))) <- O . O . Def.Annotated anns . Def.Located location <$> inferStmt location ttstmt
        pf "STMT: %" stmt'''
        pure stmt'''

    inferStmt :: Def.Location -> StmtF R (Expr TC, Type TC) a -> Infer (StmtF TC (Expr TC) a)
    inferStmt _ stmt = case stmt of

      Assignment v varLocation (rexpr@(Fix (N en _)), t) -> do
        vt <- var v
        (varLocation, vt) `uni` (Just en.loc, t)

        pure $ Assignment v varLocation rexpr


      Mutation v varLocation locality accesses (expr@(Fix (N ne _)), t) -> do
        vt <- var v

        case locality of
          Def.Local -> pure ()
          Def.FromEnvironment {} ->
            addEnv (T.DefinedVariable v) vt

        -- prepare accesses for typechecking.
        taccesses <- for accesses $ \case
              MutRef l -> (MutRef l,) <$> fresh
              MutField l mem -> (MutField l mem,) <$> fresh

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
        pure $ Mutation v varLocation locality taccesses expr


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
        ret <- inferExpr rret
        emret <- RWS.asks returnType

        eret <- maybe (findBuiltinType Prelude.tlReturnFind) pure emret  -- NOTE: When default return type is nothing, this means that we are  [TVar phaselparsing prelude. Return type from top level should be "Int" (or, in the future, U8).
        askUni ret `uni` (Nothing, eret)

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
        pure $ Fun fn

      Inst rinst -> do
        inst <- inferInstance rinst
        pure $ Inst inst

      Other () -> pure $ Other ()



inferExpr :: Expr R -> Infer (Expr TC)
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType :: Base (Expr R) (Infer (Expr TC)) -> Infer (Base (Expr TC) (Expr TC))
    inferExprType (N location e) = do
      upExpr
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
            substAccessAndAssociations

            pure exprBody

          -- be sure to copy the environment HERE!
          let
            T.EnvDef _ venv _ = fenv
            varsFromNestedFun = Set.fromList $ venv <&> \(v, _, t) -> (v, t)

          RWS.modify $ \s -> s { instantiations = varsFromNestedFun <> s.instantiations }

          union <- singleEnvUnion (T.UnionLam fenv [])
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
          (t, v') <- instantiateVariable location loc v

          case loc of
            Def.Local -> pure ()
            Def.FromEnvironment {} -> do
              addEnv v' t

          pure (Var v' loc, t)


        Con c emptyEnv -> do
          c' <- inferConstructor c

          (t, match, envts) <- instantiateConstructor emptyEnv c'
          pure (Con c' (emptyEnv, match, envts), t)

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
inferConstructor = \case
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
      envtvars <- traverse (mkType . TO . TVar) $ snd dd.ddOther
      pure $ TCon dd params ([], envtvars)  -- maybe should be undefined??
    TCon (R.ExternalDatatype dd) rparams () -> do
      params <- sequenceA rparams
      envtvars <- traverse (mkType . TO . TVar) $ snd dd.ddOther
      pure $ TCon dd params ([], envtvars)  -- maybe should be undefined??
    TO (R.TClass rcd) -> do
      cd <- inferClass rcd
      t <- fresh
      let constr = constrain (error "todo (should come from class type)")
      t `constr` (cd, mempty)  -- NOTE: we MUST ensure that this turns into a TVar. If not, it should be an error...? 
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
    envtvars <- traverse (mkType . TO . TVar) $ snd dd.ddOther
    Match newParams unions _ <- instantiateScheme' mempty $ fst dd.ddOther

    (Def.TmpNoLocation, newParams) `uniMany` (Nothing, params) -- just in case unify em

    mkType $ TCon dd params (unions, envtvars)

  TCon (R.ExternalDatatype dd) rparams () -> do
    params <- sequenceA rparams
    envtvars <- traverse (mkType . TO . TVar) $ snd dd.ddOther
    Match newParams unions _ <- instantiateScheme' mempty $ fst dd.ddOther

    (Def.TmpNoLocation, newParams) `uniMany` (Nothing, params) -- just in case unify em
    mkType $ TCon dd params (unions, envtvars)

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
      envtvars <- traverse (mkType . TO . TVar) $ snd dd.ddOther
      unions <- extractUnionsFromDataType dd  -- i think it's safe here to extractUnions, since it'll get instantiated anyway?
      pure $ TCon dd params' (unions, envtvars)

    TO tv -> pure $ TO tv
    TFun emptyFunUnion params ret -> liftA2 (TFun emptyFunUnion) (sequenceA params) ret


inferDatatype :: R.DataType -> Infer (DataDef TC)
inferDatatype = \case
  R.ExternalDatatype tdd -> pure tdd
  R.DefinedDatatype rdd -> inferDataDef rdd

inferDataDef :: DataDef R -> Infer (DataDef TC)
inferDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $
  \(DD ut (rtvars, renvtvars) erdcs anns) addMemo -> mdo
    pf "miau"
    tvars <- traverse inferTVar rtvars
    envtvars <- traverse inferTVar renvtvars
    pf "cock"
    let ~scheme = T.Scheme tvars unions []
    let ~dd = DD ut (scheme, envtvars) edcs anns  -- NOTE: TVar correctness (no duplication, etc.) should be checked in Resolver!
    pf "not miau"

    addMemo dd

    ~edcs <- case erdcs of
      Right rdcs -> fmap Right $ for rdcs $ \(DC _ uc rts dcAnn)-> do
        ts <- traverse inferType rts
        let dc = DC dd uc ts dcAnn
        pure dc

      Left rrecs -> fmap Left $ for rrecs $ \(Def.Annotated recAnn (memname, rt)) -> do
        t <- inferType rt
        pure $ Def.Annotated recAnn (memname, t)

    ~unions <- case edcs of
          Right dcs -> trafold extractUnionsFromConstructor dcs
          Left drs -> trafold (\(Def.Annotated _ (_, t)) -> extractUnion ut t) drs

    pure dd



inferFunction :: Function R -> Infer (Function TC)
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration
    let anns = rfundec.functionOther.foAnnotations

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
    -- let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
    let noGeneralizationScheme = Scheme mempty mempty mempty
    let fundec = FD env rfundec.functionId params ret $ T.FunOther noGeneralizationScheme rfundec.functionOther.foFunStack anns rfundec.functionOther.foLocation
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
      substAccessAndAssociations
      -- su <- RWS.gets typeSubstitution
      -- replacedStmts <- replaceClassFunsWithInstantiations su classInstantiationAssocs stmts

      pure stmts

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

--   As x at -> As <$> x <> pure at

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
        , classDeclarationLocation = Def.TmpNoLocation
        }
  funs <- for cd.classFunctions $ inferClassFunDec tcd . R.DefinedClassFunDec
  pure tcd

inferClassFunDec :: ClassDef TC -> XClassFunDec R -> Infer (ClassFunDec TC)
inferClassFunDec cd = \case
  (R.ExternalClassFunDec cfd) -> pure cfd
  (R.DefinedClassFunDec (CFD _ uv params ret ())) -> do
    params' <- for params $ \(decon, rt) -> do
      d <- inferDecon decon
      t <- inferClassType rt

      let dt = askUni d
      self <- fresh
      ct <- mkTypeFromClassType self t
      dt `uni` (Just (error "location for types (in function parameters!)"), ct)

      pure (d, t)

    ret' <- inferClassType ret
    pure $ CFD cd uv params' ret' undefined

inferClassDeclaration :: ClassFunDec R -> Infer (ClassFunDec TC)
inferClassDeclaration (CFD rcd uv _ _ ()) = do
  tcd <- inferClassDef rcd
  let mcfd = find (\(CFD _ cuv _ _ _) -> cuv == uv) tcd.classFunctions
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
    cfd@(CFD _ _ cparams cret _) <- inferClassFunDec klass rfn.instClassFunDec

    -- TODO: add check?
    fn <- generalize $ mdo
      pf "lam generalize"
      -- TODO NEW: same as in `inferType`
      Match tvs unions _ <- instantiateScheme' mempty $ fst it.ddOther
      self <- mkType $ TCon it tvs (unions, undefined)  -- TODO: when we stop ignoring tvars, properly instantiate them here.
      pf "miau"

      -- Infer function declaration.
      let rfundec = rfn.instFunDec
      let anns = rfundec.functionOther.foAnnotations

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
      (classFunType, _) <- instantiateClassFunction cfd undefined undefined

      union <- emptyUnion
      genFun <- mkType $ TFun union (snd <$> params) ret

      let instFunHeaderLocation = rfn.instFunDec.functionOther.foLocation
      (instFunHeaderLocation, genFun) `uni` (Nothing, classFunType)


      -- Set up temporary recursive env (if this function is recursive, this env will be used).
      let recenv = T.RecursiveEnv rfundec.functionEnv.envID (null $ R.fromEnv rfundec.functionEnv)
      let noGeneralizationScheme = Scheme mempty mempty
      let fundec = FD env rfundec.functionId params ret $ T.FunOther undefined rfundec.functionOther.foFunStack anns rfundec.functionOther.foLocation
      let fun = Function { functionDeclaration = fundec, functionBody = body }

      -- Infer body.
      (env, body) <- withEnv rfundec.functionEnv $ withReturn ret $ do
        stmts <- inferStmts rfn.instFunBody

        -- First, finalize substitution by taking care of member access.
        -- NOTE: We have to call it here, because some types in the declaration might be dependent on member types.
        --  At the end there will be one last member access.
        -- TODO: technically, we can do it all at the end. I should add it to state and replace them at the end (since they are all referred to by the unique instantiation id).
        substAccessAndAssociations
        -- replacedStmts <- replaceClassFunsWithInstantiations su classInstantiationAssocs stmts

        pure stmts

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



-- Generalizes the function inside.
generalize :: Infer (Function TC) -> Infer (Function TC)
generalize ifn = do
  fn <- ifn

  pf "Unsubstituted function:"
  pc fn

  -- csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  scheme <- constructSchemeForFunctionDeclaration fn.functionDeclaration

  pf "Scheme for %s: %s" (pp fn.functionDeclaration.functionId) (pp scheme) :: Infer ()
  -- pf "Assocs for %s: %s" (pp fn.functionDeclaration.functionId) (pp assocs) :: Infer ()


  let generalizedFnWithScheme = fn { functionDeclaration = fn.functionDeclaration { functionOther = T.FunOther
    { T.functionScheme = scheme
    , T.functionStack = fn.functionDeclaration.functionOther.functionStack
    , T.functionAnnotations = fn.functionDeclaration.functionOther.functionAnnotations
    , T.functionLocation = fn.functionDeclaration.functionOther.functionLocation
    } } }

  pf "Substituted function %:" fn.functionDeclaration.functionId
  pc generalizedFnWithScheme
  pc =<< lift InterModular.getTypeUni

  pure generalizedFnWithScheme


-- NEW: it should be called before every env creation.
substAccessAndAssociations :: Infer ()
substAccessAndAssociations = do
  phase "SUBST ACCESS"
  go where
    go = do
      didAccessProgressedSubstitutions <- substAccess
      didAssociationsProgressedSubstitutions <- substAssociations
      -- let didAssociationsProgressedSubstitutions = not $ null classInstantiationAssocs
      -- pf "CIA KEYS: %" $ classInstantiationAssocs
      -- pc classInstantiationAssocs

      -- There should be no more than one UCI for a type. These are already selected.
      if didAccessProgressedSubstitutions || didAssociationsProgressedSubstitutions
        then go
        else do
          phase "END SUBST ACCESS"
          pure ()


-- substitutes members n shiii (this is done in conjunction with associated types).
-- returns True if substitutions were done.
-- TODO: uggo function in general (including the `getExpectedType`)
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
-- TODO: uggo function 2
substAssociations :: Infer Bool
substAssociations = do
  assocs <- RWS.gets associations
  RWS.modify $ \s -> s { associations = mempty }

  substitutedAssociations <- fmap filterDesignatedForRemoval $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) (toLocation, to) (CFD cd uv _ _ _) classInstID envsToAddTo, insts) -> do
    unFrom <- getType from
    case unFrom of
        TCon dd _ _ -> case insts !? cd >>= (!? dd) of
          Just inst -> do
            -- select instance function to instantiate.
            let instFun = Def.mustOr (pf "[COMPILER ERROR]: Could not select function %s bruh," (pp uv)) $ find (\InstFun { instClassFunDec = CFD _ cuv _ _ _ } -> cuv == uv) inst.instFuns

            -- hope it's correct....
            -- let baseFunctionScopeSnapshot = Map.singleton instFun.instDef.instClass insts  -- FIX: bad interface. we make a singleton, because we know which class it is. also, instance might create constraints of some other class bruh. ill fix it soon.
            -- TODO: FromEnvironment locality only here, because it means we won't add anything extra to the instantiations.
            (instFunType, T.DefinedFunction fn _, theseInsts) <- instantiateFunction fromLocation insts $ Function instFun.instFunDec instFun.instFunBody

            pf "fun assoc uni %: %" fn.functionDeclaration.functionId <$> presentFunctionType fn =<< getTypeUni
            mto <- presentType to <$> getTypeUni
            ifnt <- presentType instFunType <$> getTypeUni
            pf "uni: % %" mto ifnt
            (toLocation, to) `uni` justType instFunType
            -- pf "ENV ASSOC: %" env
            addExtraToEnv envsToAddTo undefined

            -- su <- RWS.gets typeSubstitution

            pure (t, True)

          Nothing -> do
            pure (t, False)  -- error.

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        _ -> pure (t, False)

  dbgAssociations "after" substitutedAssociations
  RWS.modify $ \s -> s { associations = s.associations <> substitutedAssociations }
  pure $ not $ null substitutedAssociations


-- adds last fixups to the environment.
-- NEW: shouldn't it be the same as what's in instantiateVariable with function?
--    like, shouldn't it be recursive, adding instantiations from a function used in the instantiation??
-- 
-- class ToInt
-- 	to-int (n _) -> Int

-- env = 420
-- f ()
-- 	inst ToInt Bool
-- 		to-int (n Bool) -> Int
-- 			return env

-- 	print to-int(True)
-- 	return

-- f()
--     test result: NEGATIVE. Incorrect codegen. The implementation was INCORRECT. I have to change it.
--   So, I was right. It should be the same!
addExtraToEnv :: [Def.EnvID] -> T.EnvDef -> Infer ()
addExtraToEnv envIds (T.EnvDef _ vars instEnvStack) =
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
  in lift $ InterModular.addEnvAdditions undefined

--  2. report any errors or something.
-- TODO: all of these 3 functions are kinda hindi-style programming. FIX IT AFTER I UNDERSTAND WHAT IM DOING.
reportAssociationErrors :: Infer ()
reportAssociationErrors = do
  assocs <- RWS.gets associations
  -- su <- RWS.gets typeSubstitution

  -- first, report errors.
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) _ (CFD cd _ _ _ _) _ _, insts) -> do
    getType from >>= \case
        TCon dd _ _ -> case insts !? cd >>= (!? dd) of
          Just _ -> error "[COMPILER ERROR]: resolvable associated type found. should already be taken care of."

          Nothing -> do
            err $ DataDefDoesNotImplementClass (fromLocation) dd cd
            pure (t, True)

        -- I guess we don't signal errors yet! We'll do it on the next pass.
        TFun {} -> do
          from' <- presentType from <$> getTypeUni
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
  substitutedAssociations <- fmap filterDesignatedForRemoval $ for assocs $ \t@(T.TypeAssociation (fromLocation, from) _ (CFD cd _ _ _ _) _ _, insts) -> do
    getType from >>= \case
        TO (TVar tv) | tv.binding == BindByVar funUV -> do
          -- will be added later to the association list!
          pure (t, True)

        _ ->
          -- ignore!
          pure (t, False)

  RWS.modify $ \s -> s { associations = substitutedAssociations }  -- TODO: what? what am i doing

  -- second: extract associations for the function.
  functionAssociationsAndFutureTVars <- fmap catMaybes $ for assocs $ \(T.TypeAssociation (fromLocation, from) (toLocation, to) cfd _ _, _) -> do
    getType from >>= \case
        TO (TVar tv) | tv.binding == BindByVar funUV ->
          fmap Just $ (T.FunctionTypeAssociation tv to cfd undefined,) <$> lift (findFTV to)
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
constructSchemeForFunctionDeclaration :: FunDec TC -> Infer (Scheme TC)
constructSchemeForFunctionDeclaration dec = do
      -- IMPORTANT: We only extract types from non-instantiated! The instantiated type might/will contain types from our function and we don't want that. We only want to know which types are from outside.
      -- So, for a function, use its own type.
      -- For a variable, use the actual type as nothing is instantiated!
  -- NEW TODO: replace with extractUnion + ftv
  let digOutTyVarsAndUnionsFromEnv :: T.EnvDef -> Infer (Set (TypeID, T.TyVar), Set T.EnvUnion)
      digOutTyVarsAndUnionsFromEnv (T.EnvDef _ env _) = fmap fold $ traverse (\(v, _ ,t) -> digThroughVar t v) env
        where
          digThroughVar :: Type TC -> T.Variable -> Infer (Set (TypeID, T.TyVar), Set T.EnvUnion)
          digThroughVar t = \case
            T.DefinedVariable _ -> digOutTyVarsAndUnionsFromType t
            T.DefinedFunction f _ -> do
              params <- traverse (digOutTyVarsAndUnionsFromType . snd) f.functionDeclaration.functionParameters
              ret <- digOutTyVarsAndUnionsFromType f.functionDeclaration.functionReturnType  -- should we dig through external functions?
              pure $ fold params <> ret

            T.DefinedClassFunction (CFD cd _ _ _ _) _   -- TODO: I think we don't need to dig through instances?
              -> pure mempty

  (tyVarsOutside, unionsOutside) <- digOutTyVarsAndUnionsFromEnv dec.functionEnv
  (tyVarsDeclaration, unionsDeclaration) <- liftA2 (<>) (fmap fold $ traverse (digOutTyVarsAndUnionsFromType . snd) dec.functionParameters) (digOutTyVarsAndUnionsFromType dec.functionReturnType)

      -- TypesDefinedHere = FnType \\ Environment
  let tyVarsOutside' = Set.map snd tyVarsOutside
      tyVarsOnlyFromHere = Set.filter ((`Set.notMember` tyVarsOutside') . snd) tyVarsDeclaration
      unionsOnlyFromHere = unionsDeclaration \\ unionsOutside

      -- ALGO: ASSOCIATIONS

      -- function to find tvars defined for this function!
      definedTVars = findTVarsForID dec.functionId

  tvarsDefinedForThisFunction <- liftA2 (<>) (trafold (definedTVars . snd) dec.functionParameters) (definedTVars dec.functionReturnType)

  pf "FunDec for %: %" (pp dec.functionId) (pp dec)
  pf "UNIONS for %: % = % \\\\ %" (pp dec.functionId) (pp unionsOnlyFromHere) (pp unionsDeclaration) (pp unionsOutside)
  pf "ASSOCS when %:" (pp dec.functionId)
  associations <- RWS.gets associations
  pf "Associations (???): %" (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation (fromLocation, from) to cfd _ _, _) -> pf "(%) %: %" (pp cfd.classFunID) (pp from) (pp to) :: String)

  -- add associations.
  -- NEW: here TyVars -> TVars. this is bad, because it's illogical. I should change it. But it should work.
  (assocs, tvmap) <- rummageThroughAssociations dec.functionId tyVarsOnlyFromHere -- remember to use the new Subst, which generalizes the associations.
  pf "after rummaging: %" assocs
  reportAssociationErrors

  -- BIG THING HERE!!!!
  -- do the substitution like THIS.
  pf "after binding"

  -- TODO NEW: here I will exclude unions in type associations in the future from Scheme for caching instantiations (and mostly for functions to not repeat)
  let
      tvars = Set.toList $ Set.fromList (Map.elems tvmap) <> tvarsDefinedForThisFunction

  (_, assocUnions) <- trafold (\(T.FunctionTypeAssociation _ t _ _) -> digOutTyVarsAndUnionsFromType t) assocs
  let assocScheme = Scheme tvars (Set.toList $ unionsOnlyFromHere <> assocUnions) assocs

  pure assocScheme

-- TODO NEW: TypingContext should be moved outside to increase laziness.
digOutTyVarsAndUnionsFromType :: Type TC -> Infer (Set (TypeID, T.TyVar), Set T.EnvUnion)
digOutTyVarsAndUnionsFromType = getType' >=> traverse2 (\t -> (t,) <$> digOutTyVarsAndUnionsFromType t) >=> \(tid, t) -> case t of
    TO (TyVar tyv) -> pure $ (Set.singleton (tid, tyv), mempty)
    TFun union ts t -> pure $ (mempty, Set.singleton union) <> foldMap snd ts <> snd t
    TCon _ ts (unis, envtvars) -> do
      ets <- traverse digOutTyVarsAndUnionsFromType envtvars
      pure $ foldMap snd ts <> foldMap ((mempty,) . Set.singleton) unis <> fold ets
    t -> pure $ foldMap snd t


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

-- TODO NEW: Bad name and weird implementation.
-- This function is for getting the type of a record accessor.
getExpectedType :: Def.Location -> Type TC -> Def.MemName -> Infer (Maybe (Type TC), Bool)  -- (maybe type, should remove from list?)
getExpectedType location t memname = getType t >>= \case
  TCon dd@(DD _ (Scheme ogTVs ogUnions ~[], ogEnvTVs) (Left recs) _) tvs (unions, envtvars) ->
    case find (\(Def.Annotated _ (name, _)) -> name == memname) recs of
      Just (Def.Annotated _ (_, recType)) -> do
        ogUnions' <- for ogUnions getUnion
        recType' <- ump (Map.fromList (zip ogTVs tvs) <> Map.fromList (zip ogEnvTVs envtvars)) (Map.fromList $ zip (T.unionID <$> ogUnions') unions) mempty Nothing $ mapTVs recType
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
    t' <- presentType t <$> getTypeUni
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
      con@(DC dd@(DD _ (scheme@(Scheme ogTVs ogUnions _), envtvars) _ _) _ usts _) <- inferConstructor rcon

      -- Deconstruct decons.
      decons <- sequenceA idecons
      envTVs <- traverse (mkType . TO . TVar) envtvars

      -- Custom instantiation for a deconstruction.
      -- Create a parameter list to this constructor
      --  NOTE: scheme is a scheme from a datatype, so no insts to worry about
      ogUnions' <- for ogUnions getUnion
      (Match tvs unions _, ts) <- instantiateScheme mempty Nothing scheme $ \mapTVs -> do
        traverse mapTVs usts


      let args = askType <$> decons
      (location, args) `uniMany` (Just (error "todo: add location information to datatype declaration"), ts)

      t <- mkType $ TCon dd tvs (unions, envTVs)
      pure $ N (T.ExprNode { T.t = t, T.loc = location }) $ CaseConstructor con decons


------
-- Instantiation
------

-- TODO: merge it with 'inferVariable'.
instantiateVariable :: Def.Location -> Def.Locality -> R.Variable -> Infer (Type TC, T.Variable)
instantiateVariable location loc = \case
  R.DefinedVariable v -> var v <&> (,T.DefinedVariable v)
  R.ExternalVariable uv t -> pure (t, T.DefinedVariable uv)

  R.DefinedFunction rfn rsnapshot -> do
    fn <- inferFunction rfn
    snapshot <- inferSnapshot rsnapshot
    (t, v, theseInsts) <- instantiateFunction location snapshot fn
    RWS.modify $ \s -> s { instantiations = Set.insert (v, t) $ theseInsts <> s.instantiations }
    pure (t, v)

  R.ExternalFunction fn rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    (t, v, theseInsts) <- instantiateFunction location snapshot fn -- notice that we use the UFI from here (inferVariable just creates a temp error type to not use it)

    -- pf "Associations (instantiation): %" (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation (fromLocation, from) to _ _ _, _) -> pf "(%) %: %" (pp (uci, ufi)) (pp from) (pp to) :: String)

    -- NEW: Temporarily commented out. This will be the base for 
    -- add instantiations!
    --  only when it's a local function should you add stuff from its environment to instantiations.
    -- let gatherInstsFromEnvironment :: T.Env -> Infer (Set (T.Variable, Type TC))
    --     gatherInstsFromEnvironment = \case
    --         T.RecursiveEnv _ _ -> pure mempty
    --         T.Env _ -> flip trafold vars $ \case
    --           (envVar@(T.DefinedFunction fn _), Def.Local, t) -> do
    --             -- NOTE: we need mapped envs, so we have to dig through the type. but, are we too permissive? should we only choose this current env? or all of them? how do we distinguish the "current" one?
    --             let currentEnvID = T.envID fn.functionDeclaration.functionEnv
    --             (baset, envs) <- getType' t >>= \(baset, tt) -> case tt of
    --               TFun union _ _ -> (baset,) <$> (getUnion union <&> \u -> map (\(_, _, _, env) -> env) $ filter (\(_, ufi', _, env) -> ufi' == ufi) u.union)
    --               _ -> error "impossible, it's a function type."
    --             Set.insert (envVar, baset) <$> (trafold gatherInstsFromEnvironment envs)
    --           (envVar, _, t) -> pure $ Set.singleton (envVar, t)

    -- theseInsts <- if loc == Def.Local
    --   -- only when it's a function in the same level as this, add its environment to the enclosing function's environment
    --   -- TODO are we checking, that the types do not repeat? (different type IDs...)
    --   then gatherInstsFromEnvironment env
    --   else pure mempty

    RWS.modify $ \s -> s { instantiations = Set.insert (v, t) $ theseInsts <> s.instantiations }

    pure (t, v)


  -- Should we generate ClassInstIDs here, or in Resolver????
  -- nahhhhh, that's arbitrary as hell.
  R.DefinedClassFunction rcfd rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    cfd@(CFD cd _ _ _ _) <- inferClassDeclaration rcfd

    instantiateClassFunction cfd snapshot location

  R.ExternalClassFunction cfd@(CFD cd _ _ _ _) rsnapshot -> do
    snapshot <- inferSnapshot rsnapshot
    let insts = Def.defaultEmpty cd snapshot

    -- addClassFunctionUse fnUnion cfd self insts
    -- pf "INSTANTIATING CLASS FUN %(%). INSTS: %" (pp funid) (pp uci) $ fmap (fmap (\(DD { ddName }) -> ddName) . Set.toList . Map.keysSet) $ Map.elems insts :: Infer ()

    (fnType, v) <- instantiateClassFunction cfd snapshot location
    pure (fnType, v)



instantiateClassFunction :: ClassFunDec TC -> T.ScopeSnapshot TC -> Def.Location -> Infer (Type TC, T.Variable)
instantiateClassFunction cfd@(CFD cd funid params ret scheme@(Scheme schemeTVars schemeUnions _)) snapshot location = do
    -- NEW: same part from inferVariable:
    self <- fresh
    let possibleInstancesHere = Def.defaultEmpty cd snapshot
    let constr = constrain location
    self `constr` (cd, possibleInstancesHere)

    cid <- newClassInstID


    -- TODO: a lot of it is duplicated from DefinedFunction. sussy
    -- TODO TODO: NOT SURE IF IT'S ALL NECESSARY!!!!!!!!!!!!!!!!!!!!!!!!
    -- SHOULD EXPLAIN EACH LINE BECAUSE SOMETHING FEELS OFF
    -- let allTypes = ret : map snd params
    -- let thisFunctionsTVars = foldMap (findTVarsForIDInClassType funid) allTypes

    -- dig out unions from class type (instantiate class type)
    -- all these unions should come from datatypes. so...
    -- let extractUnions :: ClassType TC -> Infer (Set (T.EnvUnion))
    --     extractUnions = cata $ \case
    --       NormalType (TCon dd params _) -> do
    --         ddUnions <- Set.fromList <$> extractUnionsFromDataType dd
    --         paramUnions <- seqfold params
    --         pure $ ddUnions <> paramUnions
    --       ct -> seqfold ct

    -- thisFunctionsUnions <- trafold extractUnions allTypes

    -- let schemeTVars = Set.toList thisFunctionsTVars
    -- let schemeUnions = Set.toList thisFunctionsUnions
    -- let scheme = Scheme schemeTVars schemeUnions mempty

    -- TODO NEW: I think this part code appears somewhere else also. Type mapping should be better.
    (_, (iparams, iret)) <- instantiateScheme mempty Nothing scheme $ \mapTVs' -> do
      let mapTVs = mapTVs' <=< lift . mkTypeFromClassType self
      ts <- traverse (mapTVs . snd) params
      r <- mapTVs ret
      pure (ts, r)

    fnUnion <- emptyUnion
    fnType <- mkType $ TFun fnUnion iparams iret

    -- NEW: part from instantiateVariable:
    associateType (location, self) (location, fnType) cfd cid snapshot

    pure (fnType, T.DefinedClassFunction cfd cid)


-- Return: new type, variable and variables to add to enclosing envs!
instantiateFunction :: Def.Location -> T.ScopeSnapshot TC -> Function TC -> Infer (Type TC, T.Variable, Set (T.Variable, Type TC))
instantiateFunction assocLocation snapshot fn = do
    let fundec = fn.functionDeclaration
    let (Scheme schemeTVars schemeUnions _) = fundec.functionOther.functionScheme

    definesBeforeInst <- lift InterModular.numTypesAndUnionsDefined

    pf "Before schemin: %" fundec.functionId
    pf "Before schemin: %" =<< presentFunctionType fn <$> getTypeUni
    (match@(Match tvs unions _), (funparams, funret, envInsts)) <- instantiateScheme snapshot (Just fn) fundec.functionOther.functionScheme $ \mapTVs -> do
      params <- traverse (mapTVs . snd) fundec.functionParameters
      ret <- mapTVs fundec.functionReturnType

      envInsts <- instantiationsRelativeToFunction mapTVs fundec.functionEnv
      pure (params, ret, envInsts)


    pf "after assocs: %" =<< presentFunctionType fn <$> getTypeUni

    fnUnion <- singleEnvUnion $ T.UnionFun fn [] match
    pf "cock 2"
    fnType <- mkType $ TFun fnUnion funparams funret
    let v = T.DefinedFunction fn match

    pf "cock 3"
    punions <- traverse getUnion unions
    pf "TypeUni for % after scheme instantiation: %" fundec.functionId =<< lift InterModular.getTypeUni
    pf "GOT SCHEME: % %" tvs punions

    pf "Instantiation of %" (pp fundec.functionId) :: Infer ()
    pf "TVars: %" (pp schemeTVars)  :: Infer ()
    pf "Unions: %" =<< traverse getUnion schemeUnions
    pf "Scope Snapshot:\n%" (T.dbgSnapshot snapshot) :: Infer ()
    pf "after schemin: %" =<< presentFunctionType fn <$> getTypeUni

    -- pc $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) tvmap
    -- pc $ (Def.ppMap . fmap (bimap Def.ppUnionID pp) . Map.toList) unionmap

    pc =<< lift InterModular.getTypeUni
    gfn <- presentFunctionType fn <$> getTypeUni
    pf "For function %:\n\tScheme unions: % -> %\n\tType %.\n\tAfter instantiation: %"
      (pp fundec.functionId)
      schemeUnions
      punions
      gfn
      =<< presentType fnType <$> getTypeUni

    lift $ InterModular.trackInstantiation definesBeforeInst fn
    pure (fnType, v, envInsts)


-- gather instantiations for stuff this function used
--   wait, how does the OG handle retrieving stuff from functions, which are local, but were called inside other function???
--   wait, were they also filtered by Resolver's renvQuery?
--   TODO: check that. write the similar implementation first, then check.
--   TODO: maybe optimize, so I don't acess reader state all the time?
--         will this have any penalty with effects??
instantiationsRelativeToFunction :: (Type TC -> UltraMap (Type TC)) -> T.EnvDef -> UltraMap (Set (T.Variable, Type TC))
instantiationsRelativeToFunction mapTVs (T.EnvDef _ baseVars _) = do
  -- flip trafold vars $ \case
  --   (envVar@(T.DefinedFunction fn match), Def.Local, t) -> do
  --     (baset, tt) <- getType' t

  --     -- instnatiate match and do other stuff
  --     -- TODO: I should consider the design of typemap for this, since we will be adding more and more mappings to this.
  --     undefined
  --   (envVar, _, t) -> pure $ Set.singleton (envVar, t)
  
  -- only when it's a local function should you add stuff from its environment to instantiations.
  let gatherInstsFromEnvironment :: [(T.Variable, Def.Locality, Type TC)] -> UltraMap (Set (T.Variable, Type TC))
      gatherInstsFromEnvironment vars = flip trafold vars $ \case
            (envVar@(T.DefinedFunction fn match), Def.Local, t) -> do
              -- NOTE: we need mapped envs, so we have to dig through the type. but, are we too permissive? should we only choose this current env? or all of them? how do we distinguish the "current" one?
              -- NEW ALGO: future typeclass thing?
              mappedT <- mapTVs t
              let scheme = fn.functionDeclaration.functionOther.functionScheme
              env <- withMatch scheme match fn.functionDeclaration.functionEnv

              Set.insert (envVar, mappedT) <$> (gatherInstsFromEnvironment env)
            (envVar, _, t) -> do
              mappedT <- mapTVs t
              pure $ Set.singleton (envVar, mappedT)
  gatherInstsFromEnvironment baseVars

withMatch :: T.Scheme TC -> Match -> T.EnvDef -> UltraMap [(T.Variable, Def.Locality, Type TC)]
withMatch (Scheme sTVs suUnions suAssocs) match env = do
  sUnions <- lift $ traverse (fmap T.unionID . getUnion) suUnions
  let sAssocs = suAssocs <&> \(T.FunctionTypeAssociation _ _ _ cid) -> cid

  Match mTVs mUnions mAssocs <- mapMatch match
  (T.EnvDef _ vars _) <- RST.local
    ( \um ->
      let appendMap ks vs = Map.union $ Map.fromList $ zip ks vs
      in UMS
      { ultraTypeMap  = appendMap sTVs mTVs um.ultraTypeMap
      , ultraUnionMap = appendMap sUnions mUnions um.ultraUnionMap
      , ultraAssocMap = appendMap sAssocs mAssocs um.ultraAssocMap
      , ultraMatchThing = Nothing  -- NOTE: i don't think we need it anymore.
      }
    )
    $ mapEnv env
  pure vars



-- check which types should NOT be instantiated (for cuckedUnions)
--  should we go that deep?
--   NOTE NEW: it should go only as deep as the ftv function.
-- definedVarTypes :: T.EnvDef -> Infer (Set (Type TC))
-- definedVarTypes = doEnv where
--   doEnv = \case
--     T.EnvDef _ vars _ -> do
--       let (dvars, others) = partition (\(v, _, _) -> case v of { T.DefinedVariable {} -> True; _ -> False }) vars
--       dvarBaseTypes <- trafold (\(_, _, t) -> Set.singleton . fst <$> getType' t) dvars
--       -- otherTypes <- fmap fold $ traverse doType $ map (\(_, _, t) -> t) others
--       pure $ dvarBaseTypes  -- maybe i shouldn't go deeper?

--   doType :: Type TC -> Infer (Set (Type TC))
--   doType = getType >=> traverse doType >=> \case
--     TFun union ts t -> doUnion union <&> (<> fold ts <> t)
--     TCon _ ts unions -> (fold ts <>) <$> trafold doUnion unions
--     _ -> pure mempty

--   doUnion :: T.EnvUnion -> Infer (Set (Type TC))
--   doUnion = getUnion >=> \u -> flip trafold u.union $ \case
--     -- T.UnionFun fn _ -> doEnv $ fn.functionEnv
--     -- T.UnionLam env -> doEnv env

-- NOTE NEW: we need the whole scope snapshot, because we will be instantiating the whole function, which might require other classes. Is it correct? Or am I overshitting myself?
associateType :: (Def.Location, Type TC) -> (Def.Location, Type TC) -> ClassFunDec TC -> Def.ClassInstID -> T.ScopeSnapshot TC -> Infer ()
associateType (fromLocation, based) (toLocation, result) cfd classInstID insts = do
    -- pf "ASSOC: %s %s" (pp uci) (pp ufi)
    estack <- RWS.gets envStack
    let ta = T.TypeAssociation (fromLocation, based) (toLocation, result) cfd classInstID estack

    RWS.modify $ \s -> s { associations = (ta, insts) : s.associations }


-- addClassFunctionUse :: T.EnvUnion -> T.ClassFunDec -> T.Type -> T.PossibleInstances -> Infer ()
-- addClassFunctionUse eu cfd self insts = RWS.modify $ \s -> s { classFunctionUnions = (eu, cfd, self, insts) : s.classFunctionUnions }

instantiateConstructor :: Def.EnvID -> DataCon TC -> Infer (Type TC, Match, [Type TC])
instantiateConstructor envID = \case
  DC dd@(DD _ (scheme, envtvars) _ _) _ [] _ -> do
    match@(Match tvs unions []) <- instantiateScheme' mempty scheme
    envTVs <- traverse (mkType . TO . TVar) envtvars
    t <- mkType $ TCon dd tvs (unions, envTVs)
    pure (t, match, envTVs)

  (DC dd@(DD _ (scheme, envtvars) _ _) _ usts@(_:_) _) -> do
    (match@(Match tvs unions _), ts) <- instantiateScheme mempty Nothing scheme $ \mapTVs -> do
      traverse mapTVs usts
    envTVs <- traverse (mkType . TO . TVar) envtvars
    ret <- mkType $ TCon dd tvs (unions, envTVs)

    -- don't forget the empty env!
    union <- singleEnvUnion $ T.UnionConEnv envID
    t <- mkType $ TFun union ts ret
    pure (t, match, envTVs)

instantiateRecord :: DataDef TC -> Infer (Type TC)
instantiateRecord dd@(DD _ (scheme, envtvars) (Left _) _) = do
  Match tvs unions _ <- instantiateScheme' mempty scheme
  envTVs <- traverse (mkType . TO . TVar) envtvars
  mkType $ TCon dd tvs (unions, envTVs)

instantiateRecord (DD ut scheme (Right _) _) = error $ pf "Attempted to instantiate ADT (%s) as a Record!" (pp ut)


instantiateScheme' :: T.ScopeSnapshot TC -> Scheme TC -> Infer Match
instantiateScheme' snapshot scheme = fst <$> instantiateScheme snapshot Nothing scheme (const $ pure ())

instantiateScheme :: T.ScopeSnapshot TC -> Maybe (Function TC) -> Scheme TC -> ((Type TC -> UltraMap (Type TC)) -> UltraMap a) -> Infer (Match, a)
instantiateScheme snapshot mfn scheme@(Scheme schemeTVars schemeUnions schemeAssocs) stuffToMap = mdo
  -- Prepare a mapping for the scheme!
  tyvs <- traverse (const fresh) schemeTVars  -- scheme
  let tvmap = Map.fromList $ zip schemeTVars tyvs

  -- ALGO NEW: we must also map the Match types in the instantiated union!!
  newUnionUIDs <- traverse (const (lift InterModular.nextUnionUniID)) schemeUnions
  schemeUnionIDs <- traverse (fmap (T.unionID . snd) . getUnion') schemeUnions 
  let unionMap = Map.fromList $ zip schemeUnionIDs newUnionUIDs

  -- do the whole mapping in context

  -- unions with new ID, but `Match` is not yet mapped
  schemeUnionsMatchNotMapped <- for schemeUnions $ \uuid -> do
    u <- getUnion uuid
    uid <- newUnionID
    pure $ u { T.unionID = uid }

  let ogAssocIDs = schemeAssocs <&> \(T.FunctionTypeAssociation _ _ _ classInstID) -> classInstID
  newAssocIDs <- for ogAssocIDs reinstantiateClassInstID
  let assocMap = Map.fromList $ zip ogAssocIDs newAssocIDs

  (match, x) <- ump tvmap unionMap assocMap ((,match) <$> mfn) $ do
    -- The problem is that unions can contain other unions which are exposed. So, we have to map 'em.
    -- 
    -- 1. map `Match` types of scheme unions
    unions <- for schemeUnionsMatchNotMapped $ \u -> do
      mapUnion' u

    -- 2. add actual union implementation for this.
    lift $ for_ (zip newUnionUIDs unions) $
      uncurry addUnionWithExistingID

    -- 3. associations
    assocs <- for (zip newAssocIDs schemeAssocs) $ \(newInstID, T.FunctionTypeAssociation tv to cfd@(CFD cd _ _ _ _) _) -> do
      from <- mapTVs =<< lift (mkType $ TO $ TVar tv)
      mto <- mapTVs to
      lift $ do
        pf "FROM: %" from
        pf "TO: %" =<< presentType mto <$> getTypeUni

        -- ALGO: reinstantiate the class ID. This will make it separate from the OG ID in case it'll get generalized again, but also we can compare it to the original Scheme to know which old ID it belongs to.
        associateType (Def.TmpNoLocation, from) (Def.TmpNoLocation, mto) cfd newInstID snapshot
        pure newInstID

    -- 3.5 ENV MATCH SHIT
    let numatch = Match tyvs newUnionUIDs assocs

    -- 4. cuck stuff at the end (used as pejorative for the caller of this function, not related to `cuckedUnions`)
    nux <- stuffToMap mapTVs

    pure (numatch, nux)

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
      let instmap = fromMaybe mempty $ snapshot !? klass
      let constr = constrain (error "todo")
      t `constr` (klass, instmap)

  pure (match, x)  -- (tyvs, unions)


-- very bad... memo for mapping types.
type UltraMap a = RST UltraMaps (Map (Type TC) (Type TC), Map T.EnvUnion T.EnvUnion) Infer a
ultraMapThing :: Map (TVar TC) (Type TC) -> Map Def.UnionID (T.EnvUnion) -> Map ClassInstID ClassInstID -> Maybe (Function TC, T.Match) -> UltraMap a -> Infer a
ultraMapThing typemap unionmap assocmap mmatch umx = fst <$> RST.runRST umx (UMS { ultraTypeMap = typemap, ultraUnionMap = unionmap, ultraAssocMap = assocmap, ultraMatchThing = mmatch }) mempty
data UltraMaps = UMS
  { ultraTypeMap :: Map (TVar TC) (Type TC)
  , ultraUnionMap :: Map Def.UnionID (T.EnvUnion)
  , ultraAssocMap :: Map ClassInstID ClassInstID
  , ultraMatchThing :: Maybe (Function TC, Match)
  }

ump = ultraMapThing


-- so this thing is only used when instantiating stuff.
mapTVs :: Type TC -> UltraMap (Type TC)
mapTVs tid = do
  pf "mapTVs"
  tryMemoType tid $ \baseTid ttt -> upMapSthTVs >> traverse mapTVs ttt >>= \case
    TO (TVar tv) -> error "bruh"  -- lift $ getType $ fromMaybe baseTid (tvmap !? tv)
    TFun union ts tret -> do
      pf "mapTVs: TFun"
      union' <- mapUnion union
      pure $ TFun union' ts tret
    TCon dd ts (unions, envtvs) -> do
      pf "mapTVs: TCon"
      unions' <- for unions $ \union -> do
        mapUnion union
      envTVs <- traverse mapTVs envtvs
      pure $ TCon dd ts (unions', envTVs)
    TO tt -> do
      pf "mapTVs: TO"
      pure $ TO tt

tryMemoType :: Type TC -> (Type TC -> TypeF TC TypeID -> UltraMap (TypeF TC TypeID)) -> UltraMap (Type TC)
tryMemoType tid fux = lift (getType' tid) >>= \(baseTid, t) -> do
    RST.gets fst >>= \tvs -> case tvs !? baseTid of
      Just newU -> pure newU
      Nothing -> do
            t' <- case t of
              TO (TVar tv) -> do
                tvmap <- RST.asks ultraTypeMap
                pure $ fromMaybe baseTid (tvmap !? tv)  -- HACK! to not duplicate changed tvars accidentally
              _ -> do
                evaldType <- fux baseTid t
                if t == evaldType
                  then pure tid
                  else do
                        newT <- lift $ mkType evaldType
                        pure newT

            RST.modify $ first $ Map.insert baseTid t'
            pure t'

mapUnion :: T.EnvUnion -> UltraMap T.EnvUnion
mapUnion = tryMemoUnion $ \_ u -> mapUnion' u

mapUnion' :: T.EnvUnionF T.EnvUnion (Type TC) -> UltraMap (T.EnvUnionF T.EnvUnion (Type TC))
mapUnion' u = do
    upMapSthTVs
    pf "union"
    newUnion <- for u.union $ \case
      T.UnionFun fn outermatch match -> do
        mumt <- RST.asks ultraMatchThing
        let msm = case mumt of
              Nothing -> id
              Just m@(tfn, _) ->
                let es = fn.functionDeclaration.functionEnv.envStack
                in if tfn.functionDeclaration.functionEnv.envDefID `elem` es
                  then (m:)
                  else id

        RST.local (\um -> um { ultraMatchThing = Nothing })
          $ T.UnionFun fn
          <$> msm
              <$> traverse2 mapMatch outermatch
          <*> mapMatch match
      T.UnionLam env outer -> do
        mumt <- RST.asks ultraMatchThing
        let msm = case mumt of
              Nothing -> id
              Just m@(tfn, _) ->
                let es = env.envStack
                in if tfn.functionDeclaration.functionEnv.envDefID `elem` es
                  then (m:)
                  else id

        T.UnionLam env <$> (msm <$> traverse2 mapMatch outer)

      T.UnionConEnv envID -> pure $ T.UnionConEnv envID
          -- ts' <- traverse mapTVs ts
          -- env' <- mapEnv premade exclude tvmap unionmap env
          -- pure (muci, ufi, ts', env')
    pure $ u { T.union = newUnion }

tryMemoUnion :: (T.EnvUnion -> T.EnvUnionF T.EnvUnion TypeID -> UltraMap (T.EnvUnionF T.EnvUnion TypeID)) -> T.EnvUnion -> UltraMap T.EnvUnion
tryMemoUnion fux uid = do
  pf "tryMemoUnion: %" uid
  (baseUid, u) <- lift $ getUnion' uid
  pf "tryMemoUnion 1.5"
  RST.gets snd >>= \us -> do
    pf "FUCK UAOJDOJSAOD"
    pf "exists? %" $ isJust $ us !? baseUid
    case us !? baseUid of
        Just newU -> do
          pf "tryMemoUnion 1.75"
          pure newU
        Nothing -> do
          pf "tryMemoUnion 2"
          unionmap <- RST.asks ultraUnionMap
          case unionmap !? u.unionID of
            Just mu -> pure mu
            Nothing -> mdo
              pf "tryMemoUnion 3"
              RST.modify $ fmap $ Map.insert baseUid newU
              evaldUnion <- fux baseUid u
              newU <- if u == evaldUnion
                then pure uid
                else do
                  lift $ mkUnion evaldUnion
              pure newU


-- NEW NOTE: kinda bad, because we're redoing the mistakes I did. I wonder if there is a better way? I guess I didn't want to map unions (I wanted to leave em alone)
mapEnv :: T.EnvDef -> UltraMap T.EnvDef
mapEnv (T.EnvDef eid vars stack) = do
  vars' <- for vars $ \(v, l, t) -> do
    v' <- case v of
      T.DefinedVariable uv ->
        pure $ T.DefinedVariable uv
      T.DefinedFunction fn match -> do
        match' <- mapMatch match
        pure $ T.DefinedFunction fn match'
      T.DefinedClassFunction cfd classInstID ->
        pure $ T.DefinedClassFunction cfd classInstID

    t' <- mapTVs t
    pure (v', l, t')

  pure $ T.EnvDef eid vars' stack

-- TODO NEW: bruh, the "assocs" part is weird. should I map inside it or leave it alone? probably leave it alone, as it means, that it's not tied to our function, so it should not be mapped.
--   or maybe not. imagine an inner instance, which has tvars in its environment, but depends on some top level var for its type.
-- so... maybe. NOTE: right now I'm leaving it be, but I should keep it in mind.
mapMatch :: T.Match -> UltraMap T.Match
mapMatch (Match ts us as) = do
  pf "fuck"
  assocmap <- RST.asks ultraAssocMap
  Match
    <$> traverse mapTVs ts
    <*> traverse mapUnion us
    <*> pure (as <&> \classInstID -> fromMaybe classInstID (assocmap !? classInstID))


-- Constructs an environment from all the instantiations.
--  We need the instantiations, because not all instantiations of a function can come up in the environment.
--  But, when there is a TVar in the type, it means all instantiated types of TVars must be there.
withEnv :: R.Env -> Infer a -> Infer (T.EnvDef, a)
withEnv renv x = do
  let eid = renv.envID
  pf "BEGIN ENV: %" (pp renv)

  -- 1. clear environment - we only collect things from this scope.
  outOfEnvInstantiations <- RWS.gets instantiations

  -- 2. execute in scope.
  RWS.modify $ \s -> s { instantiations = Set.empty, envStack = eid : s.envStack }
  x' <- x
  modifiedInstantiations <- RWS.gets instantiations


  -- 3. then filter the stuff that actually is from the environment
  --  TODO: This realistically encounters two cases:
  --    1. remove self insert
  --    2. don't remove self insert
  --   in instantiateVariable, we always add the function itself to the `instantiations` (environment), but if it's local, we don't need to do that. Here it would be removed. BUT. Imagine... maybe we just would not add the instantiation if the function is not local??? imagine that.
  -- TODO: also, this kind of thing "degrades" the meaning of Resolver even more, as we can just as well define the environment during typechecking. Should we even keep resolver??
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
  RWS.modify $ \s -> s { instantiations = outOfEnvInstantiations, envStack = tail s.envStack }  -- NOTE: `tail` instead of `drop`, because if an empty list is here must be a bug in the code.

  let newEnv = T.EnvDef eid newEnvVars renv.envStackLevel
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
        Just dd@(DD _ (scheme, ~[]) _ _) -> do  -- note, that a builtin type should not have 'em.
          Match tvs unions _ <- instantiateScheme' mempty scheme
          mkType $ TCon dd tvs (unions, [])
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."

mkPtr :: Type TC -> Infer (Type TC)
mkPtr insidePtr = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> mkType $ p.mkPtr insidePtr
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap Prelude.ptrTypeName (\(DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(DD _ (scheme, ~[]) _ _) -> do
          Match tvs@[innerTyVar] unions _ <- instantiateScheme' mempty scheme
          (error "should it even fail?", innerTyVar) `uni` (Nothing, insidePtr)
          mkType $ TCon dd tvs (unions, [])

        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show Prelude.ptrTypeName <> "'."


mkType :: TypeF TC TypeID -> Infer TypeID
mkType t = lift $ do
  tid <- InterModular.nextTypeID
  InterModular.modifyTypeUni $ IntMap.insert tid.fromTypeID $ Right t
  pure tid

mkUnion :: T.EnvUnionF T.EnvUnion TypeID -> Infer T.EnvUnion
mkUnion u = lift $ do
  uid <- InterModular.nextUnionUniID
  InterModular.modifyUniUni $ IntMap.insert uid.fromUnionUniID $ Right u
  pure uid

mkUnion' :: T.EnvUnionF T.EnvUnion TypeID -> Infer T.EnvUnion
mkUnion' u = lift $ do
  newUid <- newUnionID
  uid <- InterModular.nextUnionUniID
  InterModular.modifyUniUni $ IntMap.insert uid.fromUnionUniID $ Right $ u { T.unionID = newUid }
  pure uid

-- adds more stuff to the union and adds a reference for the old one to the union.
nextUnion :: T.EnvUnion -> T.EnvUnionF T.EnvUnion TypeID -> Infer T.EnvUnion
nextUnion oldUnionID union = lift $ do
  nextUnionID <- InterModular.nextUnionUniID
  InterModular.modifyUniUni
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
  upf "uni many!"
  unifyMany ts1 ts2

-- maybe later get the location from the type?
constrain :: Def.Location -> Type TC -> (ClassDef TC, T.PossibleInstances TC) -> Infer ()
constrain location t cdi = 
    addConstraint location t cdi


------

unify :: (Def.Location, Type TC) -> (Maybe Def.Location, Type TC) -> Infer ()
unify (locl, tttl) (locr, tttr) = do
  (ttl, tl) <- getType' tttl
  (ttr, tr) <- getType' tttr
  upUni
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

    (TCon t ta (unions, envtvars), TCon t' ta' (unions', envtvars')) | t == t' -> do
      unifyMany (locl, ta) (locr, ta')
      zipWithM_ unifyFunEnv unions unions'  -- i don't think we need to unify the types associated with EnvUnion, right???
      unifyMany (locl, envtvars) (locr, envtvars')

    (_, _) -> do
      ttl' <- presentType ttl <$> getTypeUni
      ttr' <- presentType ttr <$> getTypeUni
      err $ TypeMismatch (locl, ttl') (locr, ttr')

unifyMany :: (Def.Location, [Type TC]) -> (Maybe Def.Location, [Type TC]) -> Infer ()
unifyMany (_, []) (_, []) = nun
unifyMany (ll, tl:ls) (lr, tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
  unify (ll, tl) (lr, tr)
  unifyMany (ll, ls) (lr, rs)

unifyMany tl tr = do
  tl' <- traverse (\t -> presentType t <$> getTypeUni) $ snd tl
  tr' <- traverse (\t -> presentType t <$> getTypeUni) $ snd tr
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
        newtyvid <- lift InterModular.nextTypeID
        lift $ InterModular.modifyTypeUni $
            IntMap.insert newtyvid.fromTypeID $ Right $ TO $ TyVar newtyv
        upf "TVAR MAKER: New tyvar %. In %." newtyv tyv
        let bind' = bind (Left (location, Nothing))
        (tid, tyv) `bind'` newtyvid

      TFun {} -> do
        t <- presentType tid <$> getTypeUni
        err $ FunctionTypeConstrainedByClass location t klass

bind :: Either (Def.Location, Maybe Def.Location) (Maybe Def.Location, Def.Location) -> (TypeID, T.TyVar) -> Type TC -> Infer ()
bind loc (tyvid, tyv) tid = do
  t <- getType tid
  case t of
    TO (TyVar tyv') | tyv == tyv' -> nun  -- TODO: this is just in case, because same fresh variables should have the same TypeIDs.
    _ -> do
      tyVarOccursInRightType <- occursCheck tyv tid
      if tyVarOccursInRightType
        then do
          tid' <- presentType tid <$> getTypeUni
          err $ InfiniteType loc tyv tid'
        else do
          pf "bind: % -> %" tyvid tid
          lift $ InterModular.modifyTypeUni $ IntMap.insert tyvid.fromTypeID (Left tid.fromTypeID)

unifyFunEnv :: T.EnvUnion -> T.EnvUnion -> Infer ()
unifyFunEnv lenv renv = do
  unionID <- newUnionID
  unionUniID <- lift InterModular.nextUnionUniID


  (baseLEnv, lenv'@T.EnvUnion { T.unionID = _ }) <- getUnion' lenv
  (baseREnv, renv'@T.EnvUnion { T.unionID = _ }) <- getUnion' renv
  let union2envset = Set.fromList . (\(T.EnvUnion { T.union = union }) -> union)
      envset2union = Set.toList
      funEnv = envset2union $ union2envset lenv' <> union2envset renv'

  let env = T.EnvUnion { T.unionID = unionID, T.union = funEnv }
  lift $ InterModular.modifyUniUni
    $ IntMap.insert unionUniID.fromUnionUniID (Right env)       -- insert union itself
    . IntMap.insert baseLEnv.fromUnionUniID (Left unionUniID.fromUnionUniID)   -- insert ref
    . IntMap.insert baseREnv.fromUnionUniID (Left unionUniID.fromUnionUniID)   -- insert ref


getUnion :: T.EnvUnion -> Infer (T.EnvUnionF T.EnvUnion TypeID)
getUnion = fmap snd . getUnion'

getUnion' :: T.EnvUnion -> Infer (T.EnvUnion, T.EnvUnionF T.EnvUnion TypeID)
getUnion' uid = do
  tu <- lift InterModular.getTypeUni
  pure $ TC.getUnionFromUni tu uid

getUnion'' :: TC.TypeUni -> T.EnvUnion -> T.EnvUnionF T.EnvUnion TypeID
getUnion'' tu = snd . TC.getUnionFromUni tu

getType :: Type TC -> Infer (TypeF TC TypeID)
getType = fmap snd . getType'

getType' :: Type TC -> Infer (Type TC, TypeF TC TypeID)
getType' tid = do
  tu <- lift InterModular.getTypeUni
  pure $ TC.getTypeFromUni tu tid

getType'' :: TC.TypeUni -> Type TC -> TypeF TC TypeID
getType'' tu = snd . TC.getTypeFromUni tu

getTypeUni :: Infer TC.TypeUni
getTypeUni = lift InterModular.getTypeUni

presentType :: Type TC -> TC.TypeUni -> Def.Context
presentType t tu = go t where
  go t =  case fmap go (getType'' tu t) of
    TCon tc ts (unions, env) ->
      let us = fmap (presentUnion tu) unions
      in pf "(% % % %)" (ppDef tc) ts env us
    TFun union ts t ->
      let u = presentUnion tu union
      in pf "(%% -> %)" u ts t
    TO (TVar tv) -> pp tv
    TO (TyVar tyv) -> pp tyv

presentUnion :: TC.TypeUni -> T.EnvUnion -> Def.Context
presentUnion tu u = go u where
  go u =
    let u' = fmap (flip presentType tu) (getUnion'' tu u)
    in pf "%%" u'.unionID (Def.encloseSepBy "{" "}" ", " $ u'.union <&> \unionMember -> pf "%" unionMember :: Def.Context)

presentFunctionType :: Function TC -> TC.TypeUni -> Def.Context
presentFunctionType fn tu =
  let env = (flip presentType tu) <$> fn.functionDeclaration.functionEnv
      params = (flip presentType tu) <$> (snd <$> fn.functionDeclaration.functionParameters)
      ret = presentType fn.functionDeclaration.functionReturnType tu
  in pf "%% -> %" env params ret

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

newtype FTV a = FTV { fromFTV :: Reader TC.TypeUni a } deriving (Functor, Applicative, Monad)

instance Semigroup a => Semigroup (FTV a) where
  fl <> fr = liftA2 (<>) fl fr
    
instance Monoid a => Monoid (FTV a) where
  mempty = pure mempty


findFTV :: Substitutable a => a -> InterModular (Set (Type TC, T.TyVar))
findFTV x = do
  typeUni <- InterModular.getTypeUni
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

instance Substitutable (T.ExprNode) where
  ftv en = ftv en.t

instance Substitutable TypeID where
  ftv tid = FTV Reader.ask >>= \tuni ->
    let ftvType ttid =
          let (baseid, tt) = fmap2 ftvType $ TC.getTypeFromUni tuni ttid
          in case tt of
              TO (TyVar tyv) -> pure $ Set.singleton (baseid, tyv)
              t -> seqfold t
    in ftvType tid


instance Substitutable (T.LamDec TC) where
  ftv (T.LamDec _ env) = ftv env

instance Substitutable t => Substitutable (T.VariableF u t) where
  ftv _ = mempty


instance Substitutable Def.UniqueVar where
  ftv _ = mempty

instance Substitutable Def.MemName where
  ftv _ = mempty

instance Substitutable Def.Location where
  ftv = const mempty


instance Substitutable (Function TC) where
  ftv fn = liftA2 (\\) (ftv fn.functionBody) (ftv fn.functionDeclaration)

instance Substitutable (FunDec TC) where
  ftv (FD _ _ params ret other) =
    ftv params <> ftv ret <> ftv other -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 

instance Substitutable (T.FunOther TC) where
  ftv other =
    let Scheme _ _ assocs = other.functionScheme
    in ftv assocs

instance Substitutable T.TypeAssociation where
  ftv (T.TypeAssociation from to _ _ _) = ftv from <> ftv to

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


instance Substitutable t => Substitutable (T.EnvUnionF u t) where
  ftv (T.EnvUnion _ envs) = ftv envs

instance Substitutable t => Substitutable (T.UnionMemberF u t) where
  ftv = foldMap ftv


instance Substitutable t => Substitutable (T.EnvF u t) where
  ftv (T.Env env) = ftv env
  ftv (T.RecursiveEnv _ _) = mempty

instance Substitutable ty => Substitutable (T.EnvDefF u ty) where
  ftv = foldMap ftv

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


-- Returns a fresh new tyvare
fresh :: Infer (Type TC)
fresh = do
  tid <- lift InterModular.nextTypeID
  tyv <- freshTyVar
  pf "fresh: % %" (ppDef tid) tyv
  lift $ InterModular.modifyTypeUni $
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


singleEnvUnion :: T.UnionMember -> Infer T.EnvUnion
singleEnvUnion um = do
  uid <- newUnionID
  mkUnion $ T.EnvUnion { T.unionID = uid, T.union = [um] }

addUnionWithExistingID :: T.EnvUnion -> T.EnvUnionF T.EnvUnion (Type TC) -> Infer ()
addUnionWithExistingID uuid union = do
  lift $ InterModular.modifyUniUni $ IntMap.insert uuid.fromUnionUniID $ Right $ union

-- Creates an empty union.
emptyUnion :: Infer T.EnvUnion
emptyUnion = do
  uid <- newUnionID
  mkUnion $ T.EnvUnion uid []


findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList

classFunDecToClassType :: ClassFunDec R -> ClassType R
classFunDecToClassType (CFD _ _ params ret _) =
  Fix $ NormalType $ TFun undefined undefined undefined


newClassInstID :: Infer ClassInstID
newClassInstID = ClassInstID <$> liftIO newUnique

-- NOTE: we don't actually need the old class ID, but it makes it obvious we are reinstantiating it. we might also add info as to the previous ID.
reinstantiateClassInstID :: ClassInstID -> Infer ClassInstID
reinstantiateClassInstID = const $ newClassInstID


------------------------------------------
--          DATATYPES n shiiii
------------------------------------------

-- TODO: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer = RWST Context [TypeError] TypecheckingState InterModular  -- normal inference

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe (Type TC)
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

upc :: (PP a, Log p, p ~ x unit, unit ~ ()) => a -> p
upc = Def.pc T_Uni

upf :: PrintfType r => String -> r
upf = Def.printf T_Uni


uphase :: (Log pctx, x () ~ pctx) => String -> pctx
uphase = Def.phase T_Uni


printUni :: Int -> [Def.Ann] -> Infer a -> Infer a
printUni line anns ix = if Def.ADebugUnification `elem` anns
  then do
    oldAssocLength <- RWS.gets $ length . associations
    x <- ix
    -- also other shit
    assocs <- RWS.gets associations
    let newAssocs = take (length assocs - oldAssocLength) assocs
    upf "Assocs generated right now: %" $ fst <$> newAssocs
    pure x
  else ix


dbgAssociations :: String -> [(T.TypeAssociation, T.ScopeSnapshot TC)] -> Infer ()
dbgAssociations title associations = pf "Associations (%): %" title (Def.encloseSepBy "[" "]" ", " $ associations <&> \(T.TypeAssociation from to _ classInstID _, _) -> pf "(%) %: %" classInstID from to :: String)




-- This is currently how we extract unions from types.
-- This needs to be done, because custom types need to track which unions were used.
-- TODO: this should probably be made better. Maybe store those unions in DataDef?
extractUnionsFromDataType :: DataDef TC -> Infer [T.EnvUnion]
extractUnionsFromDataType (DD _ _ (Right dcs) _) =
  trafold extractUnionsFromConstructor dcs

extractUnionsFromDataType dd@(DD ut _ (Left drs) _) =
  flip trafold drs $ \(Def.Annotated _ (_, t)) -> extractUnion ut t

extractUnionsFromConstructor :: DataCon TC -> Infer [T.EnvUnion]
extractUnionsFromConstructor (DC (DD ut _ _ _) _ ts _) = trafold (extractUnion ut) ts

-- TODO: clean up all the mapUnion shit. think about proper structure.
-- NEW: what even is it doing????
-- it's getting unions out. note, that there are "live", instantiated unions. it's kinda funny, because we have to traverse dis shit.
extractUnion :: Def.UniqueType -> Type TC -> Infer [T.EnvUnion]
extractUnion ut = getType >=> \case
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  TCon (DD tut _ _ _) paramts (conUnions, envtypes)
    -- breaks cycle with self referential datatypes.
    | tut == ut -> trafold (extractUnion ut) paramts
    | otherwise
      -> liftA2 (<>) (trafold (extractUnion ut) envtypes)
      $  liftA2 (<>) (concat <$> traverse ueu conUnions) (trafold (extractUnion ut) paramts)

  TFun u args ret -> liftA3 (\ue l r -> ue <> l <> r) (ueu u) (trafold (extractUnion ut) args) (extractUnion ut ret)
  TO _ -> pure []

-- NEW: unfortunately, we have to look inside the union with the current typing scheme.
--      not really needed in datatype, but when I use it for generalizing, I should look inside
addUnionAndExtractFromUnion, ueu :: T.EnvUnion -> Infer [T.EnvUnion]
ueu = addUnionAndExtractFromUnion  -- shorthand
addUnionAndExtractFromUnion u = pure [u]


trafold :: (Monoid b, Traversable t, Applicative f) => (a -> f b) -> t a -> f b
trafold f = fmap fold . traverse f

seqfold :: (Monoid b, Traversable t, Applicative f) => t (f b) -> f b
seqfold  = fmap fold . sequenceA


upExpr :: Infer ()
upExpr = lift $! imLift $! countUp tExprNum  -- lift $ InterModular $ RWS.modify $ \cc -> cc { stats = cc.stats { CompilerContext.tcExpr = cc.stats.tcExpr + 1} }

upStmt :: Infer ()
upStmt = lift $! imLift $! countUp tStmtNum  -- lift $! CompilerContext $! RWS.modify $! \cc -> cc { stats = cc.stats { CompilerContext.tcStmt = cc.stats.tcStmt + 1} }

upUni :: Infer ()
upUni = lift $! imLift $! countUp numSeparateUnifications

upMapSthTVs :: UltraMap ()
upMapSthTVs = lift $! lift $! imLift $! countUp numTVMaps

upMapCS :: Infer ()
upMapCS = lift $! imLift $! countUp numCSMaps

-- the COCK operator
infixr 1 &=>
(&=>) :: Functor m => (a -> m b) -> (b -> c) -> a -> m c
(&=>) f g = fmap g . f

instance Foldable ((,,,) a b c) where
  foldMap f (_, _, _, x) = f x

instance Traversable ((,,,) a b c) where
  traverse f (a, b, c, x) = (a, b, c,) <$> f x
