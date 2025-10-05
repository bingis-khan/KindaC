{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- we implement basic instances (Foldable, Travesable) for Tuple.

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}  -- for HLINT kekek
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant pure" #-}  -- this is retarded. it sometimes increases readability with that extra pure.
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStrict #-}
module Mono (mono) where

import qualified AST.Typed as T
import qualified AST.Mono as M
import qualified AST.Mono as IM
import qualified AST.Common as Common
import Data.Fix (Fix(..))
import Data.Functor.Foldable (embed, cata, para, project)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first, bimap)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.Map (Map, (!?), (!))
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State (runStateT, withStateT)
import qualified Control.Monad.State.Class as State
import qualified Control.Monad.Reader.Class as Reader
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Foldable (fold, for_)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe, fromJust, maybeToList, fromMaybe, isJust, listToMaybe)
import Data.Set (Set)
import Misc.Memo (Memo (..), emptyMemo, memo, memo', isMemoed, Memoizable)
import qualified Misc.Memo as Memo
import Data.Monoid (Any (Any, getAny))
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Bifoldable (bifold)
import Control.Monad (void, (<=<))
import Data.String (fromString)
import Data.List (find, partition, tails, unsnoc)
import AST.Common (AnnStmt, Module, StmtF (..), Expr, ExprNode (..), ExprF (..), Function (..), TypeF (..), ClassFunDec (..), Type, CaseF (..), Case, Decon, DeconF (..), FunDec (..), TVar (..), DataDef (..), DataCon (..), ClassDef, InstDef, IfStmt (..), instFunDec, InstFun, MutAccess (..), askNode, XEnv)
import AST.Mono (M)
import AST.Def ((:.) (..), Annotated (..), Locality (..), PP (..), fmap2, PPDef (..), traverse2, sequenceA2, (<+>), Located (..), Log (..), PrintfType, PrintContext (..))
import qualified AST.Def as Def
import Data.List (nubBy)
import Data.List (nub)
import Stats (Counter, mStmtNum, mExprNum, mTypeNum, mUnionNum, mfStmtNum, mfExprNum, mfTypeNum, mfUnionNum, Stats)
import BaseCtx (BaseCtx, countUp')
import AST.Typed (TC, MatchF)
import qualified TypingContext as TC
import TypingContext (globalTypeUni)
import Lens.Micro ((^.), Lens')
import Lens.Micro.Mtl (use)
import Control.Monad.State (MonadState, lift)
import Control.Monad.Fix (MonadFix)
import Data.List (inits)
import Data.Semigroup (sconcat)

type T = TC
type IM = M


pf :: PrintfType r => String -> r
pf = Def.printf Def.M

pc :: (PP a, Log p, p ~ x unit, unit ~ ()) => a -> p
pc = Def.pc Def.M

phase :: (Log pctx, x () ~ pctx) => String -> pctx
phase = Def.phase Def.M



-- 26.09.25: NOTE: all this dumb shit with using T.EnvDefF don't work - we're ignoring unions!!! so, this must be changed.


------ Monomorphization consists of two steps:
--  Step 1: Perform normal monomorphization (however, you won't be able to compile escaped TVars).
--  Step 2: Replace escaped TVars with each instantiation of them. (maybe it can be eliminated like doing env defs by first collecting the variables)

mono :: TC.TypingContext -> [AnnStmt TC] -> BaseCtx (Module M)
mono tc tmod = {-# SCC mono #-} do
  -- Step 1: Just do monomorphization with a few quirks*.
  (mistmts, monoCtx) <- flip State.runStateT (startingContext tc) $ fromContext $ do
    mBody "[top level]" tmod

  let imEnvs = memoToMap monoCtx.memoEnv

  phase "Monomorphisation (just envs)"
  pc $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) imEnvs

  phase "Monomorphisation"
  pc $ Def.ppLines mistmts

  pure $ M.Mod mistmts



mAnnStmt :: AnnStmt T -> Context (AnnStmt IM)
mAnnStmt = cata (fmap embed . thisAnd (countUp mStmtNum) .  f) where
  f :: (:.) ((:.) Annotated Located) (StmtF T (Expr T)) (Context (AnnStmt IM)) -> Context ((:.) ((:.) Annotated Located) ((StmtF IM (Expr IM))) (AnnStmt IM))
  f (O (O (Annotated ann (Located location stmt)))) = do
    stmt' <- bitraverse mExpr id stmt
    let
      mann, noann :: b a -> Context ((:.) ((:.) Annotated Located) b a)
      mann = pure . O . O . Annotated ann . Located location
      noann = pure . O . O . Annotated [] . Located location

    -- NOTE: this is just remapping.......
    case stmt' of
      Pass -> mann Pass
      ExprStmt expr -> mann $ ExprStmt expr
      Assignment vid location expr -> mann $ Assignment vid location expr
      Print expr -> mann $ Print expr
      Mutation vid location l accesses expr -> do
        maccesses <- mMutAccesses accesses
        mann $ Mutation vid location l maccesses expr  -- NOTE: we don't need to adjust locality, because we may only assign to variables but only class functions might have their locality changed.
      If (IfStmt cond iftrue elseIfs else') -> mann $ If $ IfStmt cond iftrue elseIfs else'
      Switch switch cases -> do
        mcases <- traverse mCase cases
        mann $ Switch switch mcases
      Return ete -> do
        mete <- mExpr ete
        mann $ Return mete
      While cond bod -> do
        mann $ While cond bod

      Fun fn -> do
        -- let env = fn.functionDeclaration.functionEnv
        let envID = fn.functionDeclaration.functionEnv
        envInsts <- State.gets envInstantiations

        let currentEnvUses = fromMaybe mempty $ envInsts !? envID
        let envUses = foldMap Set.toList $ fromEnvUses currentEnvUses -- <&> \(IM.EnvUse (Just fn) env) -> (fn, env)

        pf "[stmt fun] ENCOUNTERED FUN %" (pp fn.functionDeclaration.functionId)
        pf "[stmt fun] current env uses %" currentEnvUses
        pf "[stmt fun] envUses %" (ppDef envUses)
        envDefs <- orderEnvironments envUses
        pf "[stmt fun] envdefs (%) %" (length envDefs) (fmap2 (ppDef . M.envDef) envDefs)
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ M.EnvInsts $ x :| xs

      Inst inst -> do
        envInsts <- State.gets envInstantiations

        let envUses = flip concatMap inst.instFuns $ \fn ->
              let envID = fn.instFunDec.functionEnv
                  currentEnvUses = fromMaybe mempty $ envInsts !? envID
                  defs = foldMap Set.toList $ fromEnvUses currentEnvUses
              in  defs

        pf "[stmt inst] ENV INSTS: %" (pp envInsts)
        pf "[stmt inst] ENCOUNTERED INST: %" (pp $ instFunDec <$> inst.instFuns)
        pf "[stmt inst] INST TURNED TO: %" (pp $ functionDeclaration <$> envUses)
        envDefs <- orderEnvironments envUses
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ M.EnvInsts $ x :| xs

      Other () -> error "OTHER OTHER OTHER SHOULD NOT BE CREATED EVER"


mMutAccesses :: [(MutAccess T, Type T)] -> Context [(MutAccess IM, Type IM)]
mMutAccesses accs = for accs $ \(acc, t) -> case acc of
  MutRef location -> do
    mt <- mType t
    pure (MutRef location, mt)
  MutField location mem -> do
    mt <- mType t
    let dd = expectIDataDef mt
    um <- member (dd, mem)
    pure (MutField location um, mt)

-- TODO: replace with actual types.
-- LEFT: ENV ASSIGNMENT
-- RIGHT: ENV DEFINITION.
orderEnvironments :: [Function IM] -> Context [Either M.EnvMod M.EnvInst]
orderEnvironments fns = do
  currentLevel <- State.gets $ length . currentEnvStack
  pf "CURRENT LEVEL: %" $ pp currentLevel

  let
    isFromCurrentEnv env = IM.envDefLevel env == currentLevel
    isFromOuterEnv env = IM.envDefLevel env < currentLevel

    filterOtherEnvs :: [Function IM] -> [Function IM]
    filterOtherEnvs = filter (isFromCurrentEnv . functionEnv . functionDeclaration)

    filterOuterEnvs :: [Function IM] -> [Function IM]
    filterOuterEnvs = filter (not . isFromOuterEnv . functionEnv . functionDeclaration)


    -- TODO: later, should create some custom datatypes (Env, [Function IM])
    loop :: [(Function IM, [Function IM])] -> Context [Either IM.EnvMod M.EnvInst]
    loop currentEnvs = do
        pf "ORDER ENVS: %" (pp $ bimap (functionId . functionDeclaration) (fmap (functionId . functionDeclaration)) <$> currentEnvs)
        completedEnvs <- State.gets completedEnvs

        let currentEnvsWithIncompleteEnvs = Def.fmap2 (filter ((\e -> e `Set.notMember` completedEnvs && not (isFromOuterEnv e)) . functionEnv . functionDeclaration)) currentEnvs
        -- pf "CANDIDATES: %" $ pp $ currentEnvsWithIncompleteEnvs <&> \(fn, deps) -> pp fn.functionDeclaration.functionId <+> pp (IM.envLevel fn.functionDeclaration.functionEnv) <+> (pp $ IM.envLevel . functionEnv . functionDeclaration <$> deps)
        -- pf "CANDIDATES (filtered outer): %" $ pp $ currentEnvsWithIncompleteEnvs <&> \(fn, deps) -> pp fn.functionDeclaration.functionId <+> pp (IM.envLevel fn.functionDeclaration.functionEnv) <+> (pp $ IM.envLevel . functionEnv . functionDeclaration <$> filterOuterEnvs deps)
        let areAllDependentEnvsDefinedInThisScope = null . snd . fmap filterOtherEnvs
        let (complete, incomplete) = partition areAllDependentEnvsDefinedInThisScope currentEnvsWithIncompleteEnvs
        -- pf "COMPLETE: %" (pp $ functionId . functionDeclaration . fst <$> complete)
        -- pf "INCOMPLETE: %" (pp $ bimap (functionId . functionDeclaration) (fmap $ functionId . functionDeclaration) <$> incomplete)
        if null complete
          then do
            setIncomplete $ first (functionEnv . functionDeclaration) <$> incomplete  -- there could be some incomplete envs, so we must add them here.
            pure $ fmap Right $ incomplete <&> \(e, ds) -> M.EnvInst { envDef = e, notYetInstantiated = ds }
          else do
            setComplete $ functionEnv . functionDeclaration . fst <$> complete
            let completedStmts = complete <&> \(e, deps) -> Right $ M.EnvInst { envDef = e, notYetInstantiated = deps }  -- NOTE: maybe we should filter out ONLY outer envs.
            envAdds <- Def.fmap2 Left completeEnvironments
            ((completedStmts <> envAdds) <>) <$> loop incomplete

    completeEnvironments :: Context [IM.EnvMod]
    completeEnvironments = do
        envsAndDependencies <- Map.toList <$> State.gets environmentsLeft
        pf "ENVS AND DEPS: %" (pp $ fmap (bimap pp (fmap (\fn -> fromString $ Def.pf "% %(%)" (pp fn.functionDeclaration.functionId) (pp $ IM.envDefID fn.functionDeclaration.functionEnv) (pp $ IM.envDefLevel fn.functionDeclaration.functionEnv) :: Def.Context))) envsAndDependencies)
        completedEnvs <- State.gets completedEnvs
        lastEnvVars <- State.gets lastEnvironment
        let
          -- this is a roundabout way, because it should already be done in dependencies.
          gatherAccesses :: IM.EnvDef -> (IM.Variable, Type IM) -> [IM.EnvAccess]
          gatherAccesses e = \case
            (IM.DefinedVariable _, _) -> []
            (IM.DefinedFunction fn, t) ->
              let currentEnv = fn.functionDeclaration.functionEnv
              in if currentEnv == e
                then [IM.EnvAccess { access = NonEmpty.singleton (fn, t), accessedEnv = e }]
                else case currentEnv of
                  IM.EnvDef _ vars _ -> 
                    concatMap (gatherAccesses e . (\(v, _, t) -> (v, t))) vars <&> \ea -> ea { IM.access = (fn, t) <| ea.access }

          -- TODO: this will be modified, as access will be represented differently.
          isFromEnv :: IM.EnvDef -> IM.EnvAssign
          isFromEnv e =
            case concatMap (gatherAccesses e) lastEnvVars of
              [] -> IM.LocalEnv e
              (acc:accs) -> IM.EnvFromEnv (acc :| accs)

        -- i do not understand this.
        -- oh, because environmentsLeft (incomplete) should have their dependencies updated. so these completed envs are NEW completed envs which need to be added. ahmygahd this is so bad.
        let dependencies
              = concatMap (\(e, ds) -> (e,) <$> ds)
              $ Def.fmap2 (filterOtherEnvs . filter ((`Set.member` completedEnvs) . functionEnv . functionDeclaration)) envsAndDependencies
        if null dependencies
          then pure []
          else do
            let incompleteEnvsAndDeps = Def.fmap2 (filter ((`Set.notMember` completedEnvs) . functionEnv . functionDeclaration) . filterOuterEnvs . filterOtherEnvs) envsAndDependencies
            let newCompletedEnvs = fst <$> filter (null . snd) incompleteEnvsAndDeps
            pf "COMPLETE ENVS: %\nCOMPLETE INCOMPLETE ENVS: %" (pp newCompletedEnvs) (pp $ Def.fmap3 (functionId . functionDeclaration) incompleteEnvsAndDeps)
            setComplete newCompletedEnvs
            setIncomplete incompleteEnvsAndDeps

            let dependencies' = dependencies <&> \(e, fn) -> IM.EnvMod (isFromEnv e) fn
            (dependencies' <>) <$> completeEnvironments

  loop $ fmap (\e -> (e, getEnvDependencies e.functionDeclaration.functionEnv)) $ nubBy (\f f' -> f.functionDeclaration.functionEnv == f'.functionDeclaration.functionEnv) fns  -- NOTE: nubBy added after we changed the representation of EnvUses to include all generated functions. It turns out, we actually want unique environments only here.


-- TODO: replace type (env assignment)
setIncomplete :: [(IM.EnvDef, [Function IM])] -> Context ()
setIncomplete envsAndDependencies = do
  -- add the incomplete environments to `environmentsLeft`
  let newEnvsLeft = Map.fromList envsAndDependencies
  State.modify' $ \c -> c { environmentsLeft = newEnvsLeft <> c.environmentsLeft }


setComplete :: [IM.EnvDef] -> Context ()
setComplete fns = State.modify' $ \c -> c { completedEnvs = c.completedEnvs <> Set.fromList fns }

getEnvDependencies :: IM.EnvDef -> [Function IM]
getEnvDependencies (IM.EnvDef _ vars _) = mapMaybe (\(v, _, _) -> case v of { IM.DefinedFunction fn -> Just fn; _ -> Nothing }) vars
-- getEnvDependencies _ = error "RECURSIVE ENV WHAT."


mExpr :: Expr T -> Context (Expr IM)
mExpr = cata $ thisAnd (countUp mExprNum) . fmap embed . \(N en expr) -> do
  mt <- mType en.t
  mexpr <- case expr of
    Lam (T.LamDec _ env) args ret -> do
      margs <- Def.traverse2 mType args
      (mret, menv) <- withEnv Nothing env ret

      pure $ Lam menv margs mret

    otherExpr -> do
      motherExpr <- sequenceA otherExpr
      case motherExpr of
        Lam {} -> error "Should be handled earlier."

        Var v locality -> do
          mv <- variable =<< bitraverse mUnion mType v

          envStack <- State.gets currentEnvStack
          newLocality <- reLocality envStack locality v

          pure $ Var mv newLocality

        Con c (eid, match, envtvs) -> do
          menvtvs <- traverse mType envtvs
          mc <- constructor c menvtvs =<< bitraverse mUnion mType match

          -- don't forget to register usage. (for codegen)
          void $ withEnv Nothing eid $ pure ()

          pure $ Con mc ()

        RecCon _ inst -> do
          let dd = expectIDataDef mt
          inst' <- for inst $ \(mem, memt) -> do
            ut <- member (dd, mem)
            pure (ut, memt)

          pure $ RecCon dd inst'

        RecUpdate me upd -> do
          -- TODO: Before i had a reference to the data def, but i may add it later. Maybe I should add the info while I'm checking types?
          let dd = expectIDataDef (askNode me)
          upd' <- for upd $ \(mem, meme) -> do
            ut <- member (dd, mem)
            pure (ut, meme)

          pure $ RecUpdate me upd'

        MemAccess me memname -> do
          let dd = expectIDataDef (askNode me)
          um <- member (dd, memname)
          pure $ MemAccess me um

        Lit lit -> pure $ Lit $ Common.relit id lit
        BinOp l op r -> pure $ BinOp l op r
        UnOp op x -> pure $ UnOp op x
        Call e args -> pure $ Call e args
        As (Fix (N _ e)) _ -> do
          -- Ignore 'as' by unpacking the variable and passing in the previous expression.
          pure e

  pure $ N mt mexpr

withEnv :: Maybe (Function IM) -> XEnv T -> Context a -> Context (a, IM.EnvDef)
withEnv mfn eid cx = do
  funStack <- State.gets functionStack
  menv@(IM.EnvDef _ envContent _) <- memo' memoEnv (\m c -> c { memoEnv = m }) (eid, funStack) $ \(eid', _) _ -> do
      newEID <- newEnvID
      (T.EnvDef _ envContent envStack) <- bitraverse mUnion mType =<< getEnv eid'
      let envLevel = Def.envStackToLevel envStack
      menvContent <- for envContent $ \(v, l, mt) -> do
        let vv = v
        mv <- variable vv

        newLocality <- reLocality envStack l vv

        pure (mv, newLocality, mt)

      pure $ IM.EnvDef newEID menvContent envLevel  -- env IDs changed, so kind of hard to track env stack. that's why only level. might not even need this.

  pf "[env] % % => %" eid (ppDef <$> mfn) (M.envDefID menv)
  
  -- SAVE PREVIOUS STATE
  prevlev <- State.gets currentEnvStack
  prevCompleteEnvs <- State.gets completedEnvs
  prevEnvsLeft <- State.gets environmentsLeft
  lastEnv <- State.gets lastEnvironment
  usedEnvs <- State.gets envInstantiations
  cusKeys <- Map.keysSet . Memo.memoToMap <$> State.gets cuckedUnions

  -- SET NEW LOCAL STATE
  T.EnvDef _ _ lev <- getEnv eid
  let curlev = eid : lev

  State.modify' $ \c -> c
    { currentEnvStack = curlev
    , completedEnvs = mempty
    , environmentsLeft = mempty
    , lastEnvironment = envContent <&> \(v, _, t) -> (v, t)
    , envInstantiations = mempty
    }

  -- NOTE: recursively add environments all environments. (is not yet ready for recursiveness)
  let doEnvIncompletes (IM.EnvDef _ envContent _) = concatMap ((\case { IM.DefinedFunction fn -> fn.functionDeclaration.functionEnv : doEnvIncompletes fn.functionDeclaration.functionEnv; _ -> [] }) . (\(v, _, _) -> v)) envContent
  pf "WITH ENV INCOMPLETE: %" $ pp $ doEnvIncompletes menv <&> \e -> (e, functionId . functionDeclaration <$> getEnvDependencies e)

  setIncomplete $ (\e -> (e, filter ((== length curlev) . IM.envDefLevel . functionEnv . functionDeclaration) $ getEnvDependencies e)) <$> doEnvIncompletes menv
  x <- cx


  -- RETRIEVE PREVIOUS STATE
  State.modify' $ \c -> c
    { currentEnvStack = prevlev
    , completedEnvs = prevCompleteEnvs
    , environmentsLeft = prevEnvsLeft
    , lastEnvironment = lastEnv
    , envInstantiations = Map.unionWith (<>) usedEnvs c.envInstantiations  -- only allow non-local instantiations through. (otherwise we get extra environment declarations)
    , cuckedUnions = Memo $ Map.restrictKeys (Memo.memoToMap c.cuckedUnions) cusKeys -- cucked unions should be local per function
    }


  pf "%M: % =WITH ENV%=> %" (ppDef eid) eid (case mfn of { Nothing -> "" :: Def.Context; Just fn -> fromString $ Def.pf " (%)" $ pp fn.functionDeclaration.functionId }) (pp menv)

  pure (x, menv)


-- TODO NEW: REEVALUATE THIS FUNCTION BRUH. IF WE START UPDATING THE ENV IN PLACE, IT SHOULD BE GOOD.
-- Evaluate the locality of a class function after we have access to the instance.
reLocality :: Def.EnvStack -> Def.Locality -> T.VariableF u a -> Context Def.Locality
reLocality envStack ogLocality = \case
  -- NOTE: I COMMENTED IT OUT FOR NOW WHILE I'M BEGINNING THE TYPECLASS IMPLEMENTATION.
  -- v@(T.DefinedClassFunction _ classInstID) -> do
  --   (_, es) <- selectInstance' classInstID

  --   let vfn = Common.instanceToFunction ivfn
  --   let (T.EnvDef _ _ instEnvStack) = vfn.functionDeclaration.functionEnv
  --   let newLoc = if envStack == instEnvStack then Local else FromEnvironment (Def.envStackToLevel instEnvStack)
  --   pf "NEW LOCALITY % (% =?= %) OF VAR (miau)" (pp newLoc) (pp instEnvStack) (pp envStack)
  --   pure newLoc


  _ -> pure ogLocality


getEnv :: XEnv T -> Context T.EnvDef
getEnv eid = do
  tc <- State.gets typingContext
  let envdef = TC.getEnv tc eid
  pure envdef

findUsedVarsInExpr :: Expr T -> Set (T.Variable, Type T)
findUsedVarsInExpr = cata $ \(N en expr) -> case expr of
  Var v _ -> Set.singleton (v, en.t)
  e -> fold e

mCase :: CaseF T (Expr IM) (AnnStmt IM) -> Context (Case IM)
mCase kase = do
  decon <- mDecon kase.deconstruction
  pure $ Case decon kase.caseCondition kase.caseBody

mDecon :: Decon T -> Context (Decon IM)
mDecon = cata $ fmap embed . \(N en d) -> do
  mt <- mType en.t
  N mt <$> case d of
    CaseIgnore -> pure CaseIgnore
    CaseVariable uv -> do
      pure $ CaseVariable uv

    CaseRecord _ args -> do
      -- fun unsafe shit.
      let dd = case project mt of
            TCon mdd _ _ -> mdd
            mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

      margs <- for args $ \(mem, decon) -> do
        mdecon <- decon
        um <- member (dd, mem)
        pure (um, mdecon)

      pure $ CaseRecord dd margs

    CaseConstructor dc args -> do
      -- TEMP: only for now. we can put this in the CaseConstructor type later to match!
      let (params, unions, env) = case mt of
            Fix (TCon _ mparams (mus, menv)) -> (mparams, mus, menv)
            _ -> undefined
      let knockoffMatch = T.Match params unions []
      mdc <- constructor dc
        env
        knockoffMatch

      margs <- sequenceA args
      pure $ CaseConstructor mdc margs



variable :: T.VariableF IM.EnvUnion (Type IM) -> Context IM.Variable  -- NOTE: we're taking in both types, because we need to know which TVars were mapped to types and which to other tvars.
variable (T.DefinedVariable uv) = pure $ IM.DefinedVariable uv
variable (T.DefinedFunction vfn match) = do
  mfn <- mFunction match vfn
  pure $ IM.DefinedFunction mfn

variable v@(T.DefinedClassFunction cfd classInstID) = do
  pf "VARIABLE: %" (pp v)

  fn <- selectInstance classInstID
  pure $ IM.DefinedFunction fn


-- Since instances should effectively act the same as functions, I need to ensure the code is the same to not intrudoce any bugs.
mFunction :: T.MatchF IM.EnvUnion (Type IM) -> Function T -> Context (Function IM)
mFunction match vfn = do
  pf "[fun] mFunction %" $ ppDef vfn
    -- NOTE: Env must be properly monomorphised with the type map, because it can also call other functions, so each env might have different types though albeit
    --  doc/compiler/why-monomorphize-env-types-for-memo
    -- menv <- mEnvTypes vfn.functionDeclaration.functionEnv
    -- pf "IM Env Types: %" (pp menv)

    -- see definition of Context for exact purpose of these parameters.
  -- funStack <- relativeFunStack vfn.functionDeclaration.functionOther.functionStack undefined
  funStack <- trimmedStack vfn
  pf "[fun] FORCE stack: %" $ ppDef <$> funStack
  pf "[fun] memo % %" (ppDef vfn) (ppDef funStack)
  (fn, envInsts) <- memo' memoFunction (\(~mem) ~s -> s { memoFunction = mem }) (vfn, match, funStack) $ \(tfn, _, funStack') addMemo -> withTrimmed funStack' $ do
    pf "[fun] in memo"
  -- creates a type mapping for this function.
    typemap <- mkTypeMap vfn.functionDeclaration.functionOther.functionScheme match
    withTypeMap typemap $ mdo
      pf "[fun] in typemap"
      uv <- newUniqueVar tfn.functionDeclaration.functionId
      let fundec = FD env uv params ret vfn.functionDeclaration.functionOther.functionAnnotations :: FunDec IM
      let fn = Function { functionDeclaration = fundec, functionBody = body } :: Function IM
      addMemo (fn, envInsts)
      State.modify' $ \s -> s { functionStack = fn : s.functionStack }

      pf "VARIABLE OF MEMO: %" (pp uv)

      params <- traverse (bitraverse mDecon mType) tfn.functionDeclaration.functionParameters
      ret <- mType tfn.functionDeclaration.functionReturnType


      -- DEBUG: when in the process of memoization, show dis.
      -- pf "Decl: % -> %" (Def.encloseSepBy "(" ")" ", " $ pp <$> ts) (pp ret)
      -- pf "M %: %" dbgFunctionTypeName (pp fundec.functionId)


      -- add memo, THEN traverse body.
      ((body, envInsts), env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        stmts <- mBody (pp fundec.functionId) tfn.functionBody
        thisFunctionsEnvs <- State.gets envInstantiations
        pure (stmts, thisFunctionsEnvs)

      pf "[fun] exit mFunction % in memo" uv
      pf "[fun] env insts %" envInsts
      State.modify' $ \s -> s
        { functionStack = tail s.functionStack
        }
      pure (fn, envInsts)

  let thisFunsEnvInsts = envInsts
  let
    nuEnvID = M.envDefID fn.functionDeclaration.functionEnv
    oldEnvID = vfn.functionDeclaration.functionEnv
    envuse = EnvUses $ Map.singleton fn.functionDeclaration.functionEnv (Set.singleton fn)
  State.modify' $ \c -> c
    { envInstantiations
      = Map.insertWith (<>) nuEnvID envuse   -- NOTE: this shid outside of memo
      $ Map.insertWith (<>) oldEnvID envuse
      $ Map.unionWith (<>) thisFunsEnvInsts c.envInstantiations
    }
  pf "[fun] REGISTERED FUNCTION % (env: %) with ENV INSTANTIATIONS: %" (pp fn.functionDeclaration.functionId) (pp $ IM.envDefID fn.functionDeclaration.functionEnv) (pp fn.functionDeclaration.functionOther)
  pure fn

-- they should somehow be connected, shouldn't they?
trimmedStack :: Function T -> Context [Function IM]
trimmedStack vfn = do
  funStack <- State.gets functionStack
  envdef <- getEnv vfn.functionDeclaration.functionEnv
  let envStack = envdef.envStack  -- HACK: should be a "function stack" - right now it should work, but if I add a multiline lambda, it'll break. we need info about generalization/instantiation stack.
      sz = length envStack
  pure $ reverse $ take sz $ reverse funStack

withTrimmed :: [Function IM] -> Context a -> Context a
withTrimmed fns fx = do
  fs <- State.gets functionStack
  State.modify $ \s -> s { functionStack = fns }
  x <- fx
  State.modify $ \s -> s { functionStack = fs }
  pure x

-- type AppliedAssocs = [Type T]
-- forceFunctionType :: Type IM -> ([Type IM], Type IM, AppliedAssocs, T.EnvF (Type T))
-- forceFunctionType uciOrUfi et = case project et of
--     TFun (IM.EnvUnion { IM.oldUnion = union }) mts mret ->
--       let findFn = case uciOrUfi of
--             Left uci -> \(muci, _, _, _) -> Just uci == muci
--             Right ufi -> \(_, ufi', _, _) -> ufi == ufi'

--           (_, _, appliedAssocs, tEnv) = fromJust $ find findFn $ union.union
--       in (mts, mret, appliedAssocs, tEnv)

--     _ -> error "NOT A FUNCTION TYPE BRUH"


-- selectInstance' :: Def.ClassInstID -> Context (Function IM)
-- selectInstance' cid = do
--   (ifn, match) <- selectInstance cid
--   let tfn = Common.instanceToFunction ifn
--   fn <- mFunction match tfn
--   pure fn

selectInstance :: Def.ClassInstID -> Context (Function IM)
selectInstance classInstID = do
  tm <- State.gets tvarMap
  case tm.tmAssocMap !? classInstID of
    Just fn -> pure fn
    Nothing -> do
      tc <- State.gets typingContext
      case (tc ^. TC.globalInsts) !? classInstID of
        Just (tfn, tmatch) -> do
          match <- bitraverse mUnion mType tmatch
          mFunction match tfn
        Nothing -> error $ pf "Instance not found for %." classInstID
  -- get instance from typing context, profit.
  -- mself <- mType self
  -- ucis <- State.gets classInstantiationAssociations
  -- pf "SNAPSHOT UCIS: %" (ppDef $ Map.keysSet <$> ucis)
  -- case ucis !? uci of
  --   Just insts -> do
  --     let inst = mustSelectInstance mself insts
  --     let instfun = fromJust $ find (\ifn -> ifn.instClassFunDec == cfd) inst.instFuns
  --     pure instfun

  --   -- we might be top level here, so we fall back to the snapshot.
  --   Nothing ->
  --     let dd = case project mself of
  --           TCon mdd _ _ -> mdd.ddScheme.ogDataDef
  --           _ -> error "WHAT THJE FUCK"
  --     in case snapshot !? cd >>= (!? dd) of
  --       Just inst ->
  --         let instfun = fromJust $ find (\ifn -> ifn.instClassFunDec == cfd) inst.instFuns
  --         in pure instfun
  --       Nothing -> do
  --         let selfTVar = case project self of
  --               TO (T.TVar tv) -> Just tv
  --               _ -> Nothing
  --         error $ Def.pf "SNAPSHOT %\nSNAPSHOT UCIS %\nLOOKING FOR %\nCOULD NOT FIND INSTANCE (tvar: %, uci: %, mt: %) in % (could get: (%))" (T.dbgSnapshot snapshot) (ppDef $ Map.keysSet <$> ucis) (pp dd.ddName) (pp selfTVar) (pp uci) ("<type>" :: Def.Context) (pp cfdId) (Def.ppSet pp $ Set.toList $ Map.keysSet ucis)




mBody :: Traversable f => Def.Context -> f (AnnStmt T) -> Context (f (AnnStmt IM))
mBody dbgName body = do
  -- Collects all instantiations from the current scope and monomorphises them.
  -- This way we know how many environments we should create when we get to Inst or Fun.
  let usedVarsInCurrentScope = findUsedVarsInFunction body

  pf "% level vars: %" dbgName $ Def.ppSet (\(v, _) -> pp v) $ Set.toList usedVarsInCurrentScope
  for_ (Set.toList usedVarsInCurrentScope) $ \(v, t) -> do
    pf "% level TYPE: %" dbgName t
    _ <- mType t
    pf "% level VAR: %" dbgName v
    _ <- variable =<< bitraverse mUnion mType v
    pure ()


  -- then actually do the scope thing.
  traverse mAnnStmt body


findUsedVarsInFunction :: Foldable t => t (AnnStmt T) -> Set (T.Variable, Type T)
findUsedVarsInFunction = foldMap $ cata $ \(O (O (Annotated _ (Located _ stmt)))) -> case first findUsedVarsInExpr stmt of
  Return expr -> findUsedVarsInExpr expr
  s -> bifold s



constructor :: DataCon T -> [Type IM] -> MatchF IM.EnvUnion (Type IM) -> Context (DataCon IM)
constructor tdc@(DC dd@(DD ut (scheme, _) _ _) _ _ _) env match = do
  -- munions <- for tunions $ \(u, params, ret) -> do  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
  --   mparams <- traverse mType params
  --   mret    <- mType ret
  --   maybeEmptyUnion <- hideEmptyUnions u
  --   munion <- for maybeEmptyUnion $ \mu -> mUnion (mu, mparams, mret)
  --   pure (munion, mparams, mret)  
  -- -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  tm <- mkTypeMap scheme match
  (_, dcQuery) <- mDataDef (dd, match, env)
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ Def.pf "[COMPILER ERROR]: Failed to query an existing constructor for type %.\n TypeMap: %\n" (pp ut) (ppTypeMap tm)

  pure mdc

member :: (DataDef IM, Def.MemName) -> Context Def.UniqueMem
member = memo memoMember (\mem s -> s { memoMember = mem }) $ \(_, memname) _ -> do
  -- TODO: maybe this should be the same as `constructor`, where I just mDataType and find the member?
  --  at least for consistency. also, there won't be incorrect members! but right now, I'll try like this.
  mkUniqueMember memname


mType :: Type T -> Context (Type IM)
mType tid = do
  tc <- State.gets typingContext
  let tu = tc ^. globalTypeUni
      getType = snd . TC.getTypeFromUni tu
      go' = go . fmap go' . getType
  go' tid where

  go :: TypeF T (Context (Type IM)) -> Context (Type IM)
  go = thisAnd (countUp mTypeNum) . \case
    TCon dd pts (tunions, tenv) -> mdo
      params <- sequenceA pts
      munions <- traverse mUnion tunions
      menv <- traverse mType tenv
      let knockoffMatch = T.Match params munions []

      -- pf "Type shit: % % %" (ppDef dd) params munions
      (mdd, _) <- mDataDef (dd, knockoffMatch, menv)
      let mt = Fix $ TCon mdd params (munions, menv)
      pure mt

    TFun union params ret -> do
      pf "TFun"
      params' <- sequenceA params
      ret' <- ret
      union' <- mUnion union

      pure $ Fix $ TFun union' params' ret'

    TO (T.TVar tv) -> do
      retrieveTV tv

    TO (T.TyVar tv) -> error $ Def.pf "[COMPILER ERROR]: Encountered TyVar %." (pp tv)


-- ISSUE(unused-constructor-elimination): yeah, this is bad. we also need to remember to map the empty unions (through type map.)
hideEmptyUnions :: T.EnvUnionF u a -> Context (Maybe (T.EnvUnionF u a))
hideEmptyUnions u = do
  TypeMap _ mus _ <- State.gets tvarMap
  if Map.member u.unionID mus || not (T.isUnionEmpty u)
    then do
      -- params' <- traverse mType params
      -- ret' <- mType ret
      pure $ Just (u)
    else pure Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (DataDef T, MatchF IM.EnvUnion (Type IM), [Type IM]) -> Context (DataDef IM, Map (DataCon T) (DataCon IM))
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(tdd@(DD ut (scheme@(T.Scheme tvs unions _), envScheme) tdcs ann), match, envs) addMemo -> do
    pf "[data] % % %" tdd match envs
    tm <- mkTypeMap' $ (scheme, match) :| [(T.Scheme envScheme [] [], T.Match envs [] [])]
    withTypeMap tm $ mdo

      pf "OLD TYPE: %" ut

      nut <- newUniqueType ut
      pf "NEW TYPE: %" nut

      let mts = tvs <&> \tv -> tm.tmTVarMap ! tv
      let mdd = DD nut (IM.OtherDD mts) mdcs ann
      addMemo (mdd, dcQuery)


      -- Strip "unused" constructors. Currently, these are constructors that contain empty unions.
      -- TEMP: This is not finished - it only cares about unions, but a more thorough solution would track which constructors of a particular type were actually used.
      -- NOTE: also, there is something to be said about eliminating non-existent members/constructors. if we only index member by offsets and don't export it, then should we honor the structure? IMO no, unless explicitly specified in an annotation or something.
      tc <- State.gets typingContext
      let tu = tc ^. globalTypeUni
      let strippedDCs = tdcs <&> filter (\(DC _ _ conTs _) ->
            let
              isUnionEmpty :: T.EnvUnion -> Any
              isUnionEmpty unionUID =
                -- NOTE: we must first replace it. also, HACK: it's retarded. TODO: make it better.
                let union = snd $ TC.getUnionFromUni tu unionUID
                in case tm.tmUnionMap !? union.unionID of
                  Just eu -> Any $ null eu.union
                  Nothing -> Any $ null union.union

              hasEmptyUnions :: Type T -> Any
              hasEmptyUnions = go' where
                getType = snd . TC.getTypeFromUni tu
                go' = go . fmap go' . getType

                go :: TypeF T Any -> Any
                go = \case
                  TFun union ts t -> isUnionEmpty union <> foldMap hasEmptyUnions (snd $ TC.getUnionFromUni tu union) <> fold ts <> t
                  TCon _ ts (fnUnions, envts) -> fold ts <> foldMap isUnionEmpty fnUnions <> foldMap hasEmptyUnions envts
                  t -> fold t

              dcHasEmptyUnions :: [Type T] -> Bool
              dcHasEmptyUnions = getAny . foldMap hasEmptyUnions
            in not $ dcHasEmptyUnions conTs)

      mdcs <- case strippedDCs of
        Right dcs -> fmap Right $ for dcs $ \(DC _ uc ts dcann) -> do
            nuc <- newUniqueCon uc
            mdcts <- traverse mType ts
            pure $ DC mdd nuc mdcts dcann

        Left drs -> fmap Left $ for drs $ \(Annotated anns (memname, memtype)) -> do
            um <- member (mdd, memname)
            mt <- mType memtype
            pure $ Annotated anns (um, mt)


      -- DEBUG: how datatypes are transformed.
      pf "Mono: %" (Def.ppTypeInfo ut)
      pf "======"
      pc tdcs
      pf "------"
      pc strippedDCs
      pf ",,,,,,"
      pc $ either (const "n/a (it's a record.)") (Def.ppLines . fmap (\(DC _ uc _ _) -> Def.ppCon uc)) mdcs
      pf "======"
      pf "Mono'd: %" (pp nut)

      -- used only by non-record types!
      let dcQuery = Map.fromList $ case (strippedDCs, mdcs) of
            (Right ttdcs, Right mmdcs) -> zip ttdcs mmdcs
            (Left _, Left _) -> mempty
            _ -> error "caulk."  -- does not have to be very sane - controlled environment.

      pure (mdd, dcQuery)


-- relativeFunStack :: Def.FunStack -> [(Function T, T.Match)] -> Context [Function IM]
-- relativeFunStack tfunstack fncontext = do -- top: most inner fun
--   cfunstack <- State.gets functionStack
--   let baseRelative
--         = reverse
--         $ map snd
--         $ takeWhile (\(uv, (_, uv')) -> uv == uv')
--         $ zip (reverse tfunstack) (reverse cfunstack)
--   oldStack <- State.gets functionStack
--   State.modify' $ \s -> s { functionStack = baseRelative }
--   fns <- enstack fncontext
--   State.modify' $ \s -> s { functionStack = oldStack }
--   pure $ reverse fns <> (fst <$> baseRelative)


retrieveTV :: TVar T -> Context (Type IM)
retrieveTV tv = do
  TypeMap typeMap _ _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error happens) when an environment is outside of its scope.
    Nothing ->
      error $ Def.pf "TVar not mapped: %" tv



withTypeMap :: TypeMap -> Context a -> Context a
withTypeMap tm a = do
  pf "start withTypeMap"
  -- DEBUG: check typemap.
  -- pf "Type map:"
  -- pc $ ppTypeMap tm

  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- withContext (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify' $ \s -> s { tvarMap = ogTM }

  pf "end withTypeMap"

  pure x


mUnion :: T.EnvUnion -> Context IM.EnvUnion
mUnion tunionUID = thisAnd (countUp mUnionNum) $ do
  pf "[union] mUnion %" tunionUID
  tc <- State.gets typingContext
  let tu = tc ^. globalTypeUni
      tunion = snd $ TC.getUnionFromUni tu tunionUID

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  unionmap <- State.gets $ tmUnionMap . tvarMap
  pf "[union] test: %" $ isJust $ unionmap !? tunion.unionID
  pf "[union] after unionmap"
  case unionmap !? tunion.unionID of
    Just mru -> do
      pf "aaaa"
      pure mru
    Nothing -> do
      pf "nothing"
      mUnionWithoutTopMap tunionUID

-- for fixpoint shit
mUnionWithoutTopMap :: T.EnvUnion -> Context IM.EnvUnion
mUnionWithoutTopMap tunionUID = thisAnd (countUp mUnionNum) $ do
      tc <- State.gets typingContext
      let tu = tc ^. globalTypeUni
      let (baseUID, tunion) = TC.getUnionFromUni tu tunionUID
      pf "[union] mUnionWithoutTopMap: %" tunion.unionID

      pf "[union] tunion: %" tunion
      munion <- do
          pf "not cuck"

          -- HACK NEW: use function stack to locally scope unions.
          -- normal union - all TVars mapped. safe to memoize.
          -- TODO FIND A BETTER WAY!!
          fns <- State.gets functionStack
          pf "[union] try memo % %" baseUID (ppDef <$> fns)
          --     TODO this is kinda funny... ghetto scoped monomorphisations. I should make a better data structure after I fix all. but it should work for now.
          -- mu <- State.gets memoUnion
          -- let mfoundUnion = listToMaybe $ catMaybes $ map (\localfns -> isMemoed (baseUID, localfns) mu) $ tails fns
          -- case mfoundUnion of
          --   Just foundUnion -> pure foundUnion
          --   Nothing -> do
          do
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) (baseUID, fns) $ \(_, fns') addMemo -> mdo
                  nuid <- newUnionID
                  pf "[union] newid % <- % %" nuid (ppDef fns') tunion
                  let munion = M.EnvUnion { IM.unionID = nuid, IM.union = envs }
                  addMemo munion
                  pf "[union] try memo2  % %" baseUID (ppDef <$> fns)
                  pf "[union] memo before traverse"
                  menvs <- traverse unionMemberToEnv tunion.union
                  pf "[union] memo after traverse"
                  pf "[union] envs % %" tunion.unionID menvs

                  envs <- case menvs of
                    [] -> do
                      -- check disabled for now. we're not eliminating unused unions yet.
                      -- error $ Def.pf "[COMPILER ERROR]: Encountered an empty union (ID: %) - should not happen." (show tunion.unionID)
                      neid <- newEnvID  -- TEMP
                      pure $ NonEmpty.singleton $ M.EnvDef neid [] 0

                    (e:es) -> do
                      -- pf "NEW NORMAL UNION: % % % => %" tunion'' params ret nuid
                      pure $ NonEmpty.nub $ e :| es

                  -- THIS IS SO STUPID.
                  -- we might actually mono the union here and keep the ID.
                  -- but I generate a new one before, right?
                  -- basically:
                  --   1. if the union is not recursive, we can simply overwrite the memo and nothing happens.
                  --   2. if the union is recursive (through matches), then we are sure, that the next thing is "new" (because that new ID will be later compared and not be equal)
                  -- At least that's what I think.
                  -- but this is TEMP: I should figure out how to approach instantiating unions in the environment (since they clearly need to be instantiated)
                  -- for TEST 1_t26
                  munion' <- memo' memoUnion' (\mem mctx -> mctx { memoUnion' = mem }) (tunion.unionID, envs) $ \(_, _) _ ->
                    pure munion  -- save current union or get a previous one.


                  pure munion'

      pf "[union] mUnionWithoutTopMap end"
      pure munion



unionMemberToEnv :: T.UnionMemberF T.EnvUnion (Type T) -> Context M.EnvDef
unionMemberToEnv = \case
  T.UnionFun fn outers match -> do
    pf "[mem2env] UnionFun"
    -- ogFunStack <- relativeFunStack fn.functionDeclaration.functionOther.functionStack outers -- most indented: head
    pf "bruh?"
    mmatch <- bitraverse mUnion mType match
    pf "[mem2env] after bitraverse"

    prevFunStack <- State.gets functionStack
    pf "[mem2env] old' fun stack: %" $ ppDef prevFunStack
    pf "[mem2env] match: %" mmatch
    outerfns <- enstack outers
    mfn <- stackFun (reverse outerfns) $ mFunction mmatch fn
    pf "[mem2env] exit"
    pure mfn.functionDeclaration.functionEnv

  T.UnionLam env outers -> do
    outerfns <- enstack outers
    ((), menv) <- stackFun (reverse outerfns) $ withEnv Nothing env (pure ())
    pure menv

  T.UnionConEnv eid ->
    snd <$> withEnv Nothing eid (pure ())

-- we assume these are "top matches" - they are already mapped and we don't need a type map.
enstack :: [(Function T, T.Match)] -> Context [Function IM]
enstack [] = pure []
enstack ((tfn, tm):trem) = do
  pf "[enstack] miau"
  pf "[enstack] %" $ first ppDef tm
  m <- bitraverse mUnion mType tm
  pf "[enstack] after bitraverse"
  fn <- mFunction m tfn
  pf "[enstack] after fun"

  rem <- stackFun [fn] $ enstack trem
  pf "[enstack] exit"

  pure (fn : rem)

stackFun :: [Function IM] -> Context a -> Context a
stackFun fns fx = do
  prevFunStack <- State.gets functionStack
  State.modify' $ \s -> s { functionStack = fns ++ s.functionStack }
  x <- fx
  State.modify' $ \s -> s { functionStack = prevFunStack }
  pure x


------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context'
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , tvarInsts :: Map (TVar T) (Map (ClassDef T) (InstDef T))  -- TODO: smell.
  , memoFunction :: Memo (Function T, MatchF IM.EnvUnion (Type IM), [Function IM]) (Function IM, Map Def.EnvID EnvUses)
  , memoDatatype :: Memo (DataDef T, MatchF IM.EnvUnion (Type IM), [Type IM]) (DataDef IM, Map (DataCon T) (DataCon IM))
  , memoEnv :: Memo (Def.EnvID, [Function IM]) IM.EnvDef
  , memoUnion :: Memo (T.EnvUnion, [Function IM]) IM.EnvUnion
  , memoUnion' :: Memo (Def.UnionID, NonEmpty M.EnvDef) IM.EnvUnion
  , memoMember :: Memo (DataDef IM, Def.MemName) Def.UniqueMem

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo Def.UnionID IM.EnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  , cuckedUnionInstantiation :: Map IM.EnvUnion (Set (T.EnvDefF IM.EnvUnion (Type IM)))  -- (NOTE: THIS IS ACTUALLY USED AT THE END. LSP CAN'T COMPREHEND OVERLOADED RECORD DOTS) this one is to track all environments which get instantiated for this union. (not sure if it's still needed if we pre-search variables in body anyway.)
  -- also, this can be done in the same way as subst - would even require us to track less state.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: Map Def.EnvID EnvUses  -- NOTE: FUTURE TYPECHECK

  , currentEnvStack :: Def.EnvStack -- HACK: it's for knowing when instances should be local or not. (TC ENV STACK, NOT THE NEW IDs)
  , lastEnvironment :: [(IM.Variable, Type IM)]  -- HACK: for knowing which variable should envmod use.
  , functionStack :: [Function IM]  -- HACK: for unions, so that whatever ill finish it later.
  , unionMemoTransform :: Map T.EnvUnion IM.EnvUnion   -- HACK: while we are iterating, we may encounter the same union in Match. This breaks these cycles.

  , completedEnvs :: Set IM.EnvDef
  , environmentsLeft :: Map IM.EnvDef [Function IM]

  -- Should be Reader, but for now it's state.
  , typingContext :: TC.TypingContext
  }
newtype Context a = Context { fromContext :: StateT Context' BaseCtx a } deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadFix, MonadState Context', Memoizable)

startingContext :: TC.TypingContext -> Context'
startingContext tc = Context'
  { tvarMap = mempty
  , tvarInsts = mempty
  , memoFunction = emptyMemo
  , memoDatatype = emptyMemo
  , memoEnv = emptyMemo
  , memoUnion = emptyMemo
  , memoUnion' = emptyMemo
  , memoMember = emptyMemo

  , cuckedUnions = emptyMemo
  , cuckedUnionInstantiation = mempty

  , currentEnvStack = mempty
  , lastEnvironment = mempty
  , functionStack = mempty
  , unionMemoTransform = mempty
  , envInstantiations = mempty

  , completedEnvs = mempty
  , environmentsLeft = mempty

  , typingContext = tc
  }


-----------------------
-- TypeMap stuff
----------------------

-- HACK: EnvUnions are only needed when monomorphizing types. However, it's slightly easier right now to add this field. This should probably change later.
--  TODO: what did I mean???
data TypeMap = TypeMap
  { tmTVarMap :: (Map (TVar T) (Type IM))
  , tmUnionMap :: (Map Def.UnionID IM.EnvUnion)
  , tmAssocMap :: (Map Def.ClassInstID (Function IM))
  }

instance Semigroup TypeMap where
  TypeMap l1 l2 l3 <> TypeMap r1 r2 r3 = TypeMap (l1 <> r1) (l2 <> r2) (l3 <> r3)

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty mempty


ppTypeMap :: TypeMap -> Def.Context
ppTypeMap (TypeMap tvs unions assocs) = Def.ppLines'
  [ (Def.ppMap . fmap (bimap pp pp) . Map.toList) tvs
  -- , (Def.ppMap . fmap (bimap pp pp) . Map.toList) unions
  -- , (Def.ppMap . fmap (bimap pp pp) . Map.toList) assocs
  ]

mkTypeMap :: T.Scheme T -> T.MatchF IM.EnvUnion (Type IM) -> Context TypeMap
mkTypeMap s m = mkTypeMap' (NonEmpty.singleton (s, m))

mkTypeMap' :: NonEmpty (T.Scheme T, T.MatchF IM.EnvUnion (Type IM)) -> Context TypeMap
mkTypeMap' sms = mdo
  tc <- State.gets typingContext

  let (T.Scheme sTVs suUnions suAssocs, T.Match mTVs mUnions muAssocs) = sconcat sms
  let tu = tc ^. globalTypeUni
  let sUnions = T.unionID . snd . TC.getUnionFromUni tu <$> suUnions
  let sAssocs = suAssocs <&> \(T.FunctionTypeAssociation _ _ _ classInstID _) -> classInstID

  -- NOTE NEW: not sure if this is correct. we want to apply all previous type maps to this, from left to right.
  -- prevtm <- fold <$> traverse (uncurry mkTypeMap) prevMatches
  
  let tm = TypeMap
        { tmTVarMap  = Map.fromList $ zip sTVs mTVs
        , tmUnionMap = Map.fromList $ zip' sUnions mUnions
        , tmAssocMap = Map.fromList $ zip' sAssocs mAssocs
        }

  (mAssocs) <- withTypeMap tm $ do  -- not sure I need back references here? the thing is, it probably does not matter where it will get evaluated. but just in case?
    -- mmUnions <- traverse mUnionWithoutTopMap muUnions
    mmAssocs <- traverse selectInstance muAssocs
    pure (mmAssocs)

  pure tm

zip' :: [a] -> [b] -> [(a, b)]
zip' [] _ = []
zip' (x:xs) ~(y:ys) = (x,y) : zip' xs ys


newUniqueType :: Def.UniqueType -> Context Def.UniqueType
newUniqueType ut = do
  tid <- liftIO newUnique
  pure $ ut { Def.typeID = tid }


newUniqueCon :: Def.UniqueCon -> Context Def.UniqueCon
newUniqueCon uc = do
  cid <- liftIO newUnique
  pure $ uc { Def.conID = cid }


newUniqueVar :: Def.UniqueVar -> Context Def.UniqueVar
newUniqueVar uv = do
  vid <- liftIO newUnique
  pure $ uv { Def.varID = vid }

mkUniqueMember :: Def.MemName -> Context Def.UniqueMem
mkUniqueMember memname = do
  mid <- liftIO newUnique
  pure $ Def.MI { memName = memname, memID = mid }


newEnvID :: Context Def.EnvID
newEnvID = do
  eid <- liftIO newUnique
  pure $ Def.EnvID { fromEnvID = eid }


newUnionID :: Context Def.UnionID
newUnionID = do
  eid <- liftIO newUnique
  pure $ Def.UnionID { fromUnionID = eid }




--------------------------------------------------------
-- STEP 2: Map missing shit.
-- NOTE: THIS IS TYPESAFE BUT BAD. WE BASICALLY ARE REDOING MONOMORPHIZATION IN THE SAME AMOUNT OF LINES. Maybe a less typesafe data structure would be better, as it would cut down on half the file. Or somehow do it in real time - check when the scope exits and then map the instances.
--------------------------------------------------------


expectIDataDef :: Type IM -> DataDef IM
expectIDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

expectDataDef :: Type M -> DataDef M
expectDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))





----------------------
-- UNRELATED MISC
----------------------

instance Foldable ((,,) a b) where
  foldr f x (_, _, y) = f y x

instance Traversable ((,,) a b) where
  traverse f (a, b, x) = (a, b,) <$> f x



withContext :: (Context' -> Context') -> Context a -> Context a
withContext fn (Context sx) =
  Context $ State.withStateT fn sx

instance (unit ~ ()) => Log (Context unit) where
  plog lt x = do
    tc <- State.gets typingContext
    let tu = tc ^. TC.globalTypeUni
        te = tc ^. TC.globalEnvs
    let typePrinter = TC.ppTypeFromUniSafe tu
        unionPrinter = TC.ppUnionFromUniSafe tu
        unionIDPrinter = TC.ppUnionIDFromUniSafe tu
        envPrinter = TC.ppEnvFromUniSafe te

        p = PrintContext typePrinter unionPrinter unionIDPrinter envPrinter
    Context $ lift $ plog lt $ Reader.local (\c -> c { Def.printContext = Just p }) x



nePrepend :: [a] -> a -> NonEmpty a
nePrepend fronts last = NonEmpty.prependList fronts $ NonEmpty.singleton last


-- I think there was an actual function that did this kek.
{-# inline thisAnd #-}
thisAnd :: Monad m => m () -> m a -> m a
thisAnd f g = do
  x <- g
  f
  pure x

countUp :: Lens' Stats Counter -> Context ()
countUp l = Context $ countUp' l




newtype EnvUses = EnvUses { fromEnvUses :: Map M.EnvDef (Set (Function M)) }

-- instance Eq EnvUse where
--   EnvUse _ le == EnvUse _ re = le == re

-- instance Ord EnvUse where
--   EnvUse _ le `compare` EnvUse _ re = le `compare` re

instance PP EnvUses where
  pp (EnvUses efns) = pp $ fmap (\(e, fns) -> Def.pf "% => %" e fns :: Def.Context) $ fmap2 (Def.ppDef . Set.toList) $ Map.toList efns

instance Semigroup EnvUses where
  EnvUses l <> EnvUses r = EnvUses $ Map.unionWith (<>) l r

instance Monoid EnvUses where
  mempty = EnvUses mempty
