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
import qualified AST.Common as Common
import Data.Fix (Fix(..))
import Data.Functor.Foldable (embed, cata, para, project)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first, bimap)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.Map (Map, (!?), (!))
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (fold, for_)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe, fromJust, maybeToList, fromMaybe, isJust)
import Data.Set (Set)
import Misc.Memo (Memo (..), emptyMemo, memo, memo', isMemoed)
import qualified Misc.Memo as Memo
import Data.Monoid (Any (Any, getAny))
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Bifoldable (bifold)
import Control.Monad (void, (<=<))
import Data.String (fromString)
import Data.List (find, partition)
import AST.Common (AnnStmt, Module, StmtF (..), Expr, ExprNode (..), ExprF (..), Function (..), TypeF (..), ClassFunDec (..), Type, CaseF (..), Case, Decon, DeconF (..), FunDec (..), TVar (..), DataDef (..), DataCon (..), ClassDef, InstDef, IfStmt (..), instFunDec, InstFun, MutAccess (..), askNode)
import AST.Mono (M)
import AST.IncompleteMono (IM)
import AST.Def ((:.) (..), Annotated (..), Locality (..), PP (..), fmap2, PPDef (..), traverse2, sequenceA2, (<+>), Located (..), Log, PrintfType)
import qualified AST.IncompleteMono as IM
import qualified AST.Def as Def
import Data.List (nubBy)
import Data.List (nub)
import Stats (Counter, mStmtNum, mExprNum, mTypeNum, mUnionNum, mfStmtNum, mfExprNum, mfTypeNum, mfUnionNum)
import BaseCtx (BaseCtx, countUp')
import AST.Typed (TC, MatchF)
import qualified TypingContext as TC
import TypingContext (globalTypeUni)
import Lens.Micro ((^.))
import Lens.Micro.Mtl (use)

type T = TC


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
  (mistmts, monoCtx) <- flip State.runStateT (startingContext tc) $ do
    mBody "[top level]" tmod

  let imEnvs = memoToMap monoCtx.memoEnv

  phase "Monomorphisation (env instantiations)"
  pc $ (Def.ppMap . fmap (bimap pp (Def.encloseSepBy "[" "]" ", " . fmap (\(e, fns) -> pf "%: %" e (ppDef fns) :: Def.Context) . Map.toList . IM.fromEnvUses)) . Map.toList) monoCtx.envInstantiations

  phase "Monomorphisation (just envs)"
  pc $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) imEnvs

  phase "Monomorphisation (first part)"
  pc $ Def.ppLines mistmts

  phase "Monomorphisation (cucked unions)"
  pc $ monoCtx.cuckedUnionInstantiation


  (mmod) <- withEnvContext imEnvs monoCtx.envInstantiations monoCtx.cuckedUnionInstantiation $ do
    mstmts <- mfAnnStmts mistmts
    pure $ M.Mod { M.topLevelStatements = mstmts }

  pure (mmod)



mAnnStmt :: AnnStmt T -> Context (AnnStmt IM)
mAnnStmt = cata (fmap embed . thisAnd (countUp' mStmtNum) .  f) where
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
        let env = fn.functionDeclaration.functionEnv
        let envID = T.envDefID env
        envInsts <- State.gets envInstantiations

        let currentEnvUses = fromMaybe mempty $ envInsts !? envID
        let envUses = foldMap Set.toList $ IM.fromEnvUses currentEnvUses -- <&> \(IM.EnvUse (Just fn) env) -> (fn, env)

        pf "ENCOUNTERED FUN %" (pp fn.functionDeclaration.functionId)
        envDefs <- orderEnvironments envUses
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ IM.EnvInsts $ x :| xs

      Inst inst -> do
        envInsts <- State.gets envInstantiations

        let envUses = flip concatMap inst.instFuns $ \fn ->
              let env = fn.instFunDec.functionEnv
                  envID = T.envDefID env
                  currentEnvUses = fromMaybe mempty $ envInsts !? envID
                  defs = foldMap Set.toList $ IM.fromEnvUses currentEnvUses
              in  defs

        pf "ENV INSTS: %" (pp envInsts)
        pf "ENCOUNTERED INST: %" (pp $ instFunDec <$> inst.instFuns)
        pf "INST TURNED TO: %" (pp $ functionDeclaration <$> envUses)
        envDefs <- orderEnvironments envUses
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ IM.EnvInsts $ x :| xs

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
orderEnvironments :: [Function IM] -> Context [Either IM.EnvMod IM.EnvInst]
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
    loop :: [(Function IM, [Function IM])] -> Context [Either IM.EnvMod IM.EnvInst]
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
            pure $ fmap Right $ incomplete <&> \(e, ds) -> IM.EnvInst { envDef = e, notYetInstantiated = ds }
          else do
            setComplete $ functionEnv . functionDeclaration . fst <$> complete
            let completedStmts = complete <&> \(e, deps) -> Right $ IM.EnvInst { envDef = e, notYetInstantiated = deps }  -- NOTE: maybe we should filter out ONLY outer envs.
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
  State.modify $ \c -> c { environmentsLeft = newEnvsLeft <> c.environmentsLeft }


setComplete :: [IM.EnvDef] -> Context ()
setComplete fns = State.modify $ \c -> c { completedEnvs = c.completedEnvs <> Set.fromList fns }

getEnvDependencies :: IM.EnvDef -> [Function IM]
getEnvDependencies (IM.EnvDef _ vars _) = mapMaybe (\(v, _, _) -> case v of { IM.DefinedFunction fn -> Just fn; _ -> Nothing }) vars
-- getEnvDependencies _ = error "RECURSIVE ENV WHAT."


mExpr :: Expr T -> Context (Expr IM)
mExpr = cata $ thisAnd (countUp' mExprNum) . fmap embed . \(N en expr) -> do
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
          mv <- variable =<< traverse mType v

          envStack <- State.gets currentEnvStack
          newLocality <- reLocality envStack locality v

          pure $ Var mv newLocality

        Con c (eid, match) -> do
          mc <- constructor c =<< traverse mType match

          -- don't forget to register usage. (for codegen)
          void $ withEnv Nothing (T.EnvDef eid [] []) $ pure ()

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

withEnv :: Maybe (Function IM) -> T.EnvDefF (Type T) -> Context a -> Context (a, IM.EnvDef)
withEnv mfn env@(T.EnvDef eid _ lev) cx = do
  itenv <- traverse mType env  -- NOTE: We need to differentiate envs by their types. I wonder if we need the second type there?
  menv@(IM.EnvDef _ envContent _) <- memo' memoEnv (\m c -> c { memoEnv = m }) itenv $ \(T.EnvDef _ envContent envStack) _ -> do
      newEID <- newEnvID
      let envLevel = Def.envStackToLevel envStack
      menvContent <- for envContent $ \(v, l, mt) -> do
        let vv = v
        mv <- variable vv

        newLocality <- reLocality envStack l vv

        pure (mv, newLocality, mt)

      pure $ IM.EnvDef newEID menvContent envLevel  -- env IDs changed, so kind of hard to track env stack. that's why only level. might not even need this.
  
  -- SAVE PREVIOUS STATE
  prevlev <- State.gets currentEnvStack
  prevCompleteEnvs <- State.gets completedEnvs
  prevEnvsLeft <- State.gets environmentsLeft
  lastEnv <- State.gets lastEnvironment
  usedEnvs <- State.gets envInstantiations
  cusKeys <- Map.keysSet . Memo.memoToMap <$> State.gets cuckedUnions

  -- SET NEW LOCAL STATE
  let curlev = eid : lev

  State.modify $ \c -> c
    { currentEnvStack = curlev
    , completedEnvs = mempty
    , environmentsLeft = mempty
    , lastEnvironment = envContent <&> \(v, _, t) -> (v, t)
    , envInstantiations = mempty
    }

  -- NOTE: recursively add environments all environments. (is not yet ready for recursiveness)
  let doEnvIncompletes (IM.EnvDef _ envContent _) = concatMap ((\case { IM.DefinedFunction fn -> fn.functionDeclaration.functionEnv : doEnvIncompletes fn.functionDeclaration.functionEnv; _ -> [] }) . (\(v, _, _) -> v)) envContent
  pf "WITH ENV INCOMPLETE: %" $ pp $ doEnvIncompletes menv <&> \e -> (e, functionId . functionDeclaration <$> getEnvDependencies e)
  pf "used envs: %" (pp usedEnvs)

  setIncomplete $ (\e -> (e, filter ((== length curlev) . IM.envDefLevel . functionEnv . functionDeclaration) $ getEnvDependencies e)) <$> doEnvIncompletes menv
  x <- cx


  -- RETRIEVE PREVIOUS STATE
  State.modify $ \c -> c
    { currentEnvStack = prevlev
    , completedEnvs = prevCompleteEnvs
    , environmentsLeft = prevEnvsLeft
    , lastEnvironment = lastEnv
    , envInstantiations = Map.unionWith (<>) usedEnvs c.envInstantiations  -- only allow non-local instantiations through. (otherwise we get extra environment declarations)
    , cuckedUnions = Memo $ Map.restrictKeys (Memo.memoToMap c.cuckedUnions) cusKeys -- cucked unions should be local per function
    }


  pf "%M: % =WITH ENV%=> %" (pp $ T.envDefID env) (pp env) (case mfn of { Nothing -> "" :: Def.Context; Just fn -> fromString $ Def.pf " (%)" $ pp fn.functionDeclaration.functionId }) (pp menv)

  pure (x, menv)


-- Evaluate the locality of a class function after we have access to the instance.
reLocality :: Def.EnvStack -> Def.Locality -> T.VariableF a -> Context Def.Locality
reLocality envStack ogLocality = \case
  v@(T.DefinedClassFunction _ classInstID) -> do
    (ivfn, _) <- selectInstance classInstID

    let vfn = Common.instanceToFunction ivfn
    let (T.EnvDef _ _ instEnvStack) = vfn.functionDeclaration.functionEnv
    let newLoc = if envStack == instEnvStack then Local else FromEnvironment (Def.envStackToLevel instEnvStack)
    pf "NEW LOCALITY % (% =?= %) OF VAR (miau)" (pp newLoc) (pp instEnvStack) (pp envStack)
    pure newLoc


  _ -> pure ogLocality


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
      mdc <- constructor dc undefined
      margs <- sequenceA args
      pure $ CaseConstructor mdc margs



variable :: T.VariableF (Type IM) -> Context IM.Variable  -- NOTE: we're taking in both types, because we need to know which TVars were mapped to types and which to other tvars.
variable (T.DefinedVariable uv) = pure $ IM.DefinedVariable uv
variable (T.DefinedFunction vfn match) = do
  mfn <- mFunction match vfn
  pure $ IM.DefinedFunction mfn

variable v@(T.DefinedClassFunction cfd classInstID) = do
  pf "VARIABLE: %" (pp v)

  fn <- selectInstance' classInstID
  pure $ IM.DefinedFunction fn


-- Since instances should effectively act the same as functions, I need to ensure the code is the same to not intrudoce any bugs.
mFunction :: T.MatchF (Type IM) -> Function T -> Context (Function IM)
mFunction match vfn = do
  pf "mFunction"
  -- creates a type mapping for this function.
  typemap <- mkTypeMap vfn.functionDeclaration.functionOther.functionScheme match

  withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map, because it can also call other functions, so each env might have different types though albeit
    --  doc/compiler/why-monomorphize-env-types-for-memo
    menv <- mEnvTypes vfn.functionDeclaration.functionEnv
    pf "IM Env Types: %" (pp menv)

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, match, menv) $ \(tfn, _, _) addMemo -> mdo
      uv <- newUniqueVar tfn.functionDeclaration.functionId
      pf "VARIABLE OF MEMO: %" (pp uv)

      params <- traverse (bitraverse mDecon mType) tfn.functionDeclaration.functionParameters
      ret <- mType tfn.functionDeclaration.functionReturnType
      let fundec = FD env uv params ret (IM.FunOther { IM.envInstantiations = envInsts, IM.functionAnnotations = vfn.functionDeclaration.functionOther.functionAnnotations }) :: FunDec IM


      -- DEBUG: when in the process of memoization, show dis.
      -- pf "Decl: % -> %" (Def.encloseSepBy "(" ")" ", " $ pp <$> ts) (pp ret)
      -- pf "M %: %" dbgFunctionTypeName (pp fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = Function { functionDeclaration = fundec, functionBody = body } :: Function IM
      addMemo fn
      ((body, envInsts), env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        stmts <- mBody (pp fundec.functionId) tfn.functionBody

        thisFunctionsEnvInsts <- State.gets envInstantiations
        pure (stmts, thisFunctionsEnvInsts)

      pure fn

    -- complete the environment with instantiations from this variable.
    let thisFunsEnvInsts = fn.functionDeclaration.functionOther.envInstantiations
    State.modify $ \c -> c
      { envInstantiations = Map.unionWith (<>) thisFunsEnvInsts c.envInstantiations
      }

    -- NOTE: moved outside of memoization, because we depend on these "registrations" to tell us which environments need to actually be memoized.
    --       this is bad btw, but that's how it currently works. see [doc/compiler/new-expansion-scheme]
    registerEnvMono (Just fn) (T.envDefID vfn.functionDeclaration.functionEnv) fn.functionDeclaration.functionEnv mempty
    pf "REGISTERED FUNCTION % (env: %) with ENV INSTANTIATIONS: %" (pp fn.functionDeclaration.functionId) (pp $ IM.envDefID fn.functionDeclaration.functionEnv) (pp fn.functionDeclaration.functionOther)
    pure fn


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


selectInstance' :: Def.ClassInstID -> Context (Function IM)
selectInstance' cid = do
  (ifn, match) <- selectInstance cid
  let tfn = Common.instanceToFunction ifn
  fn <- mFunction match tfn
  pure fn

selectInstance :: Def.ClassInstID -> Context (InstFun T, T.MatchF (Type IM))
selectInstance classInstID = do
  -- get instance from typing context, profit.
  error "todo"
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
    pf "% level VAR: %" dbgName (pp v)
    _ <- variable =<< traverse mType v
    pure ()


  -- then actually do the scope thing.
  traverse mAnnStmt body


findUsedVarsInFunction :: Foldable t => t (AnnStmt T) -> Set (T.Variable, Type T)
findUsedVarsInFunction = foldMap $ cata $ \(O (O (Annotated _ (Located _ stmt)))) -> case first findUsedVarsInExpr stmt of
  Return expr -> findUsedVarsInExpr expr
  s -> bifold s


-- Registers a single environment monomorphization. later used to track which environments monomoprhised to what.
-- TODO: seems to be unneeded now.
registerEnvMono :: Maybe (Function IM) -> Def.EnvID -> IM.EnvDef -> Set (Def.UniqueVar, Type IM, Set (TVar T)) -> Context ()
registerEnvMono mvar oldEID nuEnv _ | null (ftvButIgnoreUnionsInEnv nuEnv) = do
  let envuse = IM.EnvUses $ Map.singleton nuEnv (maybe mempty Set.singleton mvar)
  State.modify $ \mctx -> mctx { envInstantiations = Map.insertWith (<>) (IM.envDefID nuEnv) envuse (Map.insertWith (<>) oldEID envuse mctx.envInstantiations) }

-- CHECK:
-- ignore when the environment has TVars...???? i guess... it shouldn't happen anyway, right?
registerEnvMono _ _ _ _ = pure ()



constructor :: DataCon T -> MatchF (Type IM) -> Context (DataCon IM)
constructor tdc@(DC dd@(DD ut scheme _ _) _ _ _) match = do
  -- munions <- for tunions $ \(u, params, ret) -> do  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
  --   mparams <- traverse mType params
  --   mret    <- mType ret
  --   maybeEmptyUnion <- hideEmptyUnions u
  --   munion <- for maybeEmptyUnion $ \mu -> mUnion (mu, mparams, mret)
  --   pure (munion, mparams, mret)  
  -- -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  tm <- mkTypeMap scheme match
  (_, dcQuery) <- mDataDef (dd, match)
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
  go = thisAnd (countUp' mTypeNum) . \case
    TCon dd pts tunions -> do
      params <- sequenceA pts
      let knockoffMatch = T.Match params tunions []

      tm <- mkTypeMap dd.ddScheme knockoffMatch
      munions <- withTypeMap tm $ traverse mUnion tunions  -- TODO NEW WTF: basically, maybe we should get a match for datatypes instead of those parameters?

      -- pf "Type shit: % % %" (ppDef dd) params munions
      (mdd, _) <- mDataDef (dd, knockoffMatch)
      let mt = Fix $ TCon mdd params munions
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
hideEmptyUnions :: T.EnvUnionF a -> Context (Maybe (T.EnvUnionF a))
hideEmptyUnions u = do
  TypeMap _ mus _ <- State.gets tvarMap
  if Map.member u.unionID mus || not (T.isUnionEmpty u)
    then do
      -- params' <- traverse mType params
      -- ret' <- mType ret
      pure $ Just (u)
    else pure Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (DataDef T, MatchF (Type IM)) -> Context (DataDef IM, Map (DataCon T) (DataCon IM))
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(tdd@(DD ut scheme@(T.Scheme tvs unions _) tdcs ann), match) addMemo -> do
  tm <- mkTypeMap scheme match
  withTypeMap tm $ mdo

    pf "OLD TYPE: %" ut

    nut <- newUniqueType ut
    pf "NEW TYPE: %" nut

    let mts = tvs <&> \tv -> tm.tmTVarMap ! tv
    let mdd = DD nut (IM.OtherDD mts tdd) mdcs ann
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
                TCon _ ts fnUnions -> fold ts <> foldMap isUnionEmpty fnUnions
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



retrieveTV :: TVar T -> Context (Type IM)
retrieveTV tv = do
  TypeMap typeMap _ _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error happens) when an environment is outside of its scope.
    Nothing ->
      Fix $ TO $ IM.TVar $ IM.TV { IM.fromTV = tv.fromTV, IM.binding = tv.binding }



withTypeMap :: TypeMap -> Context a -> Context a
withTypeMap tm a = do
  pf "withTypeMap"
  -- DEBUG: check typemap.
  -- pf "Type map:"
  -- pc $ ppTypeMap tm

  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- State.withStateT (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify $ \s -> s { tvarMap = ogTM }

  pure x


mUnion :: T.EnvUnion -> Context IM.EnvUnion
mUnion tunionUID = thisAnd (countUp' mUnionNum) $ do
  pf "mUnion"
  tc <- State.gets typingContext
  let tu = tc ^. globalTypeUni
      tunion = snd $ TC.getUnionFromUni tu tunionUID

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  unionmap <- State.gets $ tmUnionMap . tvarMap
  pf "test: %" $ isJust $ unionmap !? tunion.unionID
  pf "after unionmap"
  case unionmap !? tunion.unionID of
    Just mru -> do
      pf "aaaa"
      pure mru
    Nothing -> do
      pf "nothing"
      mUnionWithoutTopMap tunionUID

-- for fixpoint shit
mUnionWithoutTopMap :: T.EnvUnion -> Context IM.EnvUnion
mUnionWithoutTopMap tunionUID = thisAnd (countUp' mUnionNum) $ do
      pf "mUnionWithoutTopMap"
      tc <- State.gets typingContext
      let tu = tc ^. globalTypeUni
      let tunion = snd $ TC.getUnionFromUni tu tunionUID

      -- this adds instantiations from this specific union instantiation to cucked unions.
      let addCuckedUnionEnvs :: T.EnvUnionF (Type T) -> IM.EnvUnion -> Context ()
          addCuckedUnionEnvs tuni cuckuni = do
            envs <- traverse unionMemberToEnv' tuni.union
            let instantiatedEnvs = Set.fromList $ filter (null . foldMap ftvButIgnoreUnions) envs
            State.modify $ \c -> c { cuckedUnionInstantiation = Map.insertWith (<>) cuckuni instantiatedEnvs c.cuckedUnionInstantiation }

      -- check if we previously encountered this environment and it contained TVars that weren't mapped.
      cuckedMemo <- State.gets cuckedUnions
      case isMemoed tunion.unionID cuckedMemo of
        Just mu -> do
          addCuckedUnionEnvs tunion mu
          pure mu

        Nothing -> do
          -- it wasn't... but it's still possible for the union to be cucked.
          tunion' <- traverse mType tunion
          let unionFTV = foldMap ftvButIgnoreUnions tunion'
          if not (null unionFTV)
            then do
              -- had TVars -> remember it.
              ieu <- memo' cuckedUnions (\mem mctx -> mctx { cuckedUnions = mem }) tunion'.unionID $ \eid _ -> do
                menvs <- traverse unionMemberToEnv tunion'.union
                case menvs of
                  -- literally impossible as there would be no FTVs otherwise...
                  [] -> error $ Def.pf "[COMPILER ERROR]: Encountered an empty union (ID: %) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ IM.EnvUnion { IM.unionID = eid, IM.union = e :| es, IM.oldUnion = tunion }

              addCuckedUnionEnvs tunion ieu
              pure ieu

            else
              -- normal union - all TVars mapped. safe to memoize.
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) tunion' $ \tunion'' _ -> do
                menvs <- traverse unionMemberToEnv tunion''.union

                case menvs of
                  [] -> error $ Def.pf "[COMPILER ERROR]: Encountered an empty union (ID: %) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    nuid <- newUnionID
                    -- pf "NEW NORMAL UNION: % % % => %" tunion'' params ret nuid
                    pure $ IM.EnvUnion { IM.unionID = nuid, IM.union = e :| es, IM.oldUnion = tunion }

unionMemberToEnv' :: T.UnionMemberF (Type T) -> Context (T.EnvDefF (Type IM))
unionMemberToEnv' = unionMemberToEnv <=< traverse mType

unionMemberToEnv :: T.UnionMemberF (Type IM) -> Context (T.EnvDefF (Type IM))
unionMemberToEnv = \case
  T.UnionFun fn match -> do
    let scheme = fn.functionDeclaration.functionOther.functionScheme
    tm <- mkTypeMap scheme match
    withTypeMap tm $ do
      traverse mType fn.functionDeclaration.functionEnv
  T.UnionLam env -> pure env
  T.UnionConEnv eid ->
    pure $ T.EnvDef eid [] []


mEnvTypes :: T.EnvDefF (Type T) -> Context IM.EnvTypes
mEnvTypes env = do
  menv <- traverse mType env
  pure $ case menv of
    T.EnvDef eid params _ -> do
      IM.EnvTypes eid $ params <&> \(_, _, t) -> t

    -- T.RecursiveEnv _ _ -> error "I think recursive env cannot be monomorphised."



------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , tvarInsts :: Map (TVar T) (Map (ClassDef T) (InstDef T))  -- TODO: smell.
  , memoFunction :: Memo (Function T, MatchF (Type IM), IM.EnvTypes) (Function IM)
  , memoDatatype :: Memo (DataDef T, MatchF (Type IM)) (DataDef IM, Map (DataCon T) (DataCon IM))
  , memoEnv :: Memo (T.EnvDefF (Type IM)) IM.EnvDef
  , memoUnion :: Memo (T.EnvUnionF (Type IM)) IM.EnvUnion
  , memoMember :: Memo (DataDef IM, Def.MemName) Def.UniqueMem

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo Def.UnionID IM.EnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  , cuckedUnionInstantiation :: Map IM.EnvUnion (Set (T.EnvDefF (Type IM)))  -- (NOTE: THIS IS ACTUALLY USED AT THE END. LSP CAN'T COMPREHEND OVERLOADED RECORD DOTS) this one is to track all environments which get instantiated for this union. (not sure if it's still needed if we pre-search variables in body anyway.)
  -- also, this can be done in the same way as subst - would even require us to track less state.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: IM.EnvInstantiations  -- NOTE: FUTURE TYPECHECK
  -- i think it's also not needed now.

  , currentEnvStack :: Def.EnvStack -- HACK: it's for knowing when instances should be local or not. (TC ENV STACK, NOT THE NEW IDs)
  , lastEnvironment :: [(IM.Variable, Type IM)]  -- HACK: for knowing which variable should envmod use.

  , completedEnvs :: Set IM.EnvDef
  , environmentsLeft :: Map IM.EnvDef [Function IM]

  -- Should be Reader, but for now it's state.
  , typingContext :: TC.TypingContext
  }
type Context = StateT Context' BaseCtx

startingContext :: TC.TypingContext -> Context'
startingContext tc = Context
  { tvarMap = mempty
  , tvarInsts = mempty
  , memoFunction = emptyMemo
  , memoDatatype = emptyMemo
  , memoEnv = emptyMemo
  , memoUnion = emptyMemo
  , memoMember = emptyMemo

  , cuckedUnions = emptyMemo
  , cuckedUnionInstantiation = mempty
  , envInstantiations = mempty

  , currentEnvStack = mempty
  , lastEnvironment = mempty

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

-- fix for fixIO shit.
data FixFix m a
  = FixEval a
  | FixLazy (m a)


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


mkTypeMap :: T.Scheme T -> T.MatchF (Type IM) -> Context TypeMap
mkTypeMap (T.Scheme sTVs suUnions suAssocs) (T.Match mTVs muUnions muAssocs) = mdo
  pf "what"
  tc <- State.gets typingContext
  let tu = tc ^. globalTypeUni
  let sUnions = T.unionID . snd . TC.getUnionFromUni tu <$> suUnions
  let sAssocs = suAssocs <&> \(T.FunctionTypeAssociation _ _ _ classInstID) -> classInstID

  pf "tm"
  let tm = TypeMap
        { tmTVarMap  = Map.fromList $ zip sTVs mTVs
        , tmUnionMap = Map.fromList $ zip' sUnions mUnions
        , tmAssocMap = Map.fromList $ zip' sAssocs mAssocs
        }

  -- NEW TODO: we don't need fixIO with union maps. union maps cannot be recursive, so if we know the order of type maps, we need to order them appropriately.
  -- or do we? what about instances?
  -- right now, I assume, that all will be okay, and they get properly memoed, which I will later retrieve in mUnions.

  pf "before tm"
  (mUnions, mAssocs) <- withTypeMap tm $ do  -- not sure I need back references here? the thing is, it probably does not matter where it will get evaluated. but just in case?
    mmUnions <- traverse mUnionWithoutTopMap muUnions
    mmAssocs <- traverse selectInstance' muAssocs
    pure (mmUnions, mmAssocs)

  pf "after tm"
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


withEnvContext :: Map (T.EnvDefF (Type IM)) IM.EnvDef -> IM.EnvInstantiations -> Map IM.EnvUnion (Set (T.EnvDefF (Type IM))) -> EnvContext a -> BaseCtx (a)
withEnvContext menvs allInstantiations cuckedUnionInstantiations x = do
  (m, _, ()) <- RWS.runRWST x envUse envMemo
  pure m
  where
    envUse = EnvContextUse
      { allInsts = allInstantiations
      , envs = menvs
      , cuckedUnionInsts = cuckedUnionInstantiations
      }

    envMemo = EnvMemo
      { memoIDatatype = emptyMemo
      , memoIFunction = emptyMemo
      , memoIUnion = emptyMemo
      }


mfAnnStmts :: [AnnStmt IM] -> EnvContext [AnnStmt M]
mfAnnStmts stmts = fmap catMaybes $ for stmts $ cata $ \(O (O (Annotated anns (Located location stmt)))) -> do
  countUp' mfStmtNum
  stmt' <- bitraverse mfExpr id stmt
  let s = pure . Just
  let
    body :: NonEmpty (Maybe (AnnStmt M)) -> NonEmpty (AnnStmt M)
    body bstmts =
      let eliminated = catMaybes $ NonEmpty.toList bstmts
      in case eliminated of
        [] -> Fix (O $ O (Annotated [] (Located location Pass))) :| []
        (st:sts) -> st :| sts

  fmap (embed . O . O . Annotated anns . Located location) <$> case stmt' of
    Fun (IM.EnvInsts envs) -> do
      mfenvs <- traverse (bitraverse mfEnvMod mfEnvDef) envs
      s $ Fun $ M.EnvDefs $ NonEmpty.toList mfenvs

    Pass -> s Pass
    ExprStmt e -> s $ ExprStmt e
    Assignment vid varLocation expr -> s $ Assignment vid varLocation expr
    Print e -> s $ Print e
    Mutation vid varLocation loc accesses e -> do
      mfaccesses <- traverse (bitraverse (pure . \case { MutRef location -> MutRef location; MutField location um -> MutField location um }) mfType) accesses  -- noop access reconstruction...
      s $ Mutation vid varLocation loc mfaccesses e
    If (IfStmt { condition,  ifTrue,  ifElifs,  ifElse }) -> s $ If $ IfStmt condition (body ifTrue) (fmap2 body ifElifs) (body <$> ifElse)
    Switch e cases -> fmap (Just . Switch e) $ for cases $ \kase -> do
      mdecon <- mfDecon kase.deconstruction
      pure $ Case { deconstruction = mdecon, caseCondition = kase.caseCondition, caseBody = body kase.caseBody }
    Return e -> do
      me <- mfExpr e
      s $ Return me
    While cond bod -> do
      s $ While cond (body bod)

    Other _ -> undefined
    Inst _ -> undefined  -- TODO: remove from Common later.

mfDecon :: Decon IM -> EnvContext (Decon M)
mfDecon = cata $ \(N t e) -> do
  mt <- mfType t
  fmap (embed . N mt) $ case e of
    CaseIgnore -> pure CaseIgnore
    CaseVariable v -> do
      pure $ CaseVariable v

    CaseRecord _ decons -> do
      -- fun unsafe shit.
      let dd = case project mt of
            TCon mdd _ _ -> mdd
            mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

      decons' <- for decons $ \(um, decon) -> do
        mdecon <- decon
        pure (um, mdecon)
      pure $ CaseRecord dd decons'

    CaseConstructor dc decons -> do
      mdc <- mfConstructor dc t
      mdecons <- sequenceA decons
      pure $ CaseConstructor mdc mdecons


mfExpr :: Expr IM -> EnvContext (Expr M)
mfExpr = cata $ \(N imt imexpr) -> thisAnd (countUp' mfExprNum) $ do
  mt <- mfType imt
  fmap (embed . N mt) $ case imexpr of
    Var v loc -> do
      mv <- mfVariable v
      pure $ Var mv loc

    Lam env args ret -> do
      margs <- traverse2 mfType args
      menv <- mfEnv' env
      mret <- ret
      pure $ Lam menv margs mret

    Con con _ -> Con <$> mfConstructor con imt <*> pure ()

    RecCon _ insts -> do
      let dd = expectDataDef mt
      insts' <- sequenceA2 insts
      pure $ RecCon dd insts'

    RecUpdate e upd -> do
      let dd = expectDataDef mt
      me <- e
      upd' <- sequenceA2 upd
      pure $ RecUpdate me upd'

    MemAccess e um -> do
      mfe <- e
      pure $ MemAccess mfe um

    Lit lt -> pure $ Lit $ Common.relit id lt

    BinOp l op r -> BinOp <$> l <*> pure op <*> r
    UnOp op x -> UnOp op <$> x
    Call c args -> Call <$> c <*> sequenceA args
    As e t -> As <$> e <*> mfType t

mfVariable :: IM.Variable -> EnvContext M.Variable
mfVariable = \case
  IM.DefinedVariable uv -> pure $ M.DefinedVariable uv
  IM.DefinedFunction fun -> do
    mfun <- mfFunction fun
    pure $ M.DefinedFunction mfun


mfEnvDef :: IM.EnvInst -> EnvContext M.EnvDef
mfEnvDef (IM.EnvInst { envDef = fn, notYetInstantiated = notInstFuns }) = do
    env' <- mfFunction fn
    mNotInstFuns <- traverse mfFunction notInstFuns
    pure $ M.EnvDef { envDef = env', notYetInstantiated = mNotInstFuns } -- M.Env eid menvContent
mfEnvDef _ = error "RECURSIVE ENV"

mfEnv' :: IM.EnvDef -> EnvContext M.Env
mfEnv' = \case
  IM.EnvDef eid vars _ -> do
    menvContent <- traverse (\(v, l, t) -> mfType t >>= \t' -> (,l,t') <$> mfVariable v) vars  -- the weird monad shit is so we 
    pure $ M.Env eid menvContent
  -- IM.RecursiveEnv eid isEmpty ->
  --   pure $ M.RecursiveEnv eid isEmpty

mfEnvMod :: IM.EnvMod -> EnvContext M.EnvMod
mfEnvMod IM.EnvMod { IM.assigned = e, IM.assignee = fn } =
  M.EnvMod <$> mfEnvAssign e <*> mfFunction fn

mfEnvAssign :: IM.EnvAssign -> EnvContext M.EnvAssign
mfEnvAssign = \case
  IM.LocalEnv e -> M.LocalEnv <$> mfEnv' e
  IM.EnvFromEnv accesses -> fmap M.EnvFromEnv $ for accesses $ \access -> do
    maccess <- traverse (bitraverse mfFunction mfType) access.access
    maccessedEnv <- mfEnv' access.accessedEnv
    pure $ M.EnvAccess { access = maccess, accessedEnv = maccessedEnv }

mfEnv :: T.EnvDefF (Type IM) -> EnvContext (Maybe M.Env)
-- mfEnv (T.RecursiveEnv {}) = error "RECURSION. This, with the weird monad shit makes us crash at recursion."
mfEnv env = do
  findEnvs <- RWS.asks envs
  traverse mfEnv' $ findEnvs !? env


mfType :: Type IM -> EnvContext (Type M)
mfType = para $ fmap embed . thisAnd (countUp' mfTypeNum) .  \case
  TCon dd ts unions -> do
    munions <- traverse mfUnion unions
    mts <- traverse snd ts
    mdd <- fst <$> mfDataDef (dd, munions)
    pure $ TCon mdd mts munions

  TFun union args (_, ret) -> do
    munion <- mfUnion union
    margs <- traverse snd args
    mret <- ret
    pure $ TFun munion margs mret

  TO (IM.TVar tv) -> error $ pf "[COMPILER ERROR]: TVar % not matched - types not appied correctly?" (pp tv)



mfUnion :: IM.EnvUnion -> EnvContext M.EnvUnion
mfUnion = memo memoIUnion (\mem s -> s { memoIUnion = mem }) $ \union _ -> thisAnd (countUp' mfUnionNum) $ do
  cuckedUnions <- RWS.asks cuckedUnionInsts
  mappedEnvs <- case cuckedUnions !? union of
      -- here should be no ftvs.
      Nothing -> fmap (nub . concat) $ for (NonEmpty.toList union.union) $ \env -> do  -- NOTE: `nub` added, because at some point it seems like i removed duplicate removal.
          pf "???: % ?? %" (pp env) (null (foldMap ftvButIgnoreUnions env))
          menv <- mfEnv env
          pf "NOFTV: % => %" (pp env) (maybe "???" pp menv)
          pure $ maybeToList menv

      -- here should also be no ftvs in the NEW UNION
      -- these were cuckedUnions
      Just envs -> do
        -- NOTE: i did catMaybes because mfEnv returns this. I don't think it's necessary anymore.
        menvs <- fmap catMaybes $ traverse mfEnv $ Set.toList envs
        pure menvs

  -- NOTE: I HATE THIS FUCKING ERROR LIKE YOU WOULDN'T BELIEVE.
  pf "mfUnion: % => %" (pp union) (Def.encloseSepBy "{" "}" ", " $ pp <$> mappedEnvs)
  let mUsedEnvs = case mappedEnvs of
        [] ->
          error $ pf "[COMPILER ERROR] Empty union (%) encountered... wut!??!??!?!? Woah.1>!>!>!>!>>!\n% 8====> %" union.unionID union mappedEnvs
        (x:xs) -> x :| xs

  pure $ M.EnvUnion { M.unionID = union.unionID, M.union = mUsedEnvs }



mfDataDef :: (DataDef IM, [M.EnvUnion]) -> EnvContext (DataDef M, Map (DataCon IM) (DataCon M))
mfDataDef = memo memoIDatatype (\mem s -> s { memoIDatatype = mem }) $ \(idd, _) addMemo -> mdo
  mfAppliedTypes <- traverse mfType idd.ddScheme.appliedTypes
  let dd = DD idd.ddName (M.OtherDD mfAppliedTypes) cons idd.ddAnns
  addMemo (dd, dcQuery)

  cons <- case idd.ddCons of
    Right mcons -> fmap Right $ for mcons $ \(DC _ uc imts ann) -> do
      mts <- traverse mfType imts
      pure $ DC dd uc mts ann

    Left mrecs -> fmap Left $ for mrecs $ \(Annotated ann (um, t)) -> do
      mt <- mfType t
      pure $ Annotated ann (um, mt)

  let dcQuery = Map.fromList $ case (idd.ddCons, cons) of
        (Right ttdcs, Right mmdcs) -> zip ttdcs mmdcs
        (Left _, Left _) -> mempty
        _ -> error "caulk."  -- does not have to be very safe/sane - controlled environment.
  pure (dd, dcQuery)



mfFunction :: Function IM -> EnvContext (Function M)
mfFunction = memo memoIFunction (\mem s -> s { memoIFunction = mem }) $ \fun _ -> do  -- maybe we should addMemo earlier?
  pf "MF function %" (pp fun.functionDeclaration.functionId)
  pc fun
  -- 
  -- just map everything.
  let fundec = fun.functionDeclaration
  env <- mfEnv' fundec.functionEnv
  params <- traverse (bitraverse mfDecon mfType) fundec.functionParameters
  ret <- mfType fundec.functionReturnType

  let mfundec = FD { functionEnv = env, functionId = fundec.functionId, functionParameters = params, functionReturnType = ret, functionOther = fundec.functionOther.functionAnnotations }

  body <- mfAnnStmts $ NonEmpty.toList fun.functionBody
  let completedBody = case body of
        [] ->
          -- TODO: we need to automatically insert return values based on flow analysis (but that should be part of typechecking?)
          let pass = Fix (O (O (Annotated [] (Located (error "what should I insert here?") Pass))))
          in pass :| []

        (s:ss) -> s :| ss

  pure $ Function { functionDeclaration = mfundec, functionBody = completedBody }



mfConstructor :: DataCon IM -> Type IM -> EnvContext (DataCon M)
mfConstructor dc@(DC dd _ _ _) imt = do
  -- Extract type. Pretty bad, but should just work.
  let imunions = case project imt of
        TCon _ _ unions -> unions
        TFun _ _ (Fix (TCon _ _ unions)) -> unions

        -- COMPILER ERROR
        _ -> error $ Def.pf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%)." (pp imt)

  -- mtypes <- traverse mfType ttypes
  munions <- traverse mfUnion imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  pure mdc



ftvButIgnoreUnionsInEnv :: IM.EnvDef -> Set IM.TVar
ftvButIgnoreUnionsInEnv (IM.EnvDef _ vs _) = (foldMap . foldMap) ftvButIgnoreUnions vs

ftvButIgnoreUnions :: Type IM -> Set IM.TVar
ftvButIgnoreUnions = cata $ \case
  TO (IM.TVar tv) -> Set.singleton tv
  TCon _ ts _ -> mconcat ts
  TFun _ args ret -> mconcat args <> ret


expectIDataDef :: Type IM -> DataDef IM
expectIDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

expectDataDef :: Type M -> DataDef M
expectDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.pf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))



-------------------------
-- Step 2 Type defs!
------------------------


type EnvContext = RWST EnvContextUse () EnvMemo BaseCtx -- TEMP: PrintContext temporarily for debugging. should not be used for anything else.
-- Stores environment instantiations. 
--   NOTE: In the future, maybe more stuff (like which constructors were used!)
data EnvContextUse = EnvContextUse
  { allInsts :: IM.EnvInstantiations
  , envs     :: Map (T.EnvDefF (Type IM)) IM.EnvDef
  , cuckedUnionInsts :: Map IM.EnvUnion (Set (T.EnvDefF (Type IM)))
  }


data EnvMemo = EnvMemo
  { memoIDatatype :: Memo (DataDef IM, [M.EnvUnion]) (DataDef M, Map (DataCon IM) (DataCon M))
  , memoIFunction :: Memo (Function IM) (Function M)
  , memoIUnion    :: Memo IM.EnvUnion M.EnvUnion
  }




----------------------
-- UNRELATED MISC
----------------------

instance Foldable ((,,) a b) where
  foldr f x (_, _, y) = f y x

instance Traversable ((,,) a b) where
  traverse f (a, b, x) = (a, b,) <$> f x


mustSelectInstance :: Type IM -> T.PossibleInstances T -> InstDef T
mustSelectInstance (Fix (TCon mdd _ _)) insts =
  case insts !? mdd.ddScheme.ogDataDef of
    Just instdef -> instdef
    Nothing -> error $ Def.pf "INSTANCE FOR % DOES NOT EXIST." (ppDef mdd)
mustSelectInstance _ _ = error "TRYING TO SELECT AN INSTANCE FOR A FUNCTION."


-- I think there was an actual function that did this kek.
{-# inline thisAnd #-}
thisAnd :: Monad m => m () -> m a -> m a
thisAnd f g = do
  x <- g
  f
  pure x

mUpExpr, mUpStmt, mUpType, mUpUnion :: Context ()
mUpExpr = countUp' undefined
mUpStmt = undefined
mUpType = undefined
mUpUnion = undefined
