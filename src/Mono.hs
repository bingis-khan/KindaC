{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- we implement basic instances (Foldable, Travesable) for Tuple.

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}  -- for HLINT kekek
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant pure" #-}  -- this is retarded. it sometimes increases readability with that extra pure.
{-# LANGUAGE NamedFieldPuns #-}
module Mono (mono) where

import qualified AST.Typed as T
import qualified AST.Mono as M
import qualified AST.Common as Common
import Data.Fix (Fix(..))
import Data.Functor.Foldable (embed, cata, para, project)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first, bimap)
import Data.List.NonEmpty (NonEmpty (..), (<|))
import Data.Map.Strict (Map, (!?), (!))
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (fold, for_)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe, fromJust, maybeToList, fromMaybe)
import Data.Set (Set)
import Misc.Memo (Memo (..), emptyMemo, memo, memo', isMemoed)
import qualified Misc.Memo as Memo
import Data.Monoid (Any (Any, getAny))
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Bifoldable (bifold)
import Control.Monad (void)
import Data.String (fromString)
import Data.List (find, partition)
import AST.Typed (TC)
import AST.Common (AnnStmt, Module, StmtF (..), Expr, ExprNode (..), ExprF (..), Function (..), TypeF (..), ClassFunDec (..), Type, CaseF (..), Case, Decon, DeconF (..), FunDec (..), TVar (..), DataDef (..), DataCon (..), ClassDef, InstDef, IfStmt (..), instFunDec, InstFun, MutAccess (..), XMutAccess, LitType (..), askNode)
import AST.Mono (M)
import AST.IncompleteMono (IM)
import AST.Def ((:.) (..), Annotated (..), Locality (..), phase, PP (..), fmap2, PPDef (..), traverse2, sequenceA2, (<+>), Located (..), PrintContext, pf, pc)
import qualified AST.IncompleteMono as IM
import qualified AST.Def as Def
import Data.List (nubBy)
import Control.Applicative (liftA3)




------ Monomorphization consists of two steps:
--  Step 1: Perform normal monomorphization (however, you won't be able to compile escaped TVars).
--  Step 2: Replace escaped TVars with each instantiation of them. (maybe it can be eliminated like doing env defs by first collecting the variables)

mono :: [AnnStmt TC] -> PrintContext (Module M)
mono tmod = {-# SCC mono #-} do
  -- Step 1: Just do monomorphization with a few quirks*.
  (mistmts, monoCtx) <- flip State.runStateT startingContext $ do
    mBody "[top level]" tmod

  let imEnvs = Map.mapKeys (fmap snd) $ memoToMap monoCtx.memoEnv

  phase "Monomorphisation (env instantiations)"
  pc $ (Def.ppMap . fmap (bimap pp (Def.encloseSepBy "[" "]" ", " . fmap (\(e, fns) -> pf "%: %" e (ppDef fns) :: Def.Context) . Map.toList . IM.fromEnvUses)) . Map.toList) monoCtx.envInstantiations

  phase "Monomorphisation (just envs)"
  pc $ (Def.ppMap . fmap (bimap pp pp) . Map.toList) imEnvs

  phase "Monomorphisation (first part)"
  pc $ Def.ppLines mistmts


  -- Step 2 consists of:
  -- 1. substitute environments

  mmod <- withEnvContext imEnvs monoCtx.envInstantiations monoCtx.cuckedUnionInstantiation $ do
    mstmts <- mfAnnStmts mistmts
    pure $ M.Mod { M.topLevelStatements = mstmts }

  pure mmod



mAnnStmt :: AnnStmt TC -> Context (AnnStmt IM)
mAnnStmt = cata (fmap embed . f) where
  f :: (:.) ((:.) Annotated Located) (StmtF TC (Expr TC)) (Context (AnnStmt IM)) -> Context ((:.) ((:.) Annotated Located) ((StmtF IM (Expr IM))) (AnnStmt IM))
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
        let envID = T.envID env
        envInsts <- State.gets envInstantiations

        let currentEnvUses = fromMaybe mempty $ envInsts !? envID
        let envUses = foldMap Set.toList $ IM.fromEnvUses currentEnvUses -- <&> \(IM.EnvUse (Just fn) env) -> (fn, env)

        pf "ENCOUNTERED FUN %" (pp fn.functionDeclaration.functionId)
        envDefs <- orderEnvironments envUses
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ IM.EnvDefs $ x :| xs

      Inst inst -> do
        envInsts <- State.gets envInstantiations

        let envUses = flip concatMap inst.instFuns $ \fn ->
              let env = fn.instFunDec.functionEnv
                  envID = T.envID env
                  currentEnvUses = fromMaybe mempty $ envInsts !? envID
                  defs = foldMap Set.toList $ IM.fromEnvUses currentEnvUses
              in  defs

        pf "ENV INSTS: %" (pp envInsts)
        pf "ENCOUNTERED INST: %" (pp $ instFunDec <$> inst.instFuns)
        pf "INST TURNED TO: %" (pp $ functionDeclaration <$> envUses)
        envDefs <- orderEnvironments envUses
        noann $ case envDefs of
          [] -> Pass
          (x:xs) -> Fun $ IM.EnvDefs $ x :| xs

      Other () -> error "OTHER OTHER OTHER SHOULD NOT BE CREATED EVER"


mMutAccesses :: [(MutAccess TC, Type TC)] -> Context [(MutAccess IM, Type IM)]
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
orderEnvironments :: [Function IM] -> Context [Either IM.EnvMod IM.EnvDef]
orderEnvironments fns = do
  currentLevel <- State.gets $ length . currentEnvStack
  pf "CURRENT LEVEL: %" $ pp currentLevel

  let
    isFromCurrentEnv env = IM.envLevel env == currentLevel
    isFromOuterEnv env = IM.envLevel env < currentLevel

    filterOtherEnvs :: [Function IM] -> [Function IM]
    filterOtherEnvs = filter (isFromCurrentEnv . functionEnv . functionDeclaration)

    filterOuterEnvs :: [Function IM] -> [Function IM]
    filterOuterEnvs = filter (not . isFromOuterEnv . functionEnv . functionDeclaration)


    -- TODO: later, should create some custom datatypes (Env, [Function IM])
    loop :: [(Function IM, [Function IM])] -> Context [Either IM.EnvMod IM.EnvDef]
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
            pure $ fmap Right $ incomplete <&> \(e, ds) -> IM.EnvDef { envDef = e, notYetInstantiated = ds }
          else do
            setComplete $ functionEnv . functionDeclaration . fst <$> complete
            let completedStmts = complete <&> \(e, deps) -> Right $ IM.EnvDef { envDef = e, notYetInstantiated = deps }  -- NOTE: maybe we should filter out ONLY outer envs.
            envAdds <- Def.fmap2 Left completeEnvironments
            ((completedStmts <> envAdds) <>) <$> loop incomplete

    completeEnvironments :: Context [IM.EnvMod]
    completeEnvironments = do
        envsAndDependencies <- Map.toList <$> State.gets environmentsLeft
        pf "ENVS AND DEPS: %" (pp $ fmap (bimap pp (fmap (\fn -> fromString $ Def.printf "% %(%)" (pp fn.functionDeclaration.functionId) (pp $ IM.envID fn.functionDeclaration.functionEnv) (pp $ IM.envLevel fn.functionDeclaration.functionEnv) :: Def.Context))) envsAndDependencies)
        completedEnvs <- State.gets completedEnvs
        vars <- State.gets lastEnvironment
        let
          -- this is a roundabout way, because it should already be done in dependencies.
          gatherAccesses :: IM.Env -> (IM.Variable, Type IM) -> [IM.EnvAccess]
          gatherAccesses e = \case
            (IM.DefinedVariable _, _) -> []
            (IM.DefinedFunction fn, t) ->
              let currentEnv = fn.functionDeclaration.functionEnv
              in if currentEnv == e
                then [IM.EnvAccess { access = NonEmpty.singleton (fn, t), accessedEnv = e }]
                else case currentEnv of
                  IM.RecursiveEnv {} -> []
                  IM.Env _ vars _ -> 
                    concatMap (gatherAccesses e . (\(v, _, t) -> (v, t))) vars <&> \ea -> ea { IM.access = (fn, t) <| ea.access }

          -- TODO: this will be modified, as access will be represented differently.
          isFromEnv :: IM.Env -> IM.EnvAssign
          isFromEnv e =
            case concatMap (gatherAccesses e) vars of
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
setIncomplete :: [(IM.Env, [Function IM])] -> Context ()
setIncomplete envsAndDependencies = do
  -- add the incomplete environments to `environmentsLeft`
  let newEnvsLeft = Map.fromList envsAndDependencies
  State.modify $ \c -> c { environmentsLeft = newEnvsLeft <> c.environmentsLeft }


setComplete :: [IM.Env] -> Context ()
setComplete fns = State.modify $ \c -> c { completedEnvs = c.completedEnvs <> Set.fromList fns }

getEnvDependencies :: IM.Env -> [Function IM]
getEnvDependencies (IM.Env _ vars _) = mapMaybe (\(v, _, _) -> case v of { IM.DefinedFunction fn -> Just fn; _ -> Nothing }) vars
getEnvDependencies _ = error "RECURSIVE ENV WHAT."


mExpr :: Expr TC -> Context (Expr IM)
mExpr = cata $ fmap embed . \(N en expr) -> do
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
          mv <- variable v mt

          envStack <- State.gets currentEnvStack
          newLocality <- reLocality envStack locality v

          pure $ Var mv newLocality

        Con c eid -> do
          mc <- constructor c en.t

          -- don't forget to register usage. (for codegen)
          void $ withEnv Nothing (T.Env eid [] mempty []) $ pure ()

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

withEnv :: Maybe (Function IM) -> T.Env -> Context a -> Context (a, IM.Env)
withEnv mfn env cx = do
  itenv <- traverse (\t -> (t,) <$> mType t) env  -- NOTE: We need to differentiate envs by their types. I wonder if we need the second type there?
  menv@(IM.Env _ envContent _) <- memo' memoEnv (\m c -> c { memoEnv = m }) itenv $ \env' _ -> case env' of
    T.Env _ envContent _ envStack -> do
      newEID <- newEnvID
      let envLevel = Def.envStackToLevel envStack
      menvContent <- for envContent $ \(v, l, (_, mt)) -> do
        let vv = fst <$> v
        mv <- variable vv mt

        newLocality <- reLocality envStack l vv

        pure (mv, newLocality, mt)

      pure $ IM.Env newEID menvContent envLevel  -- env IDs changed, so kind of hard to track env stack. that's why only level. might not even need this.

    T.RecursiveEnv {} -> error "SHOULD NOT HAPPEN."  -- pure $ M.IDRecursiveEnv eid isEmpty

  -- SAVE PREVIOUS STATE
  prevlev <- State.gets currentEnvStack
  prevCompleteEnvs <- State.gets completedEnvs
  prevEnvsLeft <- State.gets environmentsLeft
  lastEnv <- State.gets lastEnvironment
  usedEnvs <- State.gets envInstantiations
  cusKeys <- Map.keysSet . Memo.memoToMap <$> State.gets cuckedUnions

  -- SET NEW LOCAL STATE
  let curlev = case env of
        T.Env eid _ _ lev -> eid : lev
        _ -> undefined

  State.modify $ \c -> c
    { currentEnvStack = curlev
    , completedEnvs = mempty
    , environmentsLeft = mempty
    , lastEnvironment = envContent <&> \(v, _, t) -> (v, t)
    , envInstantiations = mempty
    }

  -- NOTE: recursively add environments all environments. (is not yet ready for recursiveness)
  let doEnvIncompletes (IM.Env _ envContent _) = concatMap ((\case { IM.DefinedFunction fn -> fn.functionDeclaration.functionEnv : doEnvIncompletes fn.functionDeclaration.functionEnv; _ -> [] }) . (\(v, _, _) -> v)) envContent
  pf "WITH ENV INCOMPLETE: %" $ pp $ doEnvIncompletes menv <&> \e -> (e, functionId . functionDeclaration <$> getEnvDependencies e)
  pf "used envs: %" (pp usedEnvs)

  setIncomplete $ (\e -> (e, filter ((== length curlev) . IM.envLevel . functionEnv . functionDeclaration) $ getEnvDependencies e)) <$> doEnvIncompletes menv
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


  pf "%M: % =WITH ENV%=> %" (pp $ T.envID env) (pp env) (case mfn of { Nothing -> "" :: Def.Context; Just fn -> fromString $ Def.printf " (%)" $ pp fn.functionDeclaration.functionId }) (pp menv)

  pure (x, menv)


-- Evaluate the locality of a class function after we have access to the instance.
reLocality :: Def.EnvStack -> Def.Locality -> T.Variable -> Context Def.Locality
reLocality envStack ogLocality = \case
  v@(T.DefinedClassFunction cfd snapshot self uci) -> do
    ivfn <- selectInstance snapshot self uci cfd

    let vfn = Common.instanceToFunction ivfn
    let (T.Env _ _ _ instEnvStack) = vfn.functionDeclaration.functionEnv
    let newLoc = if envStack == instEnvStack then Local else FromEnvironment (Def.envStackToLevel instEnvStack)
    pf "NEW LOCALITY % (% =?= %) OF VAR %" (pp newLoc) (pp instEnvStack) (pp envStack) (pp v)
    pure newLoc


  _ -> pure ogLocality


findUsedVarsInExpr :: Expr TC -> Set (T.Variable, Type TC)
findUsedVarsInExpr = cata $ \(N en expr) -> case expr of
  Var v _ -> Set.singleton (v, en.t)
  e -> fold e

mCase :: CaseF TC (Expr IM) (AnnStmt IM) -> Context (Case IM)
mCase kase = do
  decon <- mDecon kase.deconstruction
  pure $ Case decon kase.caseCondition kase.caseBody

mDecon :: Decon TC -> Context (Decon IM)
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
            mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

      margs <- for args $ \(mem, decon) -> do
        mdecon <- decon
        um <- member (dd, mem)
        pure (um, mdecon)

      pure $ CaseRecord dd margs

    CaseConstructor dc args -> do
      mdc <- constructor dc en.t
      margs <- sequenceA args
      pure $ CaseConstructor mdc margs



variable :: T.Variable -> Type IM -> Context IM.Variable  -- NOTE: we're taking in both types, because we need to know which TVars were mapped to types and which to other tvars.
variable (T.DefinedVariable uv) _ = pure $ IM.DefinedVariable uv
variable (T.DefinedFunction vfn _ _ ufi) et = do
  mfn <- mFunction (Right ufi) et vfn
  pure $ IM.DefinedFunction mfn

variable v@(T.DefinedClassFunction cfd snapshot self uci) et = do
  pf "VARIABLE: %" (pp v)
  pf "SNAPSHOT WHEN CLASS: %" $ T.dbgSnapshot snapshot

  ivfn <- selectInstance snapshot self uci cfd
  let vfn = Common.instanceToFunction ivfn
  fn <- mFunction (Left uci) et vfn
  pure $ IM.DefinedFunction fn


-- Since instances should effectively act the same as functions, I need to ensure the code is the same to not intrudoce any bugs.
mFunction :: Either Def.UniqueClassInstantiation Def.UniqueFunctionInstantiation -> Type IM -> Function TC -> Context (Function IM)
mFunction uciOrUfi et vfn = do
  let dbgFunctionTypeName = either (const "instance") (const "function") uciOrUfi

  pc $ "in " <> dbgFunctionTypeName <> ": " <> pp vfn.functionDeclaration.functionId.varName.fromVN

  -- male feminists are seething rn
  let (tts, tret, appliedAssocs, tenv) = forceFunctionType uciOrUfi et

  -- DEBUG: print a non-memoized type. This was used to check memoization errors.
  pf "Decl (nomemo): % -> %" (Def.encloseSepBy "(" ")" ", " $ pp <$> tts) (pp tret)

  let tassocs = vfn.functionDeclaration.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ t _ _) -> t
  pf "t assocs: %" $ Def.sepBy ", " $ pp <$> appliedAssocs
  massocs <- traverse mType appliedAssocs
  pf "m assocs: %" (Def.sepBy ", " $ pp <$> massocs)

  -- creates a type mapping for this function.
  let typemap
        =  mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts
        <> mapType vfn.functionDeclaration.functionReturnType tret
        <> mapTypes tassocs massocs

  withClassInstanceAssociations tenv $ withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map, because it can also call other functions, so each env might have different types though albeit
    menv <- mEnvTypes vfn.functionDeclaration.functionEnv
    pf "IM Env Types: %" (pp menv)

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv) $ \(tfn, ts, ret, _) addMemo -> mdo
      uv <- newUniqueVar tfn.functionDeclaration.functionId
      pf "VARIABLE OF MEMO: %" (pp uv)

      params <- flip zip ts <$> traverse (mDecon . fst) tfn.functionDeclaration.functionParameters
      let fundec = FD env uv params ret (IM.FunOther { IM.envInstantiations = envInsts, IM.functionAnnotations = vfn.functionDeclaration.functionOther.functionAnnotations }) :: FunDec IM


      -- DEBUG: when in the process of memoization, show dis.
      pf "Decl: % -> %" (Def.encloseSepBy "(" ")" ", " $ pp <$> ts) (pp ret)
      pf "M %: %" dbgFunctionTypeName (pp fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = Function { functionDeclaration = fundec, functionBody = body } :: Function IM
      addMemo fn
      ((body, envInsts), env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        stmts <- mBody (dbgFunctionTypeName <+> pp fundec.functionId) tfn.functionBody

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
    registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) fn.functionDeclaration.functionEnv mempty
    pf "REGISTERED FUNCTION % (env: %) with ENV INSTANTIATIONS: %" (pp fn.functionDeclaration.functionId) (pp $ IM.envID fn.functionDeclaration.functionEnv) (pp fn.functionDeclaration.functionOther)
    pure fn


type AppliedAssocs = [Type TC]
forceFunctionType :: Either Def.UniqueClassInstantiation Def.UniqueFunctionInstantiation -> Type IM -> ([Type IM], Type IM, AppliedAssocs, T.EnvF (Type TC))
forceFunctionType uciOrUfi et = case project et of
    TFun (IM.EnvUnion { IM.oldUnion = union }) mts mret ->
      let findFn = case uciOrUfi of
            Left uci -> \(muci, _, _, _) -> Just uci == muci
            Right ufi -> \(_, ufi', _, _) -> ufi == ufi'

          (_, _, appliedAssocs, tEnv) = fromJust $ find findFn $ union.union
      in (mts, mret, appliedAssocs, tEnv)

    _ -> error "NOT A FUNCTION TYPE BRUH"


selectInstance :: T.ScopeSnapshot -> Type TC -> Def.UniqueClassInstantiation -> ClassFunDec TC -> Context (InstFun TC)
selectInstance snapshot self uci cfd@(CFD cd cfdId _ _ _ _) = do
  mself <- mType self
  ucis <- State.gets classInstantiationAssociations
  pf "SNAPSHOT UCIS: %" (ppDef $ Map.keysSet <$> ucis)
  case ucis !? uci of
    Just insts -> do
      let inst = mustSelectInstance mself insts
      let instfun = fromJust $ find (\ifn -> ifn.instClassFunDec == cfd) inst.instFuns
      pure instfun

    -- we might be top level here, so we fall back to the snapshot.
    Nothing ->
      let dd = case project mself of
            TCon mdd _ _ -> mdd.ddScheme.ogDataDef
            _ -> error "WHAT THJE FUCK"
      in case snapshot !? cd >>= (!? dd) of
        Just inst ->
          let instfun = fromJust $ find (\ifn -> ifn.instClassFunDec == cfd) inst.instFuns
          in pure instfun
        Nothing -> do
          let selfTVar = case project self of
                TO (T.TVar tv) -> Just tv
                _ -> Nothing
          error $ Def.printf "SNAPSHOT %\nSNAPSHOT UCIS %\nLOOKING FOR %\nCOULD NOT FIND INSTANCE (tvar: %, uci: %, mt: %) in % (could get: (%))" (T.dbgSnapshot snapshot) (ppDef $ Map.keysSet <$> ucis) (pp dd.ddName) (pp selfTVar) (pp uci) ("<type>" :: Def.Context) (pp cfdId) (Def.ppSet pp $ Set.toList $ Map.keysSet ucis)




mBody :: Traversable f => Def.Context -> f (AnnStmt TC) -> Context (f (AnnStmt IM))
mBody dbgName body = do
  -- Collects all instantiations from the current scope and monomorphises them.
  -- This way we know how many environments we should create when we get to Inst or Fun.
  let usedVarsInCurrentScope = findUsedVarsInFunction body

  pf "% level vars: %" dbgName $ Def.ppSet (\(v, _) -> pp v) $ Set.toList usedVarsInCurrentScope
  for_ (Set.toList usedVarsInCurrentScope) $ \(v, t) -> do
    pf "% level TYPE: %" dbgName (pp t)
    mt <- mType t
    pf "% level VAR: %" dbgName (pp v)
    _ <- variable v mt
    pure ()


  -- then actually do the scope thing.
  traverse mAnnStmt body


findUsedVarsInFunction :: Foldable t => t (AnnStmt TC) -> Set (T.Variable, Type TC)
findUsedVarsInFunction = foldMap $ cata $ \(O (O (Annotated _ (Located _ stmt)))) -> case first findUsedVarsInExpr stmt of
  Return expr -> findUsedVarsInExpr expr
  s -> bifold s


-- Registers a single environment monomorphization. later used to track which environments monomoprhised to what.
-- TODO: seems to be unneeded now.
registerEnvMono :: Maybe (Function IM) -> Def.EnvID -> IM.Env -> Set (Def.UniqueVar, Type IM, Set (TVar TC)) -> Context ()
registerEnvMono mvar oldEID nuEnv _ | null (ftvButIgnoreUnionsInEnv nuEnv) = do
  let envuse = IM.EnvUses $ Map.singleton nuEnv (maybe mempty Set.singleton mvar)
  State.modify $ \mctx -> mctx { envInstantiations = Map.insertWith (<>) (IM.envID nuEnv) envuse (Map.insertWith (<>) oldEID envuse mctx.envInstantiations) }

-- CHECK:
-- ignore when the environment has TVars...???? i guess... it shouldn't happen anyway, right?
registerEnvMono _ _ _ _ = pure ()



constructor :: DataCon TC -> Type TC -> Context (DataCon IM)
constructor tdc@(DC dd@(DD ut _ _ _) _ _ _) et = do
  -- Extract type. Pretty bad, but should just work.
  let (ttypes, tunions) = case project et of
        TCon _ tts unions -> (tts, unions)
        TFun _ _ (Fix (TCon _ tts unions)) -> (tts, unions)

        -- COMPILER ERROR
        _ -> error $ Def.printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%)." (pp et)

  mtypes <- traverse mType ttypes


  munions <- for tunions $ \(u, params, ret) -> do  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
    mparams <- traverse mType params
    mret    <- mType ret
    maybeEmptyUnion <- hideEmptyUnions u
    munion <- for maybeEmptyUnion $ \mu -> mUnion (mu, mparams, mret)
    pure (munion, mparams, mret)  
  -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  let tm = typeMapFromDataDef dd mtypes $ munions <&> \(u, _, _) -> u
  (_, dcQuery) <- mDataDef (dd, tm)
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ Def.printf "[COMPILER ERROR]: Failed to query an existing constructor for type %.\n TypeMap: %\n(applied TVs: %, applied unions: %) -> (applied TVs: %, applied unions: %)" (pp ut) (ppTypeMap tm) (Def.ppSet pp ttypes) (Def.ppSet pp tunions) (Def.ppSet pp mtypes) (Def.ppSet (maybe "?" (\u -> pp u.unionID <> (Def.ppSet (pp . T.envID) . NonEmpty.toList) u.union)) (munions <&> \(u, _, _) -> u))

  pure mdc

member :: (DataDef IM, Def.MemName) -> Context Def.UniqueMem
member = memo memoMember (\mem s -> s { memoMember = mem }) $ \(_, memname) _ -> do
  -- TODO: maybe this should be the same as `constructor`, where I just mDataType and find the member?
  --  at least for consistency. also, there won't be incorrect members! but right now, I'll try like this.
  mkUniqueMember memname


mType :: Type TC -> Context (Type IM)
mType = cata $ \case
    TCon dd pts tunions -> do
      params <- sequenceA pts

      munions <- for tunions $ \(u, params, ret) -> do  -- ISSUE(unused-constructor-elimination): very hacky, but should work. I think it echoes the need for a datatype that correctly represents what we're seeing here - a possible environment definition, which might not be initialized.
        mparams <- traverse mType params
        mret    <- mType ret
        maybeEmptyUnion <- hideEmptyUnions u
        munion <- for maybeEmptyUnion $ \mu -> mUnion (mu, mparams, mret)
        pure (munion, mparams, mret)  
      -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)
      -- we need to represent this shit differently.

      let tm = typeMapFromDataDef dd params $ munions <&> \(u, _, _) -> u
      pf "Type shit: % % %" (ppDef dd) params munions
      (mdd, _) <- mDataDef (dd, tm)
      let mt = Fix $ TCon mdd params (catMaybes (munions <&> \(u, _, _) -> u))
      pure mt

    TFun union params ret -> do
      params' <- sequenceA params
      ret' <- ret
      union' <- mUnion (union, params', ret')

      pure $ Fix $ TFun union' params' ret'

    TO (T.TVar tv) -> retrieveTV tv

    TO (T.TyVar tv) -> error $ Def.printf "[COMPILER ERROR]: Encountered TyVar %." (pp tv)


-- ISSUE(unused-constructor-elimination): yeah, this is bad. we also need to remember to map the empty unions (through type map.)
hideEmptyUnions :: T.EnvUnionF a -> Context (Maybe (T.EnvUnionF a))
hideEmptyUnions u = do
  TypeMap _ mus <- State.gets tvarMap
  if Map.member u.unionID mus || not (T.isUnionEmpty u)
    then do
      -- params' <- traverse mType params
      -- ret' <- mType ret
      pure $ Just (u)
    else pure Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (DataDef TC, TypeMap) -> Context (DataDef IM, Map (DataCon TC) (DataCon IM))
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(tdd@(DD ut (T.Scheme tvs unions) tdcs ann), tm@(TypeMap tvmap unionMap)) addMemo -> withTypeMap tm $ mdo

  pf "OLD TYPE: %" ut

  nut <- newUniqueType ut
  pf "NEW TYPE: %" nut

  let mts = tvs <&> \tv -> tvmap ! tv
  let mdd = DD nut (IM.OtherDD mts tdd) mdcs ann
  addMemo (mdd, dcQuery)


  -- Strip "unused" constructors. Currently, these are constructors that contain empty unions.
  -- TEMP: This is not finished - it only cares about unions, but a more thorough solution would track which constructors of a particular type were actually used.
  -- NOTE: also, there is something to be said about eliminating non-existent members/constructors. if we only index member by offsets and don't export it, then should we honor the structure? IMO no, unless explicitly specified in an annotation or something.
  let strippedDCs = tdcs <&> filter (\(DC _ _ conTs _) ->
        let
          isUnionEmpty :: T.EnvUnionF a -> Any
          isUnionEmpty union =
            -- NOTE: we must first replace it. also, HACK: it's retarded. TODO: make it better.
            case unionMap !? union.unionID of
              Just eu -> Any $ null eu.union
              Nothing -> Any $ null union.union

          hasEmptyUnions :: Type TC -> Any
          hasEmptyUnions = cata $ \case
              TFun union ts t -> isUnionEmpty union <> foldMap hasEmptyUnions union <> fold ts <> t
              TCon _ ts fnUnions -> fold ts <> foldMap isUnionEmpty (fnUnions <&> \(u, _, _) -> u)
              t -> fold t

          dcHasEmptyUnions :: [Type TC] -> Bool
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



retrieveTV :: TVar TC -> Context (Type IM)
retrieveTV tv = do
  TypeMap typeMap _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error happens) when an environment is outside of its scope.
    Nothing ->
      Fix $ TO $ IM.TVar $ IM.TV { IM.fromTV = tv.fromTV, IM.binding = tv.binding }



withTypeMap :: TypeMap -> Context a -> Context a
withTypeMap tm a = do
  -- DEBUG: check typemap.
  pf "Type map:"
  pc $ ppTypeMap tm

  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- State.withStateT (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify $ \s -> s { tvarMap = ogTM }

  pure x


type CurrentInstances = Map Def.UniqueClassInstantiation T.PossibleInstances
withClassInstanceAssociations :: T.Env -> Context a -> Context a
withClassInstanceAssociations ci a = do
  ogTM <- State.gets classInstantiationAssociations

  -- NOTE: i have to generate mappings for *this* function and recursively..?
  --    Maybe. but what will happen if we use two different functions. will they be distinct?
  let classFuns = Map.fromList $ case ci of
        T.Env _ vars _ _ -> flip mapMaybe vars $ \case
          (T.DefinedClassFunction (CFD cd _ _ _ _ _) snapshot _ uci, _, _) -> Just (uci, snapshot ! cd)
          _ -> Nothing

        _ -> undefined
  let what = case ci of
        T.Env _ vars _ _ -> flip mapMaybe vars $ \case
          (T.DefinedClassFunction (CFD cd _ _ _ _ _) snapshot _ uci, _, _) -> Just (uci, snapshot ! cd)
          _ -> Nothing

        _ -> undefined

  pf "WITH CLASS INSTANCE ASSOCIATIONS:\n\tOLD: %\n\tNEW: %\n\tWHAT: %" (ppDef $ Map.keysSet <$> ogTM) (ppDef $ Map.keysSet <$> classFuns) (ppDef $ Def.fmap2 Map.keysSet what <&> \(uci, dds) -> fromString (Def.printf "%: %" (ppDef uci) (ppDef dds)) :: Def.Context)

  -- this should probably be a reader thing.
  -- pf "WITH CLASS INSTANTIATIONS (env %): %" (pp (T.envID ci)) $ ppDef $ Map.keysSet <$> classFuns
  x <- State.withStateT (\s -> s { classInstantiationAssociations = classFuns }) a
  State.modify $ \s -> s { classInstantiationAssociations = ogTM }

  pure x



mUnion :: (T.EnvUnionF (Type TC), [Type IM], Type IM) -> Context IM.EnvUnion
mUnion (tunion, params, ret) = do

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  TypeMap _ envMap <- State.gets tvarMap
  case envMap !? tunion.unionID of
    Just mru -> pure mru
    Nothing -> do
      -- this adds instantiations from this specific union instantiation to cucked unions.
      let addCuckedUnionEnvs :: T.EnvUnionF (Type TC) -> IM.EnvUnion -> Context ()
          addCuckedUnionEnvs tuni cuckuni = do
            envs <- sequenceA2 $ fmap (\(_, _, _, env) -> mType <$> env) tuni.union
            let instantiatedEnvs = Set.fromList $ filter (null . foldMap ftvButIgnoreUnions) envs
            State.modify $ \c -> c { cuckedUnionInstantiation = Map.insertWith (<>) cuckuni instantiatedEnvs c.cuckedUnionInstantiation }
      -- check if we previously encountered this environment and it contained TVars that weren't mapped.
      cuckedMemo <- State.gets cuckedUnions
      case isMemoed (tunion.unionID, params, ret) cuckedMemo of
        Just mu -> do
          addCuckedUnionEnvs tunion mu
          pure mu

        Nothing -> do
          -- it wasn't... but it's still possible.
          tunion' <- sequenceA $ mType <$> tunion
          let unionFTV = foldMap ftvButIgnoreUnions tunion'
          if not (null unionFTV)
            then do
              -- had TVars -> remember it.
              ieu <- memo' cuckedUnions (\mem mctx -> mctx { cuckedUnions = mem }) (tunion'.unionID, params, ret) $ \(eid, _, _) _ -> do
                let menvs = tunion'.union <&> \(_, _, _, env) -> env
                case menvs of
                  -- literally impossible as there would be no FTVs otherwise...
                  [] -> error $ Def.printf "[COMPILER ERROR]: Encountered an empty union (ID: %) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ IM.EnvUnion { IM.unionID = eid, IM.union = e :| es, IM.oldUnion = tunion }

              addCuckedUnionEnvs tunion ieu
              pure ieu

            else
              -- normal union - all TVars mapped. safe to memoize.
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) (tunion', params, ret) $ \(tunion'', params, ret) _ -> do
                let menvs = tunion''.union <&> \(_, _, _, env) -> env
                case menvs of
                  [] -> error $ Def.printf "[COMPILER ERROR]: Encountered an empty union (ID: %) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    nuid <- newUnionID
                    pf "NEW NORMAL UNION: % % % => %" tunion'' params ret nuid
                    pure $ IM.EnvUnion { IM.unionID = nuid, IM.union = e :| es, IM.oldUnion = tunion }



mEnvTypes :: T.EnvF (Type TC) -> Context IM.EnvTypes
mEnvTypes env = do
  menv <- traverse mType env
  pure $ case menv of
    T.Env eid params _ _ -> do
      IM.EnvTypes eid $ params <&> \(_, _, t) -> t

    T.RecursiveEnv _ _ -> error "I think recursive env cannot be monomorphised."



------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , tvarInsts :: Map (TVar TC) (Map (ClassDef TC) (InstDef TC))  -- TODO: smell.
  , memoFunction :: Memo (Function TC, [Type IM], Type IM, IM.EnvTypes) (Function IM)
  , memoDatatype :: Memo (DataDef TC, TypeMap) (DataDef IM, Map (DataCon TC) (DataCon IM))
  , memoEnv :: Memo (T.EnvF (Type TC, Type IM)) IM.Env
  , memoUnion :: Memo (T.EnvUnionF (Type IM), [Type IM], Type IM) IM.EnvUnion
  , memoMember :: Memo (DataDef IM, Def.MemName) Def.UniqueMem

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo (Def.UnionID, [Type IM], Type IM) IM.EnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  , cuckedUnionInstantiation :: Map IM.EnvUnion (Set (T.EnvF (Type IM)))  -- (NOTE: THIS IS ACTUALLY USED AT THE END. LSP CAN'T COMPREHEND OVERLOADED RECORD DOTS) this one is to track all environments which get instantiated for this union. (not sure if it's still needed if we pre-search variables in body anyway.)
  -- also, this can be done in the same way as subst - would even require us to track less state.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: IM.EnvInstantiations  -- NOTE: FUTURE TYPECHECK
  -- i think it's also not needed now.

  , classInstantiationAssociations :: CurrentInstances
  , currentEnvStack :: Def.EnvStack -- HACK: it's for knowing when instances should be local or not. (TC ENV STACK, NOT THE NEW IDs)
  , lastEnvironment :: [(IM.Variable, Type IM)]  -- HACK: for knowing which variable should envmod use.

  , completedEnvs :: Set IM.Env
  , environmentsLeft :: Map IM.Env [Function IM]
  }
type Context = StateT Context' PrintContext

startingContext :: Context'
startingContext = Context
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

  , classInstantiationAssociations = mempty
  , currentEnvStack = mempty
  , lastEnvironment = mempty

  , completedEnvs = mempty
  , environmentsLeft = mempty
  }


-----------------------
-- TypeMap stuff
----------------------

-- HACK: EnvUnions are only needed when monomorphizing types. However, it's slightly easier right now to add this field. This should probably change later.
--  TODO: what did I mean???
data TypeMap = TypeMap (Map (TVar TC) (Type IM)) (Map Def.UnionID IM.EnvUnion) deriving (Eq, Ord)

instance Semigroup TypeMap where
  TypeMap l1 l2 <> TypeMap r1 r2 = TypeMap (l1 <> r1) (l2 <> r2)

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty


ppTypeMap :: TypeMap -> Def.Context
ppTypeMap (TypeMap tvs unions) = Def.ppLines'
  [ (Def.ppMap . fmap (bimap pp pp) . Map.toList) tvs
  , (Def.ppMap . fmap (bimap pp pp) . Map.toList) unions
  ]


typeMapFromDataDef :: DataDef TC -> [Type IM] -> [Maybe IM.EnvUnion] -> TypeMap
typeMapFromDataDef (DD _ (T.Scheme tvs unions) _ _) mts munions =
  TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip (unions <&> \(u, _, _) -> u) munions)


-- ahhh, i hate it. TODO: try to figure out if there is a way to do it without doing this time consuming and error prone mapping.
mapType :: Type TC -> Type IM -> TypeMap
mapType tt mt = case (project tt, project mt) of
  (TFun tu tts tret, TFun mu mts mret) -> mapTypes tts mts <> mapType tret mret <> TypeMap mempty (Map.singleton tu.unionID mu)
  (TCon _ tts tus, TCon _ mts mus) -> mapTypes tts mts <> TypeMap mempty (Map.fromList $ zip (T.unionID . (\(u, _, _) -> u) <$> tus) mus)
  (TO (T.TVar tv), t) -> TypeMap (Map.singleton tv (embed t)) mempty

  _ -> error $ Def.printf "[COMPILER ERROR]: Fuck."

mapTypes :: [Type TC] -> [Type IM] -> TypeMap
mapTypes tts mts = mconcat $ zipWith mapType tts mts



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


withEnvContext :: Map (T.EnvF (Type IM)) IM.Env -> IM.EnvInstantiations -> Map IM.EnvUnion (Set (T.EnvF (Type IM))) -> EnvContext a -> PrintContext a
withEnvContext menvs allInstantiations cuckedUnionInstantiations x = fst <$> RWS.evalRWST x envUse envMemo
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
    Fun (IM.EnvDefs envs) -> do
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
            mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

      decons' <- for decons $ \(um, decon) -> do
        mdecon <- decon
        pure (um, mdecon)
      pure $ CaseRecord dd decons'

    CaseConstructor dc decons -> do
      mdc <- mfConstructor dc t
      mdecons <- sequenceA decons
      pure $ CaseConstructor mdc mdecons


mfExpr :: Expr IM -> EnvContext (Expr M)
mfExpr = cata $ \(N imt imexpr) -> do
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


mfEnvDef :: IM.EnvDef -> EnvContext M.EnvDef
mfEnvDef (IM.EnvDef { envDef = fn, notYetInstantiated = notInstFuns }) = do
    env' <- mfFunction fn
    mNotInstFuns <- traverse mfFunction notInstFuns
    pure $ M.EnvDef { envDef = env', notYetInstantiated = mNotInstFuns } -- M.Env eid menvContent
mfEnvDef _ = error "RECURSIVE ENV"

mfEnv' :: IM.Env -> EnvContext M.Env
mfEnv' = \case
  IM.Env eid vars _ -> do
    menvContent <- traverse (\(v, l, t) -> mfType t >>= \t' -> (,l,t') <$> mfVariable v) vars  -- the weird monad shit is so we 
    pure $ M.Env eid menvContent
  IM.RecursiveEnv eid isEmpty ->
    pure $ M.RecursiveEnv eid isEmpty

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

mfEnv :: T.EnvF (Type IM) -> EnvContext (Maybe M.Env)
mfEnv (T.RecursiveEnv {}) = error "RECURSION. This, with the weird monad shit makes us crash at recursion."
mfEnv env = do
  findEnvs <- RWS.asks envs
  traverse mfEnv' $ findEnvs !? env


mfType :: Type IM -> EnvContext (Type M)
mfType = para $ fmap embed . \case
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
mfUnion = memo memoIUnion (\mem s -> s { memoIUnion = mem }) $ \union _ -> do
  cuckedUnions <- RWS.asks cuckedUnionInsts
  mappedEnvs <- case cuckedUnions !? union of
      -- here should be no ftvs.
      Nothing -> fmap concat $ for (NonEmpty.toList union.union) $ \env -> do
          pf "???: % ?? %" (pp env) (show $ null (foldMap ftvButIgnoreUnions env))
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
        [] -> error $ "[COMPILER ERROR] Empty union (" <> show union.unionID <> ") encountered... wut!??!??!?!? Woah.1>!>!>!>!>>!"
        (x:xs) -> x :| xs

  pure $ M.EnvUnion { M.unionID = union.unionID, M.union = mUsedEnvs }



mfDataDef :: (DataDef IM, [M.EnvUnion]) -> EnvContext (DataDef M, Map (DataCon IM) (DataCon M))
mfDataDef = memo memoIDatatype (\mem s -> s { memoIDatatype = mem }) $ \(idd, _) addMemo -> mdo
  mfAppliedTypes <- traverse mfType idd.ddScheme.appliedTypes
  let dd = DD idd.ddName (M.OtherDD mfAppliedTypes undefined) cons idd.ddAnns
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
        _ -> error $ Def.printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%)." (pp imt)

  -- mtypes <- traverse mfType ttypes
  munions <- traverse mfUnion imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  pure mdc



ftvButIgnoreUnionsInEnv :: IM.Env -> Set IM.TVar
ftvButIgnoreUnionsInEnv (IM.Env _ vs _) = (foldMap . foldMap) ftvButIgnoreUnions vs
ftvButIgnoreUnionsInEnv (IM.RecursiveEnv {}) = mempty

ftvButIgnoreUnions :: Type IM -> Set IM.TVar
ftvButIgnoreUnions = cata $ \case
  TO (IM.TVar tv) -> Set.singleton tv
  TCon _ ts _ -> mconcat ts
  TFun _ args ret -> mconcat args <> ret


expectIDataDef :: Type IM -> DataDef IM
expectIDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))

expectDataDef :: Type M -> DataDef M
expectDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %)" (pp (embed mpt))



-------------------------
-- Step 2 Type defs!
------------------------


type EnvContext = RWST EnvContextUse () EnvMemo PrintContext -- TEMP: PrintContext temporarily for debugging. should not be used for anything else.
-- Stores environment instantiations. 
--   NOTE: In the future, maybe more stuff (like which constructors were used!)
data EnvContextUse = EnvContextUse
  { allInsts :: IM.EnvInstantiations
  , envs     :: Map (T.EnvF (Type IM)) IM.Env
  , cuckedUnionInsts :: Map IM.EnvUnion (Set (T.EnvF (Type IM)))
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


mustSelectInstance :: Type IM -> T.PossibleInstances -> InstDef TC
mustSelectInstance (Fix (TCon mdd _ _)) insts =
  case insts !? mdd.ddScheme.ogDataDef of
    Just instdef -> instdef
    Nothing -> error $ Def.printf "INSTANCE FOR % DOES NOT EXIST." (ppDef mdd)
mustSelectInstance _ _ = error "TRYING TO SELECT AN INSTANCE FOR A FUNCTION."
