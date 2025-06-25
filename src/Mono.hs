{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- we implement basic instances (Foldable, Travesable) for Tuple.

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}  -- for HLINT kekek
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant pure" #-}  -- this is retarded. it sometimes increases readability with that extra pure.
module Mono (mono) where

import qualified AST.Typed as T
import qualified AST.Mono as M
import qualified AST.Common as Common
import Data.Fix (Fix(..))
import Data.Functor.Foldable (embed, cata, para, project)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first, bimap)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map, (!?), (!))
import Control.Monad.Trans.State (StateT)
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
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
import Control.Monad.Trans.RWS (RWST)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Bifoldable (bifold)
import Control.Monad (void)
import qualified Data.IORef as IORef
import Data.String (fromString)
import Data.List (find)
import Data.Bool (bool)
import AST.Typed (TC)
import AST.Common (AnnStmt, Module, StmtF (..), Expr, Node (..), ExprF (..), Function (..), TypeF (..), ClassFunDec (..), Type, CaseF (..), Case, Decon, DeconF (..), FunDec (..), TVar (..), ClassType, DataDef (..), ClassTypeF (..), DataCon (..), ClassDef, InstDef, IfStmt (..))
import AST.Mono (M)
import AST.IncompleteMono (IM)
import AST.Def ((:.) (..), Annotated (..), Locality (..), phase, PP (..), fmap2, PPDef (..), traverse2, sequenceA2)
import qualified AST.IncompleteMono as IM
import qualified AST.Def as Def




------ Monomorphization consists of two steps:
--  Step 1: Perform normal monomorphization (however, you won't be able to compile escaped TVars).
--  Step 2: Replace escaped TVars with each instantiation of them. (TODO: this is bad, but necessary. maybe do it in RemoveUnused somehow?)


mono :: [AnnStmt TC] -> IO (Module M)
mono tmod = do
  -- Step 1: Just do monomorphization with a few quirks*.
  (mistmts, monoCtx) <- flip State.runStateT startingContext $ do
    let usedVarsInCurrentScope = findUsedVarsInFunction tmod
    insts <- fmap fold $ for (Set.toList usedVarsInCurrentScope) $ \(v, t) -> do
      mt <- mType t
      mv <- variable v (t, mt)
      pure ()
      -- insts <- gatherInstsFromEnvironment mv
      -- pure $ Set.insert (M.asUniqueVar mv, mt) insts
    -- State.modify $ \c -> c { usedVars = insts }
    -- ctxPrint' $ printf "PRE INSTS: %s" (Common.ppList (\(uv, _) -> Common.ppVar Local uv) (Set.toList insts))
    stmts <- mStmts tmod
    pure stmts

  let envs = Map.mapKeys (fmap snd) $ memoToMap monoCtx.memoEnv

  phase "Monomorphisation (env instantiations)"
  Def.ctxPrint (Def.ppMap . fmap (bimap pp (Def.encloseSepBy "[" "]" ", " . fmap (\(EnvUse _ env) -> pp env) . Set.toList)) . Map.toList) monoCtx.envInstantiations

  phase "Monomorphisation (just envs)"
  Def.ctxPrint (Def.ppMap . fmap (bimap pp pp) . Map.toList) envs

  phase "Monomorphisation (first part)"
  Def.ctxPrint (Def.ppLines pp) mistmts


  -- Step 2 consists of:
  -- 1. substitute environments
  -- 2. check function usage and remove unused EnvDefs

  mmod <- withEnvContext envs monoCtx.envInstantiations monoCtx.cuckedUnionInstantiation $ do
    mstmts <- mfAnnStmts mistmts
    pure $ M.Mod { M.topLevelStatements = mstmts }

  pure mmod



mStmts :: Traversable f => f (AnnStmt TC) -> Context (f (AnnStmt IM))
mStmts = traverse mAnnStmt

mAnnStmt :: AnnStmt TC -> Context (AnnStmt IM)
mAnnStmt = cata (fmap embed . f) where
  f :: (:.) Annotated (StmtF TC (Expr TC)) (Context (AnnStmt IM)) -> Context ((:.) Annotated (StmtF IM (Expr IM)) (AnnStmt IM))
  f (O (Annotated ann stmt)) = do
    stmt' <- bitraverse mExpr id stmt
    let
      mann, noann :: b a -> Context ((:.) Annotated b a)
      mann = pure . O . Annotated ann
      noann = pure . O . Annotated []

    -- NOTE: this is just remapping.......
    case stmt' of
      Pass -> mann Pass
      ExprStmt expr -> mann $ ExprStmt expr
      Assignment vid expr -> mann $ Assignment vid expr
      Print expr -> mann $ Print expr
      Mutation vid expr -> mann $ Mutation vid expr
      If (IfStmt cond ifTrue elseIfs else') -> mann $ If $ IfStmt cond ifTrue elseIfs else'
      Switch switch cases -> do
        mcases <- traverse mCase cases
        mann $ Switch switch mcases
      Return ete -> do
        mete <- mExpr ete
        mann $ Return mete
      Fun fn -> do
        let env = fn.functionDeclaration.functionEnv
        let envID = T.envID env
        envInsts <- State.gets envInstantiations

        let currentEnvUses = fromMaybe mempty $ envInsts !? envID
        let defs = Set.toList currentEnvUses <&> \(EnvUse (Just fn) env) -> (fn, env)

        noann $ case defs of
          [] -> Pass
          (x:xs) -> Fun $ x :| xs

      Inst inst -> do
        envInsts <- State.gets envInstantiations

        let envs = flip concatMap inst.instFuns $ \fn ->
              let env = fn.instFunDec.functionEnv
                  envID = T.envID env
                  currentEnvUses = fromMaybe mempty $ envInsts !? envID
                  defs = Set.toList currentEnvUses <&> \(EnvUse (Just fn) env) -> (fn, env)
              in  defs


        noann $ case envs of
          [] -> Pass
          (x:xs) -> Fun $ x :| xs

      Other () -> error "OTHER OTHER OTHER SHOULD NOT BE CREATED EVER"



mExpr :: Expr TC -> Context (Expr IM)
mExpr = cata $ fmap embed . \(N t expr) -> do
  mt <- mType t
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
          mv <- variable v (t, mt)
          State.modify $ \c -> c { usedVars = Set.insert (v, mt) c.usedVars }

          newLocality <- case v of
                T.DefinedClassFunction _ _ self uci -> do
                  -- NOTE: ANOTHER COPYPASTA TO KNOW THE OG INSTANCE OF THIS FUNCTION.
                  ucis <- State.gets classInstantiationAssociations
                  mself <- mType self
                  (ifnts, ivfn) <- case ucis !? uci of
                        Just (l, r, _) -> do
                          (foundSelf, inst) <- bitraverse mType pure (l, r)  -- ts <&> \(l, r, _) -> (l, r)
                          if foundSelf == mself
                            then pure inst
                            else error $ Def.printf "ASSIGNED INSTANCE NOT MATCHED. current %s =/= found %s" (pp foundSelf) (pp mself)
                        Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"

                  let vfn = Function ivfn.instFunDec ivfn.instFunBody
                  let (T.Env _ _ _ level) = vfn.functionDeclaration.functionEnv
                  cl <- State.gets currentLevel
                  pure $ if level == cl then Local else FromEnvironment

                _ -> pure locality

          pure $ Var mv newLocality

        Con c eid -> do
          mc <- constructor c t

          -- don't forget to register usage. (for codegen)
          void $ withEnv Nothing (T.Env eid [] mempty 0) (pure ())

          pure $ Con mc ()

        RecCon _ inst -> do
          let dd = expectIDataDef mt
          inst' <- for inst $ \(mem, memt) -> do
            ut <- member (dd, mem)
            pure (ut, memt)

          pure $ RecCon dd inst'

        RecUpdate me upd -> do
          -- TODO: Before i had a reference to the data def, but i may add it later. Maybe I should add the info while I'm checking types?
          let dd = expectIDataDef (Common.typeOfNode me)
          upd' <- for upd $ \(mem, meme) -> do
            ut <- member (dd, mem)
            pure (ut, meme)

          pure $ RecUpdate me upd'

        MemAccess me memname -> do
          let dd = expectIDataDef (Common.typeOfNode me)
          um <- member (dd, memname)
          pure $ MemAccess me um

        Lit lit -> pure $ Lit lit
        Op l op r -> pure $ Op l op r
        Call e args -> pure $ Call e args
        As (Fix (N _ e)) _ -> do
          -- Ignore 'as' by unpacking the variable and passing in the previous expression.
          pure e

  pure $ N mt mexpr

withEnv :: Maybe (Function IM) -> T.Env -> Context a -> Context (a, IM.Env)
withEnv mfn env cx = do
  let showOldVars ovs = Def.ppList (Def.ppTup3 . (\(l, m, r) -> (pp l, pp m, Def.ppSet pp $ Set.toList r))) $ Set.toList ovs
  -- let printUsedVarsState uvType uvTypeTag uvs = ctxPrint' $ printf "%s%s: USED VARS %s WITH ENV%s: %s" (Common.ppEnvID $ T.envID env) (uvTypeTag :: Def.Context) (uvType :: Def.Context) (case mfn of { Nothing -> "" :: Def.Context; Just fn -> fromString $ printf " (%s)" $ ppVar Local fn.functionDeclaration.functionId }) (showOldVars uvs)

  -- oldVars <- State.gets usedVars
  -- State.modify $ \c -> c { usedVars = mempty }
  -- printUsedVarsState "BEFORE" "B" oldVars
  prevlev <- State.gets currentLevel
  let curlev = case env of
        T.Env _ _ _ lev -> lev
        _ -> undefined
  State.modify $ \c -> c { currentLevel = curlev + 1 }
  x <- cx
  State.modify $ \c -> c { currentLevel = prevlev }

  -- vars <- State.gets usedVars
  -- printUsedVarsState "INSIDE" "I" vars
  -- State.modify $ \c -> c { usedVars = oldVars <> c.usedVars }
  -- allVars <- State.gets usedVars
  -- printUsedVarsState "AFTER " "A" allVars  -- padding for logs to line up.


  itenv <- traverse (\t -> (t,) <$> mType t) env
  menv <- memo' memoEnv (\m c -> c { memoEnv = m }) itenv $ \env' _ -> case env' of
    T.Env oldEID envContent locs currentLevel -> do
      newEID <- newEnvID

      let toEnvVar (v, l, (tt, mt)) = do
            v' <- variable v (tt, mt)
            li <- needsLateInitialization v
            case v of
              T.DefinedClassFunction _ _ self uci -> do
                  ucis <- State.gets classInstantiationAssociations
                  mself <- mType self
                  (ifnts, ivfn) <- case ucis !? uci of
                        Just (l, r, _) -> do
                          (foundSelf, inst) <- bitraverse mType pure (l, r)  -- ts <&> \(l, r, _) -> (l, r)
                          if foundSelf == mself
                            then pure inst
                            else error $ Def.printf "ASSIGNED INSTANCE NOT MATCHED. current %s =/= found %s" (pp foundSelf) (pp mself)
                        Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"

                  let vfn = Function ivfn.instFunDec ivfn.instFunBody
                  let T.Env cureid _ _ instanceLevel = vfn.functionDeclaration.functionEnv
                  if currentLevel < instanceLevel
                    then do
                      let envs = case project tt of
                            TFun union _ _ -> union.union
                            _ -> error "Immmmmmmpossible"

                          tryLocalizeEnv (T.Env _ envContent _ _) = sequenceA $ flip mapMaybe envContent $ \(vEnv, _, tEnv) -> 
                              locs !? T.asProto vEnv <&> \newLoc -> do
                                mtEnv <- mType tEnv
                                mvEnv <- variable vEnv (tEnv, mtEnv)
                                li <- needsLateInitialization vEnv
                                pure (mvEnv, newLoc, li, mtEnv)
                          tryLocalizeEnv _ = error "impossssssible"

                      instanceEnv <- fmap concat $ traverse tryLocalizeEnv $ filter ((==cureid) . T.envID) envs
                      Def.ctxPrint' $ Def.printf "LOCALITIES of %s->%s:\n%s" (pp oldEID) (pp newEID) $ Def.ppMap $ fmap (bimap (pp . (\case { T.PDefinedVariable uv -> uv; T.PDefinedFunction fn -> fn.functionDeclaration.functionId; T.PDefinedClassFunction (CFD _ uv _ _) -> uv })) (fromString . show)) $ Map.toList locs
                      Def.ctxPrint (Def.ppList pp) envs
                      Def.ctxPrint (Def.ppList $ \(v, _, _, _) ->  ppDef v) instanceEnv
                      pure $ instanceEnv <&> \(v, l, _, mt) -> (v, l, mt)
                    else
                      pure [(v', l, mt)]


              _ -> do
                pure [(v', l, mt)]
      menvContent <- traverse toEnvVar envContent
      pure $ IM.Env newEID $ concat menvContent

    T.RecursiveEnv {} -> error "SHOULD NOT HAPPEN."  -- pure $ M.IDRecursiveEnv eid isEmpty


  Def.ctxPrint' $ Def.printf "%sM: %s =WITH ENV%s=> %s" (pp $ T.envID env) (pp env) (case mfn of { Nothing -> "" :: Def.Context; Just fn -> fromString $ Def.printf " (%s)" $ pp fn.functionDeclaration.functionId }) (pp menv)
  -- registerEnvMono mfn (T.envID env) menv mempty

  pure (x, menv)

-- TODO: pointless rn.
type LateInit = Bool
needsLateInitialization :: T.Variable -> Context LateInit
needsLateInitialization = const (pure False)

findUsedVarsInExpr :: Expr TC -> Set (T.Variable, Type TC)
findUsedVarsInExpr = cata $ \(N t expr) -> case expr of
  Var v _ -> Set.singleton (v, t)
  e -> fold e

findUsedVarsInFunction :: Foldable t => t (AnnStmt TC) -> Set (T.Variable, Type TC)
findUsedVarsInFunction = foldMap $ cata $ bifold . first findUsedVarsInExpr . Def.deannotate . Def.unO

mCase :: CaseF TC (Expr IM) (AnnStmt IM) -> Context (Case IM)
mCase kase = do
  decon <- mDecon kase.deconstruction
  pure $ Case decon kase.caseCondition kase.caseBody

mDecon :: Decon TC -> Context (Decon IM)
mDecon = cata $ fmap embed . \(N t d) -> do
  mt <- mType t
  N mt <$> case d of
    CaseVariable uv -> do
      pure $ CaseVariable uv

    CaseRecord _ args -> do
      -- fun unsafe shit.
      let dd = case project mt of
            TCon mdd _ _ -> mdd
            mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %s)" (pp (embed mpt))

      margs <- for args $ \(mem, decon) -> do
        mdecon <- decon
        um <- member (dd, mem)
        pure (um, mdecon)

      pure $ CaseRecord dd margs

    CaseConstructor dc args -> do
      mdc <- constructor dc t
      margs <- sequenceA args
      pure $ CaseConstructor mdc margs



variable :: T.Variable -> (Type TC, Type IM) -> Context IM.Variable  -- NOTE: we're taking in both types, because we need to know which TVars were mapped to types and which to other tvars.
variable (T.DefinedVariable uv) _ = pure $ IM.DefinedVariable uv
variable (T.DefinedFunction vfn snapshot assocs) (instType, et) = do
  Def.ctxPrint' $ "in function: " <> show vfn.functionDeclaration.functionId.varName.fromVN

  -- male feminists are seething rn
  let (tts, tret) = case project et of
        TFun _ mts mret -> (mts, mret)
        _ -> undefined


  -- DEBUG: print a non-memoized type. This was used to check memoization errors.
  Def.ctxPrint' $ Def.printf "Decl (nomemo): %s -> %s" (Def.encloseSepBy "(" ")" ", " $ pp <$> tts) (pp tret)

  let tassocs = vfn.functionDeclaration.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ t _ _) -> t
  massocs <- traverse mType assocs

  -- creates a type mapping for this function.
  let typemap = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret <> mapTypes tassocs massocs

  let fd = vfn.functionDeclaration
  let genType = Fix $ TFun undefined (snd <$> fd.functionParameters) fd.functionReturnType
  let tvtvMap = cringeGetReinstantiatedVariables fd.functionId genType instType
  -- withClassInstanceAssociations fd.functionOther.functionClassInstantiationAssociations
    -- $ withTVarInsts tvtvMap snapshot fd.functionId typemap
  withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map though albeit.
    menv <- mEnvTypes' vfn.functionDeclaration.functionEnv

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv) $ \(tfn, ts, ret, _) addMemo -> mdo

      uv <- newUniqueVar tfn.functionDeclaration.functionId

      params <- flip zip ts <$> traverse (mDecon . fst) tfn.functionDeclaration.functionParameters
      let fundec = FD env uv params ret () :: FunDec IM


      -- DEBUG: when in the process of memoization, show dis.
      Def.ctxPrint' $ Def.printf "Decl: %s -> %s" (Def.encloseSepBy "(" ")" ", " $ pp <$> ts) (pp ret)
      Def.ctxPrint' $ Def.printf "M function: %s" (pp fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = Function { functionDeclaration = fundec, functionBody = body } :: Function IM
      addMemo fn
      (body, env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        -- also dont forget about cucked unions
        cusKeys <- Map.keysSet . Memo.memoToMap <$> State.gets cuckedUnions
      
        vars <- State.gets usedVars
        usedEnvs <- State.gets envInstantiations
        State.modify $ \c -> c { usedVars = mempty, envInstantiations = mempty }
        let usedVarsInCurrentScope = findUsedVarsInFunction tfn.functionBody
        _ <- fmap fold $ for (Set.toList usedVarsInCurrentScope) $ \(v, t) -> do
          mt <- mType t
          mv <- variable v (t, mt)
          -- let insts = gatherInstsFromEnvironment mv
          pure ()
        -- State.modify $ \c -> c { usedVars = insts }
        stmts <- mStmts tfn.functionBody
        -- State.modify $ \c -> c { usedVars = vars }

        let usedEnvIDs curenv = case curenv of
              -- NOTE: in the future, we might also need to insert the current env's ID due to recursiveness?
              T.Env _ vars _ _ -> flip foldMap vars $ \case
                (T.DefinedFunction fn _ _, _, _) -> Set.insert (T.envID fn.functionDeclaration.functionEnv) (usedEnvIDs fn.functionDeclaration.functionEnv)
                _ -> mempty
              _ -> error "RECURSIVE"

        State.modify $ \c -> c
          { cuckedUnions = Memo $ Map.restrictKeys (Memo.memoToMap c.cuckedUnions) cusKeys -- cucked unions should be local per function
          , envInstantiations = Map.unionWith (<>) usedEnvs (Map.restrictKeys c.envInstantiations (usedEnvIDs tfn.functionDeclaration.functionEnv)) -- only allow non-local instantiations through. (otherwise we get extra environment declarations)
          }

        pure stmts


      pure fn

    -- NOTE: moved outside of memoization, because we depend on these "registrations" to tell us which environments need to actually be memoized.
    --       this is bad btw, but that's how it currently works. see [doc/compiler/new-expansion-scheme]
    registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) fn.functionDeclaration.functionEnv mempty
    pure $ IM.DefinedFunction fn

variable (T.DefinedClassFunction cfd@(CFD cd _ cfdParams cfdRet) snapshot self uci) (instType, et) = do
  -- male feminists are seething rn
  let (tts, tret) = case project et of
        TFun _ mts mret -> (mts, mret)
        _ -> undefined


  -- FIX: Fix for class functions not instantiating tvars, but it's bad.
  Def.ctxPrint' $ Def.printf "Self: %s" (pp self)
  ucis <- State.gets classInstantiationAssociations
  mself <- mType self
  (ifnts, ivfn) <- case ucis !? uci of
      Just (l, r, _) -> do
        (foundSelf, inst) <- bitraverse mType pure (l, r)  -- ts <&> \(l, r, _) -> (l, r)
        if foundSelf == mself
          then pure inst
          else error $ Def.printf "ASSIGNED INSTANCE NOT MATCHED. current %s =/= found %s" (pp foundSelf) (pp mself)
      Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"

  let vfn = Function ivfn.instFunDec ivfn.instFunBody

  Def.ctxPrint' $ Def.printf "Variable: %s.\n\tT Type: (%s) -> %s\n\tM Type: %s\n" (pp vfn.functionDeclaration.functionId) (Def.sepBy ", " $ pp . snd <$> vfn.functionDeclaration.functionParameters) (pp vfn.functionDeclaration.functionReturnType) (pp et)

  Def.ctxPrint' $ "in (class) function: " <> show vfn.functionDeclaration.functionId.varName.fromVN


  -- creates a type mapping for this function.
  let tassocs = vfn.functionDeclaration.functionOther.functionAssociations <&> \(T.FunctionTypeAssociation _ t _ _) -> t

  massocs <- traverse mType ifnts


  Def.ctxPrint' $ Def.printf "t assocs: %s\nm assocs: %s\n" (Def.sepBy ", " $ pp <$> tassocs) (Def.sepBy ", " $ pp <$> massocs)

  let typemap = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret
        <> mapTypes tassocs massocs  -- FIX: this should be `mapTypes tassocs massocs`, but I don't know how to pass them here, so I'll use the environment instead.

  let fd = vfn.functionDeclaration
  let genType = Fix $ TFun undefined (snd <$> fd.functionParameters) fd.functionReturnType
  let tvtvMap = cringeGetReinstantiatedVariables fd.functionId genType instType
  -- withClassInstanceAssociations fd.functionClassInstantiationAssociations
    -- $ withTVarInsts tvtvMap snapshot fd.functionId typemap
  withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map though albeit.
    menv <- mEnvTypes' vfn.functionDeclaration.functionEnv

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv) $ \(tfn, ts, ret, _) addMemo -> mdo

      uv <- newUniqueVar tfn.functionDeclaration.functionId

      params <- flip zip ts <$> traverse (mDecon . fst) tfn.functionDeclaration.functionParameters
      let fundec = FD env uv params ret () :: FunDec IM


      -- DEBUG: when in the process of memoization, show dis.
      Def.ctxPrint' $ Def.printf "Decl: %s -> %s" (Def.encloseSepBy "(" ")" ", " $ pp <$> ts) (pp ret)
      Def.ctxPrint' $ Def.printf "M function: %s" (pp fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = Function { functionDeclaration = fundec, functionBody = body } :: Function IM
      addMemo fn
      (body, env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        mStmts tfn.functionBody

      pure fn

    registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) fn.functionDeclaration.functionEnv mempty
    pure $ IM.DefinedFunction fn

gatherInstsFromEnvironment :: IM.Variable -> Set (IM.Variable, Type IM)
gatherInstsFromEnvironment = \case
  IM.DefinedFunction fn -> case fn.functionDeclaration.functionEnv of
    IM.RecursiveEnv _ _ -> mempty
    IM.Env _ vars -> flip foldMap vars $ \case
      (envVar, Local, t) -> Set.insert (envVar, t) (gatherInstsFromEnvironment envVar)
      (envVar, _, t) -> Set.singleton (envVar, t)
  _ -> mempty


-- CRINGE: FUCK.
-- EDIT: 29.04.25 WHAT IS THIS????
cringeGetReinstantiatedVariables :: Def.UniqueVar -> Type TC -> Type TC -> Map (TVar TC) (TVar TC)
cringeGetReinstantiatedVariables binding gen inst = case (project gen, project inst) of
  (TO (T.TVar to), TO (T.TVar from)) | to.binding == Def.BindByVar binding -> Map.singleton from to

  (TFun _ lts lt, TFun _ rts rt) -> fold (zipWith (cringeGetReinstantiatedVariables binding) lts rts) <> (cringeGetReinstantiatedVariables binding) lt rt
  (TCon _ lts _, TCon _ appts _) -> fold $ zipWith (cringeGetReinstantiatedVariables binding) lts appts

  _ -> mempty

-- I assume it's a quick mapping for classes. TODO: refactor nigga.
cringeMapClassType :: ClassType TC -> Type IM -> Map (TVar TC) (DataDef TC)
cringeMapClassType lpt rpt = case (project lpt, project rpt) of
  (NormalType (TO (T.TVar tv)), TCon dd _ _) -> Map.singleton tv dd.ddScheme.ogDataDef
  (NormalType (TO (T.TVar {})), TFun {}) -> mempty
  (Self, _) -> mempty

  (NormalType (TFun _ lts lt), TFun _ rts rt) -> fold (zipWith cringeMapClassType lts rts) <> cringeMapClassType lt rt
  (NormalType (TCon _ lts _), TCon _ appts _) -> fold $ zipWith cringeMapClassType lts appts

  _ -> undefined



-- Registers a single environment monomorphization. later used to track which environments monomoprhised to what.
-- TODO: seems to be unneeded now.
registerEnvMono :: Maybe (Function IM) -> Def.EnvID -> IM.Env -> Set (Def.UniqueVar, Type IM, Set (TVar TC)) -> Context ()
registerEnvMono mvar oldEID nuEnv _ | null (ftvButIgnoreUnionsInEnv nuEnv) = do
  State.modify $ \mctx -> mctx { envInstantiations = Map.insertWith (<>) (IM.envID nuEnv) (Set.singleton (EnvUse mvar nuEnv)) (Map.insertWith (<>) oldEID (Set.singleton (EnvUse mvar nuEnv)) mctx.envInstantiations) }

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
        _ -> error $ Def.printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (pp et)

  mtypes <- traverse mType ttypes

  noEmptyUnions <- hideEmptyUnions tunions
  munions <- (mUnion . fmap mType) `traverse2` noEmptyUnions  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
  -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  let tm = typeMapFromDataDef dd mtypes munions
  (_, dcQuery) <- mDataDef (dd, tm)
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ Def.printf "[COMPILER ERROR]: Failed to query an existing constructor for type %s.\n TypeMap: %s\n(applied TVs: %s, applied unions: %s) -> (applied TVs: %s, applied unions: %s)" (pp ut) (ppTypeMap tm) (Def.ppSet pp ttypes) (Def.ppSet pp tunions) (Def.ppSet pp mtypes) (Def.ppSet (maybe "?" (\u -> pp u.unionID <> (Def.ppSet (pp . T.envID) . NonEmpty.toList) u.union)) munions)

  pure mdc

member :: (DataDef IM, Def.MemName) -> Context Def.UniqueMem
member = memo memoMember (\mem s -> s { memoMember = mem }) $ \(_, memname) _ -> do
  -- TODO: maybe this should be the same as `constructor`, where I just mDataType and find the member?
  --  at least for consistency. also, there won't be incorrect members! but right now, I'll try like this.
  mkUniqueMember memname


mType :: Type TC -> Context (Type IM)
mType = cata $ \case
    TCon dd pts unions -> do
      params <- sequenceA pts

      noEmptyUnions <- hideEmptyUnions (fmap2 mType unions)
      munions <- mUnion `traverse2` noEmptyUnions  -- ISSUE(unused-constructor-elimination): very hacky, but should work. I think it echoes the need for a datatype that correctly represents what we're seeing here - a possible environment definition, which might not be initialized.
      -- we need to represent this shit differently.

      let tm = typeMapFromDataDef dd params munions
      (mdd, _) <- mDataDef (dd, tm)
      let mt = Fix $ TCon mdd params (catMaybes munions)
      pure mt

    TFun union params ret -> do
      union' <- mUnion $ mType <$> union
      params' <- sequenceA params
      ret' <- ret

      pure $ Fix $ TFun union' params' ret'

    TO (T.TVar tv) -> retrieveTV tv

    TO (T.TyVar tv) -> error $ Def.printf "[COMPILER ERROR]: Encountered TyVar %s." (pp tv)


-- ISSUE(unused-constructor-elimination): yeah, this is bad. we also need to remember to map the empty unions (through type map.)
hideEmptyUnions :: [T.EnvUnionF a] -> Context [Maybe (T.EnvUnionF a)]
hideEmptyUnions unions = do
  TypeMap _ mus <- State.gets tvarMap
  pure $ flip fmap unions $ \u -> if Map.member u.unionID mus || not (T.isUnionEmpty u)
    then Just u
    else Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (DataDef TC, TypeMap) -> Context (DataDef IM, Map (DataCon TC) (DataCon IM))
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(tdd@(DD ut (T.Scheme tvs _) tdcs ann), tm@(TypeMap tvmap unionMap)) addMemo -> withTypeMap tm $ mdo

  nut <- newUniqueType ut

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
              TCon _ ts fnUnions -> fold ts <> foldMap isUnionEmpty fnUnions
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
  Def.ctxPrint' $ Def.printf "Mono: %s" (Def.ppTypeInfo ut)
  Def.ctxPrint' "======"
  Def.ctxPrint pp tdcs
  Def.ctxPrint' "------"
  Def.ctxPrint pp strippedDCs
  Def.ctxPrint' ",,,,,,"
  Def.ctxPrint (either (const "n/a (it's a record.)") (Def.ppLines (\(DC _ uc _ _) -> Def.ppCon uc))) mdcs
  Def.ctxPrint' "======"
  Def.ctxPrint' $ Def.printf "Mono'd: %s" (pp nut)

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
  Def.ctxPrint' "Type map:"
  Def.ctxPrint ppTypeMap tm


  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- State.withStateT (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify $ \s -> s { tvarMap = ogTM }

  pure x


withClassInstanceAssociations :: T.ClassInstantiationAssocs -> Context a -> Context a
withClassInstanceAssociations ucis a = do
  ogTM <- State.gets classInstantiationAssociations

  liftIO $ Def.ctxPrint' $ Def.printf "CIA: %s" (Def.ppMap $ fmap (bimap (fromString . show) (Def.encloseSepBy "[" "]" ", " . fmap (Def.ppTup . bimap pp (Def.ppTup . bimap (Def.encloseSepBy "[" "]" ", " . fmap pp) (\ifn -> pp ifn.instFunDec.functionId))))) $ fmap2 (\(l, r, _) -> pure (l, r)) $ Map.toList ogTM)

  x <- State.withStateT (\s -> s { classInstantiationAssociations = ucis <> s.classInstantiationAssociations }) a
  State.modify $ \s -> s { classInstantiationAssociations = ogTM }

  pure x

-- withTVarInsts :: Map T.TVar T.TVar -> T.ScopeSnapshot -> UniqueVar -> TypeMap -> Context a -> Context a
-- withTVarInsts tvNewTV snapshot fnId (TypeMap tvars _) a = do
--   -- DEBUG

--   ogInsts <- State.gets tvarInsts
--   -- Remap with TVars which are mapped to previous TVars -> these need the previous scope snapshot.
--   let instsWithMappedTVars = Map.mapKeys (\tv -> fromMaybe tv $ tvNewTV !? tv) ogInsts <> ogInsts
--   -- The ones that are mapped to actual types need the scope snapshot from this instantiation.
--   let otherNewTVars = flip Map.mapMaybeWithKey tvars $ \ttv mt -> case (ttv, project mt) of
--         (tv, M.ITCon dd _ _) | tv.binding == Common.BindByVar fnId ->
--           fmap Map.fromList $ for (Set.toList tv.tvConstraints) $ \cd -> do
--             pis <- snapshot !? cd
--             instdef <- pis !? dd.ogDataDef
--             pure (cd, instdef)
--         _ -> Nothing

--   -- Merge both. Be sure to merge the older ones first, so as to not overwrite the tvars from this function, but which need the previous scope snapshot.
--   let newInsts = instsWithMappedTVars <> otherNewTVars

--   ctxPrint' "TVar Insts"
--   ctxPrint T.pBacking newInsts

--   State.modify (\s -> s { tvarInsts = newInsts })
--   x <- a
--   State.modify $ \s -> s { tvarInsts = ogInsts }

--   pure x



mUnion :: T.EnvUnionF (Context (Type IM)) -> Context IM.EnvUnion
mUnion tunion = do

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  TypeMap _ envMap <- State.gets tvarMap
  case envMap !? tunion.unionID of
    Just mru -> pure mru
    Nothing -> do
      -- this adds instantiations from this specific union instantiation to cucked unions.
      let addCuckedUnionEnvs :: T.EnvUnionF (Context (Type IM)) -> IM.EnvUnion -> Context ()
          addCuckedUnionEnvs tuni cuckuni = do
            envs <- sequenceA2 tuni.union
            let instantiatedEnvs = Set.fromList $ filter (null . foldMap ftvButIgnoreUnions) envs
            State.modify $ \c -> c { cuckedUnionInstantiation = Map.insertWith (<>) cuckuni instantiatedEnvs c.cuckedUnionInstantiation }
      -- check if we previously encountered this environment and it contained TVars that weren't mapped.
      cuckedMemo <- State.gets cuckedUnions
      case isMemoed tunion.unionID cuckedMemo of
        Just mu -> do
          addCuckedUnionEnvs tunion mu
          pure mu
        Nothing -> do

          -- it wasn't... but it's still possible.
          tunion' <- sequenceA tunion
          let unionFTV = foldMap ftvButIgnoreUnions tunion'
          if not (null unionFTV)
            then do
              -- had TVars -> remember it.
              ieu <- memo' cuckedUnions (\mem mctx -> mctx { cuckedUnions = mem }) tunion'.unionID $ \eid _ -> do
                let menvs = tunion'.union
                case menvs of
                  -- literally impossible as there would be no FTVs otherwise...
                  [] -> error $ Def.printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ IM.EnvUnion { IM.unionID = eid, IM.union = e :| es }

              addCuckedUnionEnvs tunion ieu
              pure ieu

            else
              -- normal union - all TVars mapped. safe to memoize.
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) tunion' $ \tunion'' _ -> do
                let menvs = tunion''.union
                case menvs of
                  [] -> error $ Def.printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    nuid <- newUnionID
                    pure $ IM.EnvUnion { IM.unionID = nuid, IM.union = e :| es }


mEnv :: T.EnvF (Type IM) -> IM.Env
mEnv = \case
  T.RecursiveEnv {} -> error "recursive env not handled"
  T.Env eid vs _ _ -> IM.Env eid $ vs <&> undefined


-- NOTE: This is only used to correctly monomorphize the function this env belongs to. It does not actually monomorphize envs in types.
mEnvTypes' :: T.EnvF (Type TC) -> Context IM.EnvTypes
mEnvTypes' env = do
  env' <- traverse mType env
  pure $ mEnvTypes env'



-- TODO: modify?
mEnvTypes :: T.EnvF (Type IM) -> IM.EnvTypes
mEnvTypes = \case
    T.RecursiveEnv eid isEmpty -> error "I think recursive env cannot be monomorphised."  -- IM.RecursiveEnv eid isEmpty

    -- xdddd, we don't create a new env id when it has shit inside.
    -- NOTE: 21.05.25: I don't think it's relevant anymore?
    T.Env eid params _ _ | not (null (foldMap (\(_, _, t) -> ftvButIgnoreUnions t) params)) -> do
      -- we have to preserve the original ID to later replace it with all the type permutations.
      IM.EnvTypes eid $ params <&> \(_, _, t) -> t

    T.Env eid params _ _ -> do
      IM.EnvTypes eid $ params <&> \(_, _, t) -> t



------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , tvarInsts :: Map (TVar TC) (Map (ClassDef TC) (InstDef TC))  -- TODO: smell.
  , memoFunction :: Memo (Function TC, [Type IM], Type IM, IM.EnvTypes) (Function IM)
  , memoDatatype :: Memo (DataDef TC, TypeMap) (DataDef IM, Map (DataCon TC) (DataCon IM))
  , memoEnv :: Memo (T.EnvF (Type TC, Type IM)) IM.Env
  , memoUnion :: Memo (T.EnvUnionF (Type IM)) IM.EnvUnion
  , memoMember :: Memo (DataDef IM, Def.MemName) Def.UniqueMem

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo Def.UnionID IM.EnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  , cuckedUnionInstantiation :: Map IM.EnvUnion (Set (T.EnvF (Type IM)))  -- this one is to track all environments which get instantiated for this union.
  -- also, this can be done in the same way as subst - would even require us to track less state.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: Map Def.EnvID (Set EnvUse)  -- NOTE: FUTURE TYPECHECK
  -- i think it's also not needed now.

  , usedVars :: Set (T.Variable, Type IM)  -- FROM RemoveUnused. this thing tracks which (monomorphized) variables were used. remember that it should not carry between scopes.-- NOTE: FUTURE TYPECHECK (also unused now)
  -- added Set TVar to fix the nested function environment expansion problem. Let's see if it works.

  , classInstantiationAssociations :: T.ClassInstantiationAssocs
  , currentLevel :: Int  -- HACK: it's for knowing when instances should be local or not.
  }
type Context = StateT Context' IO

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

  , usedVars = mempty
  , classInstantiationAssociations = mempty
  , currentLevel = 0  -- BAD
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
  TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip unions munions)


-- ahhh, i hate it. TODO: try to figure out if there is a way to do it without doing this time consuming and error prone mapping.
mapType :: Type TC -> Type IM -> TypeMap
mapType tt mt = case (project tt, project mt) of
  (TFun tu tts tret, TFun mu mts mret) -> mapTypes tts mts <> mapType tret mret <> TypeMap mempty (Map.singleton tu.unionID mu)
  (TCon _ tts tus, TCon _ mts mus) -> mapTypes tts mts <> TypeMap mempty (Map.fromList $ zip (T.unionID <$> tus) mus)
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


withEnvContext :: Map (T.EnvF (Type IM)) IM.Env -> Map IM.EnvID (Set EnvUse) -> Map IM.EnvUnion (Set (T.EnvF (Type IM))) -> EnvContext a -> IO a
withEnvContext menvs allInstantiations cuckedUnionInstantiations x = fst <$> RWS.evalRWST x envUse envMemo
  where
    envUse = EnvContextUse
      { allInsts = allInstantiations
      , envs = menvs
      , cuckedUnionInsts = cuckedUnionInstantiations
      }

    envMemo = EnvMemo
      { memoIDatatype = emptyMemo
      }


mfAnnStmts :: [AnnStmt IM] -> EnvContext [AnnStmt M]
mfAnnStmts stmts = fmap catMaybes $ for stmts $ cata $ \(O (Annotated anns stmt)) -> do
  stmt' <- bitraverse mfExpr id stmt
  let s = pure . Just
  let
    body :: NonEmpty (Maybe (AnnStmt M)) -> NonEmpty (AnnStmt M)
    body bstmts =
      let eliminated = catMaybes $ NonEmpty.toList bstmts
      in case eliminated of
        [] -> Fix (O (Annotated [] Pass)) :| []
        (st:sts) -> st :| sts

  fmap (embed . O . Annotated anns) <$> case stmt' of
    Fun envs -> do
      mfenvs <- traverse (bitraverse mfFunction mfEnvDef) envs
      s $ Fun $ NonEmpty.toList mfenvs

    Pass -> s Pass
    ExprStmt e -> s $ ExprStmt e
    Assignment vid expr -> s $ Assignment vid expr
    Print e -> s $ Print e
    Mutation vid e -> s $ Mutation vid e
    If (IfStmt cond ifTrue elseIfs else') -> s $ If $ IfStmt cond (body ifTrue) (fmap2 body elseIfs) (body <$> else')
    Switch e cases -> fmap (Just . Switch e) $ for cases $ \kase -> do
      mdecon <- mfDecon kase.deconstruction
      pure $ Case { deconstruction = mdecon, caseCondition = kase.caseCondition, caseBody = body kase.caseBody }
    Return e -> do
      me <- mfExpr e
      s $ Return me
    Other _ -> undefined
    Inst _ -> undefined  -- TODO: remove from Common later.

mfDecon :: Decon IM -> EnvContext (Decon M)
mfDecon = cata $ \(N t e) -> do
  mt <- mfType t
  fmap (embed . N mt) $ case e of
    CaseVariable v -> do
      pure $ CaseVariable v

    CaseRecord _ decons -> do
      -- fun unsafe shit.
      let dd = case project mt of
            TCon mdd _ _ -> mdd
            mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %s)" (pp (embed mpt))

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
      menv <- mfEnvDef env
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

    Lit lt -> pure $ Lit lt
    Op l op r -> Op <$> l <*> pure op <*> r
    Call c args -> Call <$> c <*> sequenceA args
    As e t -> As <$> e <*> mfType t

mfVariable :: IM.Variable -> EnvContext M.Variable
mfVariable = \case
  IM.DefinedVariable uv -> pure $ M.DefinedVariable uv
  IM.DefinedFunction fun -> do
    mfun <- mfFunction fun
    pure $ M.DefinedFunction mfun


mfEnvDef :: IM.Env -> EnvContext M.Env
mfEnvDef = \case
  IM.RecursiveEnv eid isEmpty -> error "RECURSIVE ENV YO." -- pure $ M.RecursiveEnv eid isEmpty
  IM.Env eid envContent -> do
    menvContent <- traverse (\(v, l, t) -> mfType t >>= \t' -> (,l,t') <$> mfVariable v) envContent  -- the weird monad shit is so we 
    pure $ M.Env eid menvContent

mfEnv :: T.EnvF (Type IM) -> EnvContext (Maybe M.Env)
mfEnv (T.RecursiveEnv {}) = error "RECURSION. This, with the weird monad shit makes us crash at recursion."
mfEnv env = do
  findEnvs <- RWS.asks envs
  traverse mfEnvDef $ findEnvs !? env

-- mfEnv :: M.IEnvF a -> EnvContext M.Env
-- mfEnv (M.IRecursiveEnv eid isEmpty) = error "RECURSIVENESS ASDASD"  -- pure $ M.RecursiveEnv eid isEmpty
-- mfEnv (M.IEnv eid _) = do
--   envInsts <- RWS.asks allInsts
--   case envInsts !? eid of
--     Just envs | length envs == 1 -> do
--       case head (Set.toList envs) of
--         EnvUse _ (M.IEnv eeid vars) -> do
--           usage' <- fmap fold
--             $ traverse (\case
--               Left  eid -> expandVars eid
--               Right var -> pure (Set.singleton var))
--             $ Set.toList usage
--           let vars' = filter (\(v, _, _) -> Set.member v usage') vars
--           vars'' <- traverse (\(v, loc, t) -> liftA2 (,loc,) (mfVariable v) (mfType t)) vars'
--           pure $ M.Env eeid vars''

--         EnvUse _ (M.IRecursiveEnv reid isEmpty) ->
--           -- pure $ M.RecursiveEnv reid isEmpty
--           error "DUPSKO!"

--     _ -> error $ "Bruh. Muh shit code is shit."

-- expandVars :: EnvID -> EnvContext (Set M.IVariable)
-- expandVars eid = do
--   envInsts <- RWS.asks allInsts
--   case envInsts !? eid of
--     Nothing -> pure mempty
--     Just set | null set -> pure mempty
--     Just set -> do
--       let EnvUse _ _ = head $ Set.toList set
--       fmap fold $ traverse (\case
--           Left  eid' -> expandVars eid'
--           Right var  -> pure (Set.singleton var)
--         ) $ Set.toList usage


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

  TO (IM.TVar tv) -> error $ Def.printf "[COMPILER ERROR]: TVar %s not matched - types not appied correctly?" (pp tv)



mfUnion :: IM.EnvUnion -> EnvContext M.EnvUnion
mfUnion union = do
  cuckedUnions <- RWS.asks cuckedUnionInsts
  mappedEnvs <- case cuckedUnions !? union of
      -- here should be no ftvs.
      Nothing -> fmap concat $ for (NonEmpty.toList union.union) $ \env -> do
          Def.ctxPrint' $ Def.printf "???: %s ?? %s" (pp env) (show $ null (foldMap ftvButIgnoreUnions env))
          menv <- mfEnv env
          Def.ctxPrint' $ Def.printf "NOFTV: %s => %s" (pp env) (maybe "???" pp menv)
          pure $ maybeToList menv

      -- here should also be no ftvs in the NEW UNION
      -- these were cuckedUnions
      Just envs -> do
        -- NOTE: i did catMaybes because mfEnv returns this. I don't think it's necessary anymore.
        menvs <- fmap catMaybes $ traverse mfEnv $ Set.toList envs
        pure menvs

  -- NOTE: I HATE THIS FUCKING ERROR LIKE YOU WOULDN'T BELIEVE.
  Def.ctxPrint' $ Def.printf "mfUnion: %s => %s" (pp union) (Def.encloseSepBy "{" "}" ", " $ pp <$> mappedEnvs)
  let mUsedEnvs = case mappedEnvs of
        [] -> error $ "[COMPILER ERROR] Empty union (" <> show union.unionID <> ") encountered... wut!??!??!?!? Woah.1>!>!>!>!>>!"
        (x:xs) -> x :| xs

  pure $ M.EnvUnion { M.unionID = union.unionID, M.union = mUsedEnvs }



-- TODO: smell. this seems to expand environments only for functions, which means it's only used for EnvDefs.
--       it's because each function usage is separate in the environment, so we don't have to expand them.
expandEnvironments :: [Def.EnvID] -> EnvContext [(Function M, M.Env)]
expandEnvironments envIDs = do
  envInsts <- RWS.asks allInsts
  Def.ctxPrint' $ Def.printf "expand: %s\n%s" (Def.ppList pp envIDs) (Def.ppMap $ Map.toList envInsts <&> \(eid, euse) -> (pp eid, Def.ppList (\(EnvUse mfn env) -> case mfn of { Just fn -> "(" <> pp fn.functionDeclaration.functionId <>  ", " <> pp (IM.envID env) <> ")"; Nothing -> pp (IM.envID env) }) $ Set.toList euse))
  fmap concat $ for envIDs $ \envID ->
    case envInsts !? envID of
      Just envs -> do
        traverse (bitraverse mfFunction mfEnvDef) $ mapMaybe (\(EnvUse fn env) -> fn <&> (,env)) $ Set.toList envs
      Nothing -> pure []


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
mfFunction fun = do
  Def.ctxPrint' $ Def.printf "MF function %s" (pp fun.functionDeclaration.functionId)
  Def.ctxPrint pp fun

  -- just map everything.
  let fundec = fun.functionDeclaration
  env <- mfEnvDef fundec.functionEnv
  params <- traverse (bitraverse mfDecon mfType) fundec.functionParameters
  ret <- mfType fundec.functionReturnType

  let mfundec = FD { functionEnv = env, functionId = fundec.functionId, functionParameters = params, functionReturnType = ret, functionOther = () }

  body <- mfAnnStmts $ NonEmpty.toList fun.functionBody
  let completedBody = case body of
        [] ->
          -- TODO: we need to automatically insert return values based on flow analysis (but that should be part of typechecking?)
          let pass = Fix (O (Annotated [] Pass))
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
        _ -> error $ Def.printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (pp imt)

  -- mtypes <- traverse mfType ttypes
  munions <- traverse mfUnion imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  pure mdc



-- ftvEnvButIgnoreUnions :: M.IEnv -> Set T.TVar
-- ftvEnvButIgnoreUnions = \case
--   M.IRecursiveEnv _ _ -> Set.empty
--   M.IEnv _ ts -> foldMap (\(_, _, t) -> ftvButIgnoreUnions t) ts

ftvButIgnoreUnionsInEnv :: IM.Env -> Set IM.TVar
ftvButIgnoreUnionsInEnv (IM.Env _ vs) = (foldMap . foldMap) ftvButIgnoreUnions vs
ftvButIgnoreUnionsInEnv (IM.RecursiveEnv {}) = mempty

ftvButIgnoreUnions :: Type IM -> Set IM.TVar
ftvButIgnoreUnions = cata $ \case
  TO (IM.TVar tv) -> Set.singleton tv
  TCon _ ts _ -> mconcat ts
  TFun _ args ret -> mconcat args <> ret

ftvTButIgnoreUnions :: Type TC -> Set (TVar TC)
ftvTButIgnoreUnions = cata $ \case
  TO (T.TVar tv) -> Set.singleton tv
  TCon _ ts _ -> mconcat ts
  TFun _ args ret -> mconcat args <> ret
  TO (T.TyVar _) -> error "Encountered a tyvar."



filterEnvs :: [T.EnvF a] -> EnvContext [T.EnvF a]
filterEnvs envs = do
  envIds <- RWS.asks allInsts
  pure $ filter (\e -> T.envID e `Map.member` envIds) envs


expectIDataDef :: Type IM -> DataDef IM
expectIDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %s)" (pp (embed mpt))

expectDataDef :: Type M -> DataDef M
expectDataDef mt = case project mt of
    TCon mdd _ _ -> mdd
    mpt -> error $ Def.printf "Ayo, member type is not a data definition, wut???? (type: %s)" (pp (embed mpt))



-------------------------
-- Step 2 Type defs!
------------------------


type EnvContext = RWST EnvContextUse () EnvMemo IO  -- TEMP: IO temporarily for debugging. should not be used for anything else.
-- Stores environment instantiations. 
--   NOTE: In the future, maybe more stuff (like which constructors were used!)
data EnvContextUse = EnvContextUse
  { allInsts :: Map IM.EnvID (Set EnvUse)
  , envs     :: Map (T.EnvF (Type IM)) IM.Env
  , cuckedUnionInsts :: Map IM.EnvUnion (Set (T.EnvF (Type IM)))
  }

data EnvUse = EnvUse (Maybe (Function IM)) IM.Env

instance Eq EnvUse where
  EnvUse _ le == EnvUse _ re = le == re

instance Ord EnvUse where
  EnvUse _ le `compare` EnvUse _ re = le `compare` re


newtype EnvMemo = EnvMemo
  { memoIDatatype :: Memo (DataDef IM, [M.EnvUnion]) (DataDef M, Map (DataCon IM) (DataCon M))
  }




----------------------
-- UNRELATED MISC
----------------------

instance Foldable ((,,) a b) where
  foldr f x (_, _, y) = f y x

instance Traversable ((,,) a b) where
  traverse f (a, b, x) = (a, b,) <$> f x
