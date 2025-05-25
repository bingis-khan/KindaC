{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- we implement basic instances (Foldable, Travesable) for Tuple.

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}  -- for HLINT kekek
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant pure" #-}  -- this is retarded. it sometimes increases readability with that extra pure.
module Mono (mono) where

import AST.Common (Annotated (..), UniqueVar (..), UniqueCon (..), UniqueType (..), UnionID (..), EnvID (..), VarName (..), Locality (..), (:.) (..), printf, ctx, ppMap, ppLines, ctxPrint', ctxPrint, phase, traverse2, fmap2, MemName, UniqueMem (..), sequenceA2, ppList, ppEnvID, ppVar, ctxPrint'', UniqueClassInstantiation)
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
import AST.Typed (defaultEmpty)
import Data.String (fromString)
import Data.List (find)
import Data.Bool (bool)




------ Monomorphization consists of two steps:
--  Step 1: Perform normal monomorphization (however, you won't be able to compile escaped TVars).
--  Step 2: Replace escaped TVars with each instantiation of them. (TODO: this is bad, but necessary. maybe do it in RemoveUnused somehow?)


mono :: T.ClassInstantiationAssocs -> [T.AnnStmt] -> IO M.Module
mono cia tmod = do
  liftIO $ ctxPrint' $ printf "CIA: %s" (Common.ppMap $ fmap (bimap (fromString . show) (Common.encloseSepBy "[" "]" ", " . fmap (Common.ppTup . bimap T.tType (Common.ppTup . bimap (Common.encloseSepBy "[" "]" ", " . fmap T.tType) (\ifn -> Common.ppVar Local ifn.instFunction.functionDeclaration.functionId))))) $ fmap2 (fmap $ \(l, r, _) -> (l, r)) $ Map.toList cia)

  -- Step 1: Just do monomorphization with a few quirks*.
  (mistmts, monoCtx) <- flip State.runStateT (startingContext cia) $ do
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
  ctxPrint (Common.ppMap . fmap (bimap Common.ppEnvID (Common.encloseSepBy "[" "]" ", " . fmap (\(EnvUse _ env) -> M.mtIEnvDef env) . Set.toList)) . Map.toList) monoCtx.envInstantiations

  phase "Monomorphisation (just envs)"
  ctxPrint (Common.ppMap . fmap (bimap M.mtEnv M.mtIEnvDef) . Map.toList) envs

  phase "Monomorphisation (first part)"
  ctxPrint M.mtStmts mistmts


  -- Step 2 consists of:
  -- 1. substitute environments
  -- 2. check function usage and remove unused EnvDefs

  mmod <- withEnvContext envs monoCtx.envInstantiations monoCtx.cuckedUnionInstantiation $ do
    mstmts <- mfAnnStmts mistmts
    pure $ M.Mod { M.toplevelStatements = mstmts }

  pure mmod



mStmts :: Traversable f => f T.AnnStmt -> Context (f M.AnnIStmt)
mStmts = traverse mAnnStmt

mAnnStmt :: T.AnnStmt -> Context M.AnnIStmt
mAnnStmt = cata (fmap embed . f) where
  f :: (:.) Annotated (T.StmtF T.Expr) (Context M.AnnIStmt) -> Context ((:.) Annotated (M.StmtF M.IncompleteEnv M.IExpr) M.AnnIStmt)
  f (O (Annotated ann stmt)) = do
    stmt' <- bitraverse mExpr id stmt
    let
      mann, noann :: b a -> Context ((:.) Annotated b a)
      mann = pure . O . Annotated ann
      noann = pure . O . Annotated []

    -- NOTE: this is just remapping.......
    case stmt' of
      T.Pass -> mann M.Pass
      T.ExprStmt expr -> mann $ M.ExprStmt expr
      T.Assignment vid expr -> mann $ M.Assignment vid expr
      T.Print expr -> mann $ M.Print expr
      T.Mutation vid loc expr -> mann $ M.Mutation vid loc expr
      T.If cond ifTrue elseIfs else' -> mann $ M.If cond ifTrue elseIfs else'
      T.Switch switch cases -> do
        mcases <- traverse mCase cases
        mann $ M.Switch switch mcases
      T.Return ete -> mann $ M.Return ete
      T.EnvDef fn -> do
        let env = fn.functionDeclaration.functionEnv
        let envID = T.envID env
        envInsts <- State.gets envInstantiations

        let currentEnvUses = fromMaybe mempty $ envInsts !? envID
        let defs = Set.toList currentEnvUses <&> \(EnvUse (Just fn) env) -> (fn, env)

        noann $ case defs of
          [] -> M.Pass
          (x:xs) -> M.EnvDef $ x :| xs

      T.InstDefDef inst -> do
        envInsts <- State.gets envInstantiations

        let envs = flip concatMap inst.instFunctions $ \fn ->
              let env = fn.instFunction.functionDeclaration.functionEnv
                  envID = T.envID env
                  currentEnvUses = fromMaybe mempty $ envInsts !? envID
                  defs = Set.toList currentEnvUses <&> \(EnvUse (Just fn) env) -> (fn, env)
              in  defs

        noann $ case envs of
          [] -> M.Pass
          (x:xs) -> M.EnvDef $ x :| xs



mExpr :: T.Expr -> Context M.IExpr
mExpr = cata $ fmap embed . \(T.TypedExpr t expr) -> do
  mt <- mType t
  mexpr <- case expr of
    T.Lam env args ret -> do
      margs <- traverse2 mType args
      (mret, menv) <- withEnv Nothing env ret

      pure $ M.Lam menv margs mret

    otherExpr -> do
      motherExpr <- sequenceA otherExpr
      case motherExpr of
        T.Lam {} -> error "Should be handled earlier."

        T.Var locality v -> do
          mv <- variable v (t, mt)
          State.modify $ \c -> c { usedVars = Set.insert (T.asUniqueVar v, mt) c.usedVars }

          newLocality <- case v of
                T.DefinedClassFunction _ _ self uci -> do
                  -- NOTE: ANOTHER COPYPASTA TO KNOW THE OG INSTANCE OF THIS FUNCTION.
                  ucis <- State.gets classInstantiationAssociations
                  mself <- mType self
                  (ifnts, ivfn) <- case ucis !? uci of
                        Just ts -> do
                          candidates <- traverse (bitraverse mType pure) $ ts <&> \(l, r, _) -> (l, r)
                          case find ((==mself) . fst) candidates of
                            Just (_, (l, r)) -> pure (l, r)
                            Nothing -> error "aisndlknsadlkjsad"
                        Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"
                  let vfn = ivfn.instFunction
                  let (T.Env _ _ _ level) = vfn.functionDeclaration.functionEnv
                  cl <- State.gets currentLevel
                  pure $ if level == cl then Local else FromEnvironment

                _ -> pure locality

          pure $ M.Var newLocality mv

        T.Con eid c -> do
          mc <- constructor c t

          -- don't forget to register usage. (for codegen)
          void $ withEnv Nothing (T.Env eid [] mempty 0) (pure ())

          pure $ M.Con mc

        T.RecCon _ inst -> do
          let dd = expectIDataDef mt
          inst' <- for inst $ \(mem, memt) -> do
            ut <- member (dd, mem)
            pure (ut, memt)

          pure $ M.RecCon dd inst'

        T.RecUpdate me upd -> do
          let dd = expectIDataDef (M.expr2type me)
          upd' <- for upd $ \(mem, meme) -> do
            ut <- member (dd, mem)
            pure (ut, meme)

          pure $ M.RecUpdate dd me upd'

        T.MemAccess me memname -> do
          let dd = expectIDataDef (M.expr2type me)
          um <- member (dd, memname)
          pure $ M.MemAccess me um

        T.Lit lit -> pure $ M.Lit lit
        T.Op l op r -> pure $ M.Op l op r
        T.Call e args -> pure $ M.Call e args
        T.As (Fix (M.TypedExpr _ e)) _ -> do
          -- Ignore 'as' by unpacking the variable and passing in the previous expression.
          pure e

  pure $ M.TypedExpr mt mexpr

withEnv :: Maybe M.IFunction -> T.Env -> Context a -> Context (a, M.IEnv)
withEnv mfn env cx = do
  let showOldVars ovs = Common.ppList (Common.ppTup3 . (\(l, m, r) -> (ppVar Local l, M.mtType m, Common.ppSet T.tTVar $ Set.toList r))) $ Set.toList ovs
  let printUsedVarsState uvType uvTypeTag uvs = ctxPrint' $ printf "%s%s: USED VARS %s WITH ENV%s: %s" (Common.ppEnvID $ T.envID env) (uvTypeTag :: Common.Context) (uvType :: Common.Context) (case mfn of { Nothing -> "" :: Common.Context; Just fn -> fromString $ printf " (%s)" $ ppVar Local fn.functionDeclaration.functionId }) (showOldVars uvs)

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
                        Just ts -> do
                          candidates <- traverse (bitraverse mType pure) $ ts <&> \(l, r, _) -> (l, r)
                          case find ((==mself) . fst) candidates of
                            Just (_, (l, r)) -> pure (l, r)
                            Nothing -> error "aisndlknsadlkjsad"
                        Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"
                  let vfn = ivfn.instFunction
                  let T.Env cureid _ _ instanceLevel = vfn.functionDeclaration.functionEnv
                  if currentLevel < instanceLevel
                    then do
                      let envs = case project tt of
                            T.TFun union _ _ -> union.union
                            _ -> error "Immmmmmmpossible"

                          tryLocalizeEnv (T.Env _ envContent _ _) = sequenceA $ flip mapMaybe envContent $ \(vEnv, _, tEnv) -> 
                              locs !? T.asProto vEnv <&> \newLoc -> do
                                mtEnv <- mType tEnv
                                mvEnv <- variable vEnv (tEnv, mtEnv)
                                li <- needsLateInitialization vEnv
                                pure (mvEnv, newLoc, li, mtEnv)
                          tryLocalizeEnv _ = error "impossssssible"

                      instanceEnv <- fmap concat $ traverse tryLocalizeEnv $ filter ((==cureid) . T.envID) envs
                      ctxPrint' $ printf "LOCALITIES of %s->%s:\n%s" (Common.ppEnvID oldEID) (Common.ppEnvID newEID) $ Common.ppMap $ fmap (bimap (Common.ppVar Local . (\case { T.PDefinedVariable uv -> uv; T.PDefinedFunction fn -> fn.functionDeclaration.functionId; T.PDefinedClassFunction (T.CFD _ uv _ _) -> uv })) (fromString . show)) $ Map.toList locs
                      ctxPrint (Common.ppList T.tEnv) envs
                      ctxPrint (Common.ppList $ \(v, _, _, _) -> Common.ppVar Local $ M.asUniqueVar v) instanceEnv
                      pure instanceEnv
                    else
                      pure [(v', l, li, mt)]


              _ -> do
                pure [(v', l, li, mt)]
      menvContent <- traverse toEnvVar envContent
      pure $ M.IDEnv newEID $ concat menvContent

    T.RecursiveEnv {} -> error "SHOULD NOT HAPPEN."  -- pure $ M.IDRecursiveEnv eid isEmpty


  ctxPrint' $ printf "%sM: %s =WITH ENV%s=> %s" (Common.ppEnvID $ T.envID env) (T.tEnv env) (case mfn of { Nothing -> "" :: Common.Context; Just fn -> fromString $ printf " (%s)" $ ppVar Local fn.functionDeclaration.functionId }) (M.mtIEnvDef menv)
  -- registerEnvMono mfn (T.envID env) menv mempty

  pure (x, menv)

needsLateInitialization :: T.Variable -> Context M.LateInit
needsLateInitialization = const (pure False)

findUsedVarsInExpr :: T.Expr -> Set (T.Variable, T.Type)
findUsedVarsInExpr = cata $ \(T.TypedExpr t expr) -> case expr of
  T.Var _ v -> Set.singleton (v, t)
  e -> fold e

findUsedVarsInFunction :: Foldable t => t T.AnnStmt -> Set (T.Variable, T.Type)
findUsedVarsInFunction = foldMap $ cata $ bifold . first findUsedVarsInExpr . T.deannAnnStmt

mCase :: T.Case M.IExpr M.AnnIStmt -> Context M.ICase
mCase kase = do
  decon <- mDecon kase.deconstruction
  pure $ M.Case decon kase.caseCondition kase.body

mDecon :: T.Decon -> Context M.IDecon
mDecon = cata $ fmap embed . \case
  T.CaseVariable t uv -> do
    mt <- mType t
    pure $ M.CaseVariable mt uv

  T.CaseRecord t _ args -> do
    mt <- mType t

    -- fun unsafe shit.
    let dd = case project mt of
          M.ITCon mdd _ _ -> mdd
          mpt -> error $ printf "Ayo, member type is not a data definition, wut???? (type: %s)" (M.mtType (embed mpt))

    margs <- for args $ \(mem, decon) -> do
      mdecon <- decon
      um <- member (dd, mem)
      pure (um, mdecon)

    pure $ M.CaseRecord mt dd margs

  T.CaseConstructor t dc args -> do
    mt <- mType t
    mdc <- constructor dc t
    margs <- sequenceA args
    pure $ M.CaseConstructor mt mdc margs



variable :: T.Variable -> (T.Type, M.IType) -> Context M.IVariable  -- NOTE: we're taking in both types, because we need to know which TVars were mapped to types and which to other tvars.
variable (T.DefinedVariable uv) _ = pure $ M.DefinedVariable uv
variable (T.DefinedFunction vfn snapshot assocs) (instType, et) = do
  ctxPrint' $ "in function: " <> show vfn.functionDeclaration.functionId.varName.fromVN

  -- male feminists are seething rn
  let (tts, tret) = case project et of
        M.ITFun _ mts mret -> (mts, mret)
        _ -> undefined


  -- DEBUG: print a non-memoized type. This was used to check memoization errors.
  ctxPrint' $ printf "Decl (nomemo): %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> tts) (M.mtType tret)

  let tassocs = vfn.functionDeclaration.functionAssociations <&> \(T.FunctionTypeAssociation _ t _ _) -> t
  massocs <- traverse mType assocs

  -- creates a type mapping for this function.
  let typemap = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret <> mapTypes tassocs massocs

  let fd = vfn.functionDeclaration
  let genType = Fix $ T.TFun undefined (snd <$> fd.functionParameters) fd.functionReturnType
  let tvtvMap = cringeGetReinstantiatedVariables fd.functionId genType instType
  withClassInstanceAssociations fd.functionClassInstantiationAssociations
    -- $ withTVarInsts tvtvMap snapshot fd.functionId typemap
    $ withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map though albeit.
    menv <- mEnv' vfn.functionDeclaration.functionEnv

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv) $ \(tfn, ts, ret, _) addMemo -> mdo

      uv <- newUniqueVar tfn.functionDeclaration.functionId

      params <- flip zip ts <$> traverse (mDecon . fst) tfn.functionDeclaration.functionParameters
      let fundec = M.FD env uv params ret :: M.IFunDec


      -- DEBUG: when in the process of memoization, show dis.
      ctxPrint' $ printf "Decl: %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> ts) (M.mtType ret)
      ctxPrint' $ printf "M function: %s" (Common.ppVar Local fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = M.Function { M.functionDeclaration = fundec, M.functionBody = body } :: M.IFunction
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
    pure $ M.DefinedFunction fn

variable (T.DefinedClassFunction cfd@(T.CFD cd _ cfdParams cfdRet) snapshot self uci) (instType, et) = do
  -- male feminists are seething rn
  let (tts, tret) = case project et of
        M.ITFun _ mts mret -> (mts, mret)
        _ -> undefined


  -- FIX: Fix for class functions not instantiating tvars, but it's bad.
  ctxPrint' $ printf "Self: %s" (T.tType self)
  ucis <- State.gets classInstantiationAssociations
  mself <- mType self
  (ifnts, ivfn) <- case ucis !? uci of
        Just ts -> do
          candidates <- traverse (bitraverse mType pure) $ ts <&> \(l, r, _) -> (l, r)
          case find ((==mself) . fst) candidates of
            Just (_, (l, r)) -> pure (l, r)
            Nothing -> error "aisndlknsadlkjsad"
        Nothing -> error "AOSJDOJSADOJSAJODJSAOJDASODSAJ"
  let vfn = ivfn.instFunction

  ctxPrint' $ printf "Variable: %s.\n\tT Type: (%s) -> %s\n\tM Type: %s\n" (Common.ppVar Local vfn.functionDeclaration.functionId) (Common.sepBy ", " $ T.tType . snd <$> vfn.functionDeclaration.functionParameters) (T.tType vfn.functionDeclaration.functionReturnType) (M.mtType et)

  ctxPrint' $ "in (class) function: " <> show vfn.functionDeclaration.functionId.varName.fromVN


  -- creates a type mapping for this function.
  let tassocs = vfn.functionDeclaration.functionAssociations <&> \(T.FunctionTypeAssociation _ t _ _) -> t

  massocs <- traverse mType ifnts


  ctxPrint' $ printf "t assocs: %s\nm assocs: %s\n" (Common.sepBy ", " $ T.tType <$> tassocs) (Common.sepBy ", " $ M.mtType <$> massocs)

  let typemap = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret
        <> mapTypes tassocs massocs  -- FIX: this should be `mapTypes tassocs massocs`, but I don't know how to pass them here, so I'll use the environment instead.

  let fd = vfn.functionDeclaration
  let genType = Fix $ T.TFun undefined (snd <$> fd.functionParameters) fd.functionReturnType
  let tvtvMap = cringeGetReinstantiatedVariables fd.functionId genType instType
  withClassInstanceAssociations fd.functionClassInstantiationAssociations
    -- $ withTVarInsts tvtvMap snapshot fd.functionId typemap
    $ withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map though albeit.
    menv <- mEnv' vfn.functionDeclaration.functionEnv

    -- see definition of Context for exact purpose of these parameters.
    fn <- flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv) $ \(tfn, ts, ret, _) addMemo -> mdo

      uv <- newUniqueVar tfn.functionDeclaration.functionId

      params <- flip zip ts <$> traverse (mDecon . fst) tfn.functionDeclaration.functionParameters
      let fundec = M.FD env uv params ret :: M.IFunDec


      -- DEBUG: when in the process of memoization, show dis.
      ctxPrint' $ printf "Decl: %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> ts) (M.mtType ret)
      ctxPrint' $ printf "M function: %s" (Common.ppVar Local fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = M.Function { M.functionDeclaration = fundec, M.functionBody = body } :: M.IFunction
      addMemo fn
      (body, env) <- withEnv (Just fn) tfn.functionDeclaration.functionEnv $ do
        mStmts tfn.functionBody

      pure fn

    registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) fn.functionDeclaration.functionEnv mempty
    pure $ M.DefinedFunction fn

gatherInstsFromEnvironment :: M.IVariable -> Set (UniqueVar, M.IType)
gatherInstsFromEnvironment = \case
  M.DefinedFunction fn -> case fn.functionDeclaration.functionEnv of
    M.IDRecursiveEnv _ _ -> mempty
    M.IDEnv _ vars -> flip foldMap vars $ \case
      (envVar, Local, _, t) -> Set.insert (M.asUniqueVar envVar, t) (gatherInstsFromEnvironment envVar)
      (envVar, _, _, t) -> Set.singleton (M.asUniqueVar envVar, t)
  _ -> mempty


-- CRINGE: FUCK.
-- EDIT: 29.04.25 WHAT IS THIS????
cringeGetReinstantiatedVariables :: UniqueVar -> T.Type -> T.Type -> Map T.TVar T.TVar
cringeGetReinstantiatedVariables binding gen inst = case (project gen, project inst) of
  (T.TVar to, T.TVar from) | to.binding == Common.BindByVar binding -> Map.singleton from to

  (T.TFun _ lts lt, T.TFun _ rts rt) -> fold (zipWith (cringeGetReinstantiatedVariables binding) lts rts) <> (cringeGetReinstantiatedVariables binding) lt rt
  (T.TCon _ lts _, T.TCon _ appts _) -> fold $ zipWith (cringeGetReinstantiatedVariables binding) lts appts

  _ -> mempty

-- I assume it's a quick mapping for classes. TODO: refactor nigga.
cringeMapClassType :: T.ClassType -> M.IType -> Map T.TVar T.DataDef
cringeMapClassType lpt rpt = case (project lpt, project rpt) of
  (T.CTVar tv, M.ITCon dd _ _)-> Map.singleton tv dd.ogDataDef
  (T.CTVar {}, M.ITFun {}) -> mempty
  (T.Self, _) -> mempty

  (T.CTFun _ lts lt, M.ITFun _ rts rt) -> fold (zipWith cringeMapClassType lts rts) <> cringeMapClassType lt rt
  (T.CTCon _ lts, M.ITCon _ appts _) -> fold $ zipWith cringeMapClassType lts appts

  _ -> undefined



-- Registers a single environment monomorphization. later used to track which environments monomoprhised to what.
-- TODO: seems to be unneeded now.
registerEnvMono :: Maybe M.IFunction -> EnvID -> M.IEnv -> Set (UniqueVar, M.IType, Set T.TVar) -> Context ()
registerEnvMono mvar oldEID nuEnv _ | null (foldMap ftvButIgnoreUnions nuEnv) = do
  State.modify $ \mctx -> mctx { envInstantiations = Map.insertWith (<>) (M.idenvID nuEnv) (Set.singleton (EnvUse mvar nuEnv)) (Map.insertWith (<>) oldEID (Set.singleton (EnvUse mvar nuEnv)) mctx.envInstantiations) }

-- CHECK:
-- ignore when the environment has TVars...???? i guess... it shouldn't happen anyway, right?
registerEnvMono _ _ _ _ = pure ()



constructor :: T.DataCon -> T.Type -> Context M.IDataCon
constructor tdc@(T.DC dd@(T.DD ut _ _ _) _ _ _) et = do
  -- Extract type. Pretty bad, but should just work.
  let (ttypes, tunions) = case project et of
        T.TCon _ tts unions -> (tts, unions)
        T.TFun _ _ (Fix (T.TCon _ tts unions)) -> (tts, unions)

        -- COMPILER ERROR
        _ -> error $ printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (T.tType et)

  mtypes <- traverse mType ttypes

  noEmptyUnions <- hideEmptyUnions tunions
  munions <- (mUnion . fmap mType) `traverse2` noEmptyUnions  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
  -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  let tm = typeMapFromDataDef dd mtypes munions
  (_, dcQuery) <- mDataDef (dd, tm)
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ printf "[COMPILER ERROR]: Failed to query an existing constructor for type %s.\n TypeMap: %s\n(applied TVs: %s, applied unions: %s) -> (applied TVs: %s, applied unions: %s)" (Common.ppTypeInfo ut) (ppTypeMap tm) (Common.ppSet T.tType ttypes) (Common.ppSet (T.tEnvUnion . fmap T.tType) tunions) (Common.ppSet M.mtType mtypes) (Common.ppSet (maybe "?" (M.tEnvUnion . fmap (ppEnvID . T.envID))) munions)

  pure mdc

member :: (M.IDataDef, MemName) -> Context UniqueMem
member = memo memoMember (\mem s -> s { memoMember = mem }) $ \(_, memname) _ -> do
  -- TODO: maybe this should be the same as `constructor`, where I just mDataType and find the member?
  --  at least for consistency. also, there won't be incorrect members! but right now, I'll try like this.
  mkUniqueMember memname


mType :: T.Type -> Context M.IType
mType = cata $ \case
    T.TCon dd pts unions -> do
      params <- sequenceA pts

      noEmptyUnions <- hideEmptyUnions unions
      munions <- mUnion `traverse2` noEmptyUnions  -- ISSUE(unused-constructor-elimination): very hacky, but should work. I think it echoes the need for a datatype that correctly represents what we're seeing here - a possible environment definition, which might not be initialized.
      -- we need to represent this shit differently.

      let tm = typeMapFromDataDef dd params munions
      (mdd, _) <- mDataDef (dd, tm)
      let mt = Fix $ M.ITCon mdd params (catMaybes munions)
      pure mt

    T.TFun union params ret -> do
      union' <- mUnion union
      params' <- sequenceA params
      ret' <- ret

      pure $ Fix $ M.ITFun union' params' ret'

    T.TVar tv -> retrieveTV tv

    T.TyVar tv -> error $ printf "[COMPILER ERROR]: Encountered TyVar %s." (T.tTyVar tv)


-- ISSUE(unused-constructor-elimination): yeah, this is bad. we also need to remember to map the empty unions (through type map.)
hideEmptyUnions :: [T.EnvUnionF a] -> Context [Maybe (T.EnvUnionF a)]
hideEmptyUnions unions = do
  TypeMap _ mus <- State.gets tvarMap
  pure $ flip fmap unions $ \u -> if Map.member u.unionID mus || not (T.isUnionEmpty u)
    then Just u
    else Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (T.DataDef, TypeMap) -> Context (M.IDataDef, Map T.DataCon M.IDataCon)
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(tdd@(T.DD ut (T.Scheme tvs _) tdcs ann), tm@(TypeMap tvmap unionMap)) addMemo -> withTypeMap tm $ mdo

  nut <- newUniqueType ut

  let mts = tvs <&> \tv -> tvmap ! tv
  let mdd = M.DD nut mdcs ann mts tdd
  addMemo (mdd, dcQuery)


  -- Strip "unused" constructors. Currently, these are constructors that contain empty unions.
  -- TEMP: This is not finished - it only cares about unions, but a more thorough solution would track which constructors of a particular type were actually used.
  -- NOTE: also, there is something to be said about eliminating non-existent members/constructors. if we only index member by offsets and don't export it, then should we honor the structure? IMO no, unless explicitly specified in an annotation or something.
  let strippedDCs = tdcs <&> filter (\(T.DC _ _ conTs _) ->
        let
          isUnionEmpty :: T.EnvUnionF a -> Any
          isUnionEmpty union =
            -- NOTE: we must first replace it. also, HACK: it's retarded. TODO: make it better.
            case unionMap !? union.unionID of
              Just eu -> Any $ null eu.union
              Nothing -> Any $ null union.union

          hasEmptyUnions :: T.Type -> Any
          hasEmptyUnions = cata $ \case
              T.TFun union ts t -> isUnionEmpty union <> fold union <> fold ts <> t
              T.TCon _ ts fnUnions -> fold ts <> foldMap isUnionEmpty fnUnions
              t -> fold t

          dcHasEmptyUnions :: [T.Type] -> Bool
          dcHasEmptyUnions = getAny . foldMap hasEmptyUnions
        in not $ dcHasEmptyUnions conTs)

  mdcs <- case strippedDCs of
    Right dcs -> fmap Right $ for dcs $ \(T.DC _ uc ts dcann) -> do
        nuc <- newUniqueCon uc
        mdcts <- traverse mType ts
        pure $ M.DC mdd nuc mdcts dcann

    Left drs -> fmap Left $ for drs $ \(T.DR _ memname memtype anns) -> do
        um <- member (mdd, memname)
        mt <- mType memtype
        pure $ M.DR mdd um mt anns


  -- DEBUG: how datatypes are transformed.
  ctxPrint' $ printf "Mono: %s" (Common.ppTypeInfo ut)
  ctxPrint' "======"
  ctxPrint T.tDataCons tdcs
  ctxPrint' "------"
  ctxPrint T.tDataCons strippedDCs
  ctxPrint' ",,,,,,"
  ctxPrint (either (const "n/a (it's a record.)") (ppLines (\(M.DC _ uc _ _) -> Common.ppCon uc))) mdcs
  ctxPrint' "======"
  ctxPrint' $ printf "Mono'd: %s" (Common.ppTypeInfo nut)

  -- used only by non-record types!
  let dcQuery = Map.fromList $ case (strippedDCs, mdcs) of
        (Right ttdcs, Right mmdcs) -> zip ttdcs mmdcs
        (Left _, Left _) -> mempty
        _ -> error "caulk."  -- does not have to be very sane - controlled environment.

  pure (mdd, dcQuery)



retrieveTV :: T.TVar -> Context M.IType
retrieveTV tv = do
  TypeMap typeMap _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error happens) when an environment is outside of its scope.
    Nothing -> Fix $ M.ITVar tv



withTypeMap :: TypeMap -> Context a -> Context a
withTypeMap tm a = do

  -- DEBUG: check typemap.
  ctxPrint' "Type map:"
  ctxPrint ppTypeMap tm


  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- State.withStateT (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify $ \s -> s { tvarMap = ogTM }

  pure x


withClassInstanceAssociations :: T.ClassInstantiationAssocs -> Context a -> Context a
withClassInstanceAssociations ucis a = do
  ogTM <- State.gets classInstantiationAssociations

  liftIO $ ctxPrint' $ printf "CIA: %s" (Common.ppMap $ fmap (bimap (fromString . show) (Common.encloseSepBy "[" "]" ", " . fmap (Common.ppTup . bimap T.tType (Common.ppTup . bimap (Common.encloseSepBy "[" "]" ", " . fmap T.tType) (\ifn -> Common.ppVar Local ifn.instFunction.functionDeclaration.functionId))))) $ fmap2 (fmap $ \(l, r, _) -> (l, r)) $ Map.toList ogTM)

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



mUnion :: T.EnvUnionF (Context M.IType) -> Context M.IEnvUnion
mUnion tunion = do

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  TypeMap _ envMap <- State.gets tvarMap
  case envMap !? tunion.unionID of
    Just mru -> pure mru
    Nothing -> do
      -- this adds instantiations from this specific union instantiation to cucked unions.
      let addCuckedUnionEnvs :: T.EnvUnionF (Context M.IType) -> M.IEnvUnion -> Context ()
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
                  [] -> error $ printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ M.EnvUnion { M.unionID = eid, M.union = e :| es }

              addCuckedUnionEnvs tunion ieu
              pure ieu

            else
              -- normal union - all TVars mapped. safe to memoize.
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) tunion' $ \tunion'' _ -> do
                let menvs = tunion''.union
                case menvs of
                  [] -> error $ printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    nuid <- newUnionID
                    pure $ M.EnvUnion { M.unionID = nuid, M.union = e :| es }



-- NOTE: This is only used to correctly monomorphize the function this env belongs to. It does not actually monomorphize envs in types.
mEnv' :: T.EnvF T.Type -> Context (M.IEnvF M.IType)
mEnv' env = do
  env' <- traverse mType env
  pure $ mEnv env'



-- TODO: modify?
mEnv :: T.EnvF M.IType -> M.IEnvF M.IType
mEnv = \case
    T.RecursiveEnv eid isEmpty -> M.IRecursiveEnv eid isEmpty

    -- xdddd, we don't create a new env id when it has shit inside.
    -- NOTE: 21.05.25: I don't think it's relevant anymore?
    T.Env eid params _ _ | not (null (foldMap (\(_, _, t) -> ftvButIgnoreUnions t) params)) -> do
      -- we have to preserve the original ID to later replace it with all the type permutations.
      M.IEnv eid $ params <&> \(_, _, t) -> t

    T.Env eid params _ _ -> do
      M.IEnv eid  $ params <&> \(_, _, t) -> t



------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , tvarInsts :: Map T.TVar (Map T.ClassDef T.InstDef)  -- TODO: smell.
  , memoFunction :: Memo (T.Function, [M.IType], M.IType, M.IEnvF M.IType) M.IFunction
  , memoDatatype :: Memo (T.DataDef, TypeMap) (M.IDataDef, Map T.DataCon M.IDataCon)
  , memoEnv :: Memo (T.EnvF (T.Type, M.IType)) M.IEnv
  , memoUnion :: Memo (T.EnvUnionF M.IType) M.IEnvUnion
  , memoMember :: Memo (M.IDataDef, MemName) UniqueMem

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo UnionID M.IEnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  , cuckedUnionInstantiation :: Map M.IEnvUnion (Set (T.EnvF M.IType))  -- this one is to track all environments which get instantiated for this union.
  -- also, this can be done in the same way as subst - would even require us to track less state.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: Map EnvID (Set EnvUse)  -- NOTE: FUTURE TYPECHECK
  -- i think it's also not needed now.

  , usedVars :: Set (UniqueVar, M.IType)  -- FROM RemoveUnused. this thing tracks which (monomorphized) variables were used. remember that it should not carry between scopes.-- NOTE: FUTURE TYPECHECK (also unused now)
  -- added Set TVar to fix the nested function environment expansion problem. Let's see if it works.

  , classInstantiationAssociations :: T.ClassInstantiationAssocs
  , currentLevel :: Int  -- HACK: it's for knowing when instances should be local or not.
  }
type Context = StateT Context' IO

startingContext :: T.ClassInstantiationAssocs -> Context'
startingContext cia = Context
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
  , classInstantiationAssociations = cia
  , currentLevel = 0  -- BAD
  }


-----------------------
-- TypeMap stuff
----------------------

-- HACK: EnvUnions are only needed when monomorphizing types. However, it's slightly easier right now to add this field. This should probably change later.
--  TODO: what did I mean???
data TypeMap = TypeMap (Map T.TVar M.IType) (Map UnionID M.IEnvUnion) deriving (Eq, Ord)

instance Semigroup TypeMap where
  TypeMap l1 l2 <> TypeMap r1 r2 = TypeMap (l1 <> r1) (l2 <> r2)

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty


ppTypeMap :: TypeMap -> Common.Context
ppTypeMap (TypeMap tvs unions) = Common.ppLines'
  [ (ppMap . fmap (bimap (Common.pretty . T.fromTV) M.mtType) . Map.toList) tvs
  , (ppMap . fmap (bimap Common.ppUnionID (M.tEnvUnion . fmap (T.tEnv' . fmap M.mtType))) . Map.toList) unions
  ]


typeMapFromDataDef :: T.DataDef -> [M.IType] -> [Maybe M.IEnvUnion] -> TypeMap
typeMapFromDataDef (T.DD _ (T.Scheme tvs unions) _ _) mts munions =
  TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip unions munions)


-- ahhh, i hate it. TODO: try to figure out if there is a way to do it without doing this time consuming and error prone mapping.
mapType :: T.Type -> M.IType -> TypeMap
mapType tt mt = case (project tt, project mt) of
  (T.TFun tu tts tret, M.ITFun mu mts mret) -> mapTypes tts mts <> mapType tret mret <> TypeMap mempty (Map.singleton tu.unionID mu)
  (T.TCon _ tts tus, M.ITCon _ mts mus) -> mapTypes tts mts <> TypeMap mempty (Map.fromList $ zip (T.unionID <$> tus) mus)
  (T.TVar tv, t) -> TypeMap (Map.singleton tv (embed t)) mempty

  _ -> error $ printf "[COMPILER ERROR]: Fuck."

mapTypes :: [T.Type] -> [M.IType] -> TypeMap
mapTypes tts mts = mconcat $ zipWith mapType tts mts



newUniqueType :: UniqueType -> Context UniqueType
newUniqueType ut = do
  tid <- liftIO newUnique
  pure $ ut { typeID = tid }


newUniqueCon :: UniqueCon -> Context UniqueCon
newUniqueCon uc = do
  cid <- liftIO newUnique
  pure $ uc { conID = cid }


newUniqueVar :: UniqueVar -> Context UniqueVar
newUniqueVar uv = do
  vid <- liftIO newUnique
  pure $ uv { varID = vid }

mkUniqueMember :: MemName -> Context UniqueMem
mkUniqueMember memname = do
  mid <- liftIO newUnique
  pure $ MI { memName = memname, memID = mid }


newEnvID :: Context EnvID
newEnvID = do
  eid <- liftIO newUnique
  pure $ EnvID { fromEnvID = eid }


newUnionID :: Context UnionID
newUnionID = do
  eid <- liftIO newUnique
  pure $ UnionID { fromUnionID = eid }




--------------------------------------------------------
-- STEP 2: Map missing shit.
-- NOTE: THIS IS TYPESAFE BUT BAD. WE BASICALLY ARE REDOING MONOMORPHIZATION IN THE SAME AMOUNT OF LINES. Maybe a less typesafe data structure would be better, as it would cut down on half the file. Or somehow do it in real time - check when the scope exits and then map the instances.
--------------------------------------------------------


withEnvContext :: Map (T.EnvF M.IType) M.IEnv -> Map M.IEnvID (Set EnvUse) -> Map M.IEnvUnion (Set (T.EnvF M.IType)) -> EnvContext a -> IO a
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


mfAnnStmts :: [M.AnnIStmt] -> EnvContext [M.AnnStmt]
mfAnnStmts stmts = fmap catMaybes $ for stmts $ cata $ \(O (Annotated anns stmt)) -> do
  stmt' <- bitraverse mfExpr id stmt
  let s = pure . Just
  let
    body :: NonEmpty (Maybe M.AnnStmt) -> NonEmpty M.AnnStmt
    body bstmts =
      let eliminated = catMaybes $ NonEmpty.toList bstmts
      in case eliminated of
        [] -> Fix (O (Annotated [] M.Pass)) :| []
        (st:sts) -> st :| sts

  fmap (embed . O . Annotated anns) <$> case stmt' of
    M.EnvDef envs -> do
      mfenvs <- traverse (bitraverse mfFunction mfEnvDef) envs
      s $ M.EnvDef $ NonEmpty.toList mfenvs

    M.Pass -> s M.Pass
    M.ExprStmt e -> s $ M.ExprStmt e
    M.Assignment vid expr -> s $ M.Assignment vid expr
    M.Print e -> s $ M.Print e
    M.Mutation vid loc e -> s $ M.Mutation vid loc e
    M.If cond ifTrue elseIfs else' -> s $ M.If cond (body ifTrue) (fmap2 body elseIfs) (body <$> else')
    M.Switch e cases -> fmap (Just . M.Switch e) $ for cases $ \kase -> do
      mdecon <- mfDecon kase.deconstruction
      pure $ M.Case { deconstruction = mdecon, caseCondition = kase.caseCondition, body = body kase.body }
    M.Return e -> s $ M.Return e

mfDecon :: M.IDecon -> EnvContext M.Decon
mfDecon = cata $ fmap embed . \case
  M.CaseVariable t v -> do
    mt <- mfType t
    pure $ M.CaseVariable mt v

  M.CaseRecord t _ decons -> do
    mt <- mfType t

    -- fun unsafe shit.
    let dd = case project mt of
          M.TCon mdd -> mdd
          mpt -> error $ printf "Ayo, member type is not a data definition, wut???? (type: %s)" (M.tType (embed mpt))

    decons' <- for decons $ \(um, decon) -> do
      mdecon <- decon
      pure (um, mdecon)
    pure $ M.CaseRecord mt dd decons'

  M.CaseConstructor t dc decons -> do
    mt <- mfType t
    mdc <- mfConstructor dc t
    mdecons <- sequenceA decons
    pure $ M.CaseConstructor mt mdc mdecons


mfExpr :: M.IExpr -> EnvContext M.Expr
mfExpr expr = flip cata expr $ \(M.TypedExpr imt imexpr) -> do
  mt <- mfType imt
  fmap (embed . M.TypedExpr mt) $ case imexpr of
    M.Var loc v -> M.Var loc <$> mfVariable v
    M.Lam env args ret -> do
      margs <- traverse2 mfType args
      menv <- mfEnvDef env
      mret <- ret
      pure $ M.Lam menv margs mret

    M.Con con -> M.Con <$> mfConstructor con imt

    M.RecCon _ insts -> do
      let dd = expectDataDef mt
      insts' <- sequenceA2 insts
      pure $ M.RecCon dd insts'
    M.RecUpdate _ e upd -> do
      let dd = expectDataDef mt
      me <- e
      upd' <- sequenceA2 upd
      pure $ M.RecUpdate dd me upd'
    M.MemAccess e um -> do
      mfe <- e
      pure $ M.MemAccess mfe um

    M.Lit lt -> pure $ M.Lit lt
    M.Op l op r -> M.Op <$> l <*> pure op <*> r
    M.Call c args -> M.Call <$> c <*> sequenceA args

mfVariable :: M.IVariable -> EnvContext M.Variable
mfVariable = \case
  M.DefinedVariable uv -> pure $ M.DefinedVariable uv
  M.DefinedFunction fun -> do
    mfun <- mfFunction fun
    pure $ M.DefinedFunction mfun


mfEnvDef :: M.IEnv -> EnvContext M.Env
mfEnvDef = \case
  M.IDRecursiveEnv eid isEmpty -> error "RECURSIVE ENV YO." -- pure $ M.RecursiveEnv eid isEmpty
  M.IDEnv eid envContent -> do
    menvContent <- traverse (\(v, l, li, t) -> mfType t >>= \t' -> (,l,li,t') <$> mfVariable v) envContent  -- the weird monad shit is so we 
    pure $ M.Env eid menvContent

mfEnv :: T.EnvF M.IType -> EnvContext (Maybe M.Env)
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


mfType :: M.IType -> EnvContext M.Type
mfType = para $ fmap embed . \case
  M.ITCon dd _ unions -> do
    munions <- traverse (mfUnion . fmap2 fst) unions
    M.TCon . fst <$> mfDataDef (dd, munions)

  M.ITFun union args (_, ret) -> do
    munion <- mfUnion $ fmap2 fst union
    margs <- traverse snd args
    mret <- ret
    pure $ M.TFun munion margs mret

  M.ITVar tv -> error $ printf "[COMPILER ERROR]: TVar %s not matched - types not appied correctly?" (ctx T.tTVar tv)



mfUnion :: M.EnvUnionF (T.EnvF M.IType) -> EnvContext M.EnvUnion
mfUnion union = do
  cuckedUnions <- RWS.asks cuckedUnionInsts
  mappedEnvs <- case cuckedUnions !? union of
      -- here should be no ftvs.
      Nothing -> fmap concat $ for (NonEmpty.toList union.union) $ \env -> do
          ctxPrint' $ printf "???: %s ?? %s" (T.tEnv' $ M.mtType <$> env) (show $ null (foldMap ftvButIgnoreUnions env))
          menv <- mfEnv env
          ctxPrint' $ printf "NOFTV: %s => %s" (T.tEnv' $ M.mtType <$> env) (maybe "???" M.tEnv menv)
          pure $ maybeToList menv

      -- here should also be no ftvs in the NEW UNION
      -- these were cuckedUnions
      Just envs -> do
        -- NOTE: i did catMaybes because mfEnv returns this. I don't think it's necessary anymore.
        menvs <- fmap catMaybes $ traverse mfEnv $ Set.toList envs
        pure menvs

  -- NOTE: I HATE THIS FUCKING ERROR LIKE YOU WOULDN'T BELIEVE.
  ctxPrint' $ printf "mfUnion: %s => %s" (M.tEnvUnion $ M.mtEnv <$> union) (Common.encloseSepBy "{" "}" ", " $ M.tEnv <$> mappedEnvs)
  let mUsedEnvs = case mappedEnvs of
        [] -> error $ "[COMPILER ERROR] Empty union (" <> show union.unionID <> ") encountered... wut!??!??!?!? Woah.1>!>!>!>!>>!"
        (x:xs) -> x :| xs

  pure $ M.EnvUnion { M.unionID = union.unionID, M.union = mUsedEnvs }



-- TODO: smell. this seems to expand environments only for functions, which means it's only used for EnvDefs.
--       it's because each function usage is separate in the environment, so we don't have to expand them.
expandEnvironments :: [EnvID] -> EnvContext [(M.Function, M.Env)]
expandEnvironments envIDs = do
  envInsts <- RWS.asks allInsts
  ctxPrint' $ printf "expand: %s\n%s" (ppList ppEnvID envIDs) (ppMap $ Map.toList envInsts <&> \(eid, euse) -> (ppEnvID eid, ppList (\(EnvUse mfn env) -> case mfn of { Just fn -> "(" <> ppVar Local fn.functionDeclaration.functionId <>  ", " <> ppEnvID (M.idenvID env) <> ")"; Nothing -> ppEnvID (M.idenvID env) }) $ Set.toList euse))
  fmap concat $ for envIDs $ \envID ->
    case envInsts !? envID of
      Just envs -> do
        traverse (bitraverse mfFunction mfEnvDef) $ mapMaybe (\(EnvUse fn env) -> fn <&> (,env)) $ Set.toList envs
      Nothing -> pure []


mfDataDef :: (M.IDataDef, [M.EnvUnion]) -> EnvContext (M.DataDef, Map M.IDataCon M.DataCon)
mfDataDef = memo memoIDatatype (\mem s -> s { memoIDatatype = mem }) $ \(idd, _) addMemo -> mdo
  mfAppliedTypes <- traverse mfType idd.appliedTypes
  let dd = M.DD idd.thisType cons idd.annotations mfAppliedTypes idd.ogDataDef
  addMemo (dd, dcQuery)

  cons <- case idd.constructors of
    Right mcons -> fmap Right $ for mcons $ \(M.DC _ uc imts ann) -> do
      mts <- traverse mfType imts
      pure $ M.DC dd uc mts ann

    Left mrecs -> fmap Left $ for mrecs $ \(M.DR _ um t ann) -> do
      mt <- mfType t
      pure $ M.DR dd um mt ann

  let dcQuery = Map.fromList $ case (idd.constructors, cons) of
        (Right ttdcs, Right mmdcs) -> zip ttdcs mmdcs
        (Left _, Left _) -> mempty
        _ -> error "caulk."  -- does not have to be very safe/sane - controlled environment.
  pure (dd, dcQuery)



mfFunction :: M.IFunction -> EnvContext M.Function
mfFunction fun = do
  ctxPrint' $ printf "MF function %s" (Common.ppVar Local fun.functionDeclaration.functionId)
  ctxPrint M.mtFunction fun

  -- just map everything.
  let fundec = fun.functionDeclaration
  env <- mfEnvDef fundec.functionEnv
  params <- traverse (bitraverse mfDecon mfType) fundec.functionParameters
  ret <- mfType fundec.functionReturnType

  let mfundec = M.FD { M.functionEnv = env, M.functionId = fundec.functionId, M.functionParameters = params, M.functionReturnType = ret }

  body <- mfAnnStmts $ NonEmpty.toList fun.functionBody
  let completedBody = case body of
        [] ->
          -- TODO: we need to automatically insert return values based on flow analysis (but that should be part of typechecking?)
          let pass = Fix (O (Annotated [] M.Pass))
          in pass :| []

        (s:ss) -> s :| ss

  pure $ M.Function { M.functionDeclaration = mfundec, M.functionBody = completedBody }



mfConstructor :: M.IDataCon -> M.IType -> EnvContext M.DataCon
mfConstructor dc@(M.DC dd _ _ _) imt = do
  -- Extract type. Pretty bad, but should just work.
  let imunions = case project imt of
        M.ITCon _ _ unions -> unions
        M.ITFun _ _ (Fix (M.ITCon _ _ unions)) -> unions

        -- COMPILER ERROR
        _ -> error $ printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (M.mtType imt)

  -- mtypes <- traverse mfType ttypes
  munions <- traverse mfUnion imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  pure mdc



-- ftvEnvButIgnoreUnions :: M.IEnv -> Set T.TVar
-- ftvEnvButIgnoreUnions = \case
--   M.IRecursiveEnv _ _ -> Set.empty
--   M.IEnv _ ts -> foldMap (\(_, _, t) -> ftvButIgnoreUnions t) ts

ftvButIgnoreUnions :: M.IType -> Set T.TVar
ftvButIgnoreUnions = cata $ \case
  M.ITVar tv -> Set.singleton tv
  M.ITCon _ ts _ -> mconcat ts
  M.ITFun _ args ret -> mconcat args <> ret

ftvTButIgnoreUnions :: T.Type -> Set T.TVar
ftvTButIgnoreUnions = cata $ \case
  T.TVar tv -> Set.singleton tv
  T.TCon _ ts _ -> mconcat ts
  T.TFun _ args ret -> mconcat args <> ret
  T.TyVar _ -> error "Encountered a tyvar."



filterEnvs :: [T.EnvF a] -> EnvContext [T.EnvF a]
filterEnvs envs = do
  envIds <- RWS.asks allInsts
  pure $ filter (\e -> T.envID e `Map.member` envIds) envs


expectIDataDef :: M.IType -> M.IDataDef
expectIDataDef mt = case project mt of
    M.ITCon mdd _ _ -> mdd
    mpt -> error $ printf "Ayo, member type is not a data definition, wut???? (type: %s)" (M.mtType (embed mpt))

expectDataDef :: M.Type -> M.DataDef
expectDataDef mt = case project mt of
    M.TCon mdd -> mdd
    mpt -> error $ printf "Ayo, member type is not a data definition, wut???? (type: %s)" (M.tType (embed mpt))



-------------------------
-- Step 2 Type defs!
------------------------


type EnvContext = RWST EnvContextUse () EnvMemo IO  -- TEMP: IO temporarily for debugging. should not be used for anything else.
-- Stores environment instantiations. 
--   NOTE: In the future, maybe more stuff (like which constructors were used!)
data EnvContextUse = EnvContextUse
  { allInsts :: Map M.IEnvID (Set EnvUse)
  , envs     :: Map (T.EnvF M.IType) M.IEnv
  , cuckedUnionInsts :: Map M.IEnvUnion (Set (T.EnvF M.IType))
  }

data EnvUse = EnvUse (Maybe M.IFunction) M.IEnv

instance Eq EnvUse where
  EnvUse _ le == EnvUse _ re = le == re

instance Ord EnvUse where
  EnvUse _ le `compare` EnvUse _ re = le `compare` re


newtype EnvMemo = EnvMemo
  { memoIDatatype :: Memo (M.IDataDef, [M.EnvUnion]) (M.DataDef, Map M.IDataCon M.DataCon)
  }




----------------------
-- UNRELATED MISC
----------------------

instance Foldable ((,,) a b) where
  foldr f x (_, _, y) = f y x

instance Traversable ((,,) a b) where
  traverse f (a, b, x) = (a, b,) <$> f x
