{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo, TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- we implement basic instances (Foldable, Travesable) for Tuple.

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}  -- for HLINT kekek
{-# HLINT ignore "Use <$>" #-}
{-# HLINT ignore "Redundant pure" #-}  -- this is retarded. it sometimes increases readability with that extra pure.
module Mono (mono) where

import AST.Common (Annotated (..), UniqueVar (..), UniqueCon (..), UniqueType (..), TVar, TCon (..), UnionID (..), EnvID (..), VarName (..), Locality (..), (:.) (..), printf, ctx, ppMap, ppLines, ctxPrint', ctxPrint, phase, ppTVar, traverse2, fmap2)
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
import Data.Foldable (fold)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe, fromJust)
import Data.Set (Set)
import Misc.Memo (Memo (..), emptyMemo, memo, memo', isMemoed)
import Data.Monoid (Any (Any, getAny))
import Control.Monad.Trans.RWS (RWST)
import qualified Control.Monad.Trans.RWS as RWS




------ Monomorphization consists of two steps:
--  Step 1: Perform normal monomorphization (however, you won't be able to compile escaped TVars).
--  Step 2: Replace escaped TVars with each instantiation of them. (TODO: this is bad, but necessary. maybe do it in RemoveUnused somehow?)


mono :: [T.AnnStmt] -> IO M.Module
mono tmod = do

  -- Step 1: Just do monomorphization with a few quirks*.
  (mistmts, monoCtx) <- flip State.runStateT startingContext $ mStmts tmod


  phase "Monomorphisation (env instantiations)"
  ctxPrint (Common.ppMap . fmap (bimap Common.ppEnvID (Common.encloseSepBy "[" "]" ", " . fmap (\(EnvUse _ env) -> M.mtEnv env) . Set.toList)) . Map.toList) monoCtx.envInstantiations

  phase "Monomorphisation (first part)"
  ctxPrint M.mtStmts mistmts


  -- Step 2 consists of:
  -- 1. substitute environments
  -- 2. check function usage and remove unused EnvDefs

  mmod <- withEnvContext monoCtx.envInstantiations $ do
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
      T.Switch switch cases -> mann . M.Switch switch $ mCase <$> cases
      T.Return ete -> mann $ M.Return ete
      T.EnvDef fn -> do
        let env = fn.functionDeclaration.functionEnv
        let envID = T.envID env
        noann $ M.EnvDef envID



mExpr :: T.Expr -> Context M.IExpr
mExpr = cata $ fmap embed . \(T.TypedExpr t expr) -> do
  mt <- mType t
  expr' <- sequenceA expr
  mexpr <- case expr' of

    T.Var locality v -> do
      mv <- variable v mt
      pure $ M.Var locality mv

    T.Con eid c -> do
      mc <- constructor c t

      -- don't forget to register usage.
      emptyEnv <- mEnv $ T.Env eid []
      registerEnvMono Nothing eid emptyEnv

      pure $ M.Con mc

    T.Lit lit -> pure $ M.Lit lit
    T.Op l op r -> pure $ M.Op l op r
    T.Call e args -> pure $ M.Call e args
    T.As (Fix (M.TypedExpr _ e)) _ -> do
      -- Ignore 'as' by unpacking the variable and passing in the previous expression.
      pure e
    T.Lam env args ret -> do
      margs <- traverse2 mType args
      menv <- mEnv' env
      registerEnvMono Nothing (T.envID env) menv

      pure $ M.Lam menv margs ret

  pure $ M.TypedExpr mt mexpr



mCase :: T.Case M.IExpr M.AnnIStmt -> M.CaseF M.IExpr M.AnnIStmt
mCase _ = undefined -- M.Case <$> mDecon kase.deconstruction <*> sequenceA kase.caseCondition <*> sequenceA kase.body
  -- where 
  --   mDecon = cata $ fmap embed . go
  --     where
  --       go = \case
  --         T.CaseVariable t uv -> do
  --           t' <- mType t
  --           uv' <- variable uv t'
  --           pure $ M.CaseVariable t' uv'
  --         T.CaseConstructor t uc args -> do
  --           t' <- mType t
  --           uc' <- constructor uc t'
  --           M.CaseConstructor t' uc' <$> sequenceA args



variable :: T.Variable -> M.IType -> Context M.IVariable
variable (T.DefinedVariable uv) _ = pure $ M.DefinedVariable uv
variable (T.DefinedFunction vfn) et = do
  ctxPrint' $ "in function: " <> show vfn.functionDeclaration.functionId.varName.fromVN

  -- male feminists are seething rn
  let (tts, tret, envEmptiness) = case project et of
        M.ITFun union mts mret -> (mts, mret, not $ M.areAllEnvsEmpty union)
        _ -> undefined


  -- DEBUG: print a non-memoized type. This was used to check memoization errors.
  ctxPrint' $ printf "Decl (nomemo): %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> tts) (M.mtType tret)


  -- creates a type mapping for this function.
  let typemap = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret

  withTypeMap typemap $ do
    -- NOTE: Env must be properly monomorphised with the type map though albeit.
    menv <- mEnv' vfn.functionDeclaration.functionEnv

    -- see definition of Context for exact purpose of these parameters.
    fmap M.DefinedFunction $ flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv, envEmptiness) $ \(tfn, ts, ret, env, needsEnv) addMemo -> mdo

      uv <- newUniqueVar tfn.functionDeclaration.functionId

      let fundec = M.FD env uv (zipWith (\mt (pv, _) -> (pv, mt)) ts tfn.functionDeclaration.functionParameters) ret needsEnv :: M.IFunDec


      -- DEBUG: when in the process of memoization, show dis.
      ctxPrint' $ printf "Decl: %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> ts) (M.mtType ret)
      ctxPrint' $ printf "M function: %s" (Common.ppVar Local fundec.functionId)


      -- add memo, THEN traverse body.
      let fn = M.Function { M.functionDeclaration = fundec, M.functionBody = body } :: M.IFunction
      addMemo fn
      body <- mStmts tfn.functionBody

      -- Then add this environment to the "used" environments for step 2.
      registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) env

      pure fn



-- Registers a single environment monomorphization. later used to track which environments monomoprhised to what.
registerEnvMono :: Maybe M.IFunction -> EnvID -> M.IEnv -> Context ()
registerEnvMono mvar oldEID nuEnv | null (ftvEnvButIgnoreUnions nuEnv) = State.modify $ \mctx -> mctx { envInstantiations = Map.insertWith (<>) (M.envID nuEnv) (Set.singleton (EnvUse mvar nuEnv)) (Map.insertWith (<>) oldEID (Set.singleton (EnvUse mvar nuEnv)) mctx.envInstantiations) }

-- ignore when the environment has TVars...???? i guess...
registerEnvMono _ _ _ = pure ()



constructor :: T.DataCon -> T.Type -> Context M.IDataCon
constructor tdc@(T.DC dd@(T.DD ut _ _ _) _ _ _) et = do
  -- Extract type. Pretty bad, but should just work.
  let (ttypes, tunions) = case project et of
        T.TCon _ tts unions -> (tts, unions)
        T.TFun _ _ (Fix (T.TCon _ tts unions)) -> (tts, unions)

        -- COMPILER ERROR
        _ -> error $ printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (T.tType et)

  mtypes <- traverse mType ttypes
  munions <- (mUnion . fmap mType) `traverse2` hideEmptyUnions tunions  -- ISSUE(unused-constructor-elimination): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.
  -- TODO: also, in this place, we should eliminate unused constructors. (either here or in mfDataDef!)

  -- Like in typechecking, find this constructor by performing an unsafe lookup!
  let tm = typeMapFromDataDef dd mtypes munions
  (_, dcQuery) <- mDataDef (dd, tm)
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ "[COMPILER ERROR]: Failed to query an existing constructor for type " <> show ut.typeName.fromTC

  pure mdc



mType :: T.Type -> Context M.IType
mType = cata $ \case
    T.TCon dd pts unions -> do
      params <- sequenceA pts
      munions <- mUnion `traverse2` hideEmptyUnions unions  -- ISSUE(unused-constructor-elimination): very hacky, but should work. I think it echoes the need for a datatype that correctly represents what we're seeing here - a possible environment definition, which might not be initialized.
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


hideEmptyUnions :: [T.EnvUnionF a] -> [Maybe (T.EnvUnionF a)]
hideEmptyUnions = fmap $ \u -> if not (T.isUnionEmpty u)
  then Just u
  else Nothing


-- (TypeMap (Map.fromList $ zip tvs mts) (Map.fromList $ fmap (first T.unionID) $ mapMaybe sequenceA $ zip ogUnions unions))
mDataDef :: (T.DataDef, TypeMap) -> Context (M.IDataDef, Map T.DataCon M.IDataCon)
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(T.DD ut (T.Scheme tvs _) tdcs ann, tm@(TypeMap tvmap unionMap)) addMemo -> withTypeMap tm $ mdo

  nut <- newUniqueType ut

  let mts = tvs <&> \tv -> tvmap ! tv
  let mdd = M.DD nut dcs ann mts
  addMemo (mdd, dcQuery)


  -- Strip "unused" constructors. Currently, these are constructors that contain empty unions.
  -- TEMP: This is not finished - it only cares about unions, but a more thorough solution would track which constructors of a particular type were actually used.
  let strippedDCs = flip filter tdcs $ \(T.DC _ _ conTs _) ->
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
        in not $ dcHasEmptyUnions conTs

  dcs <- for strippedDCs $ \(T.DC _ uc ts dcann) -> do
    nuc <- newUniqueCon uc
    mdcts <- traverse mType ts
    pure $ M.DC mdd nuc mdcts dcann


  -- DEBUG: how datatypes are transformed.
  ctxPrint' $ printf "Mono: %s" (Common.ppTypeInfo ut)
  ctxPrint' "======"
  ctxPrint (ppLines T.tConDef) tdcs
  ctxPrint' "------"
  ctxPrint (ppLines T.tConDef) strippedDCs
  ctxPrint' ",,,,,,"
  ctxPrint (ppLines (\(M.DC _ uc _ _) -> Common.ppCon uc)) dcs
  ctxPrint' "======"
  ctxPrint' $ printf "Mono'd: %s" (Common.ppTypeInfo nut)

  let dcQuery = Map.fromList $ zip strippedDCs dcs
  pure (mdd, dcQuery)



retrieveTV :: TVar -> Context M.IType
retrieveTV tv = do
  TypeMap typeMap _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error happens) when an environment is outside of its scope.
    Nothing -> Fix $ M.ITVar tv



withTypeMap :: TypeMap -> Context a -> Context a
withTypeMap tm@(TypeMap tmv tmenv) a = do

  -- DEBUG: check typemap.
  ctxPrint' "Type map:"
  ctxPrint (ppMap . fmap (bimap (Common.pretty . Common.fromTV) M.mtType) . Map.toList) tmv
  ctxPrint (ppMap . fmap (bimap Common.ppUnionID (M.tEnvUnion . fmap M.mtEnv)) . Map.toList) tmenv


  -- temporarily set merge type maps, then restore the original one.
  ogTM <- State.gets tvarMap
  x <- State.withStateT (\s -> s { tvarMap = tm <> s.tvarMap }) a
  State.modify $ \s -> s { tvarMap = ogTM }

  pure x



mUnion :: T.EnvUnionF (Context M.IType) -> Context M.IEnvUnion
mUnion tunion = do

  -- NOTE: check `TypeMap` definition as to why its needed *and* retarded.
  TypeMap _ envMap <- State.gets tvarMap
  case envMap !? tunion.unionID of
    Just mru -> pure mru
    Nothing -> do

      -- check if we previously encountered this environment and it contained TVars that weren't mapped.
      cuckedMemo <- State.gets cuckedUnions
      case isMemoed tunion.unionID cuckedMemo of
        Just mu -> pure mu
        Nothing -> do

          -- it wasn't... but it's still possible.
          tunion' <- sequenceA tunion
          let unionFTV = foldMap ftvButIgnoreUnions tunion'
          if not (null unionFTV)
            then
              -- had TVars -> remember it.
              memo' cuckedUnions (\mem mctx -> mctx { cuckedUnions = mem }) tunion'.unionID $ \eid _ -> do
                menvs <- traverse mEnv tunion'.union
                case menvs of
                  -- literally impossible as there would be no FTVs otherwise...
                  [] -> error $ printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ M.EnvUnion { M.unionID = eid, M.union = e :| es }

            else
              -- normal union - all TVars mapped. safe to memoize.
              memo' memoUnion (\mem mctx -> mctx { memoUnion = mem }) tunion' $ \tunion'' _ -> do
                menvs <- traverse mEnv tunion''.union
                case menvs of
                  [] -> error $ printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

                  (e:es) -> do
                    nuid <- newUnionID
                    pure $ M.EnvUnion { M.unionID = nuid, M.union = e :| es }



mEnv' :: T.EnvF T.Type -> Context M.IEnv
mEnv' env = do
  env' <- traverse mType env
  mEnv env'



mEnv :: T.EnvF M.IType -> Context M.IEnv
mEnv env' = do
  let mapParams = traverse $ \(v, loc, t) -> (,loc,t) <$> variable v t
  memo' memoEnv (\mem mctx -> mctx { memoEnv = mem }) env' $ \env _ -> case env of
    T.RecursiveEnv eid isEmpty -> pure $ M.RecursiveEnv eid isEmpty

    -- xdddd, we don't create a new env id when it has shit inside.
    T.Env eid params | not (null (foldMap (\(_, _, t) -> ftvButIgnoreUnions t) params)) -> do
      M.Env eid <$> mapParams params

    T.Env _ params -> do
      newEID <- newEnvID
      M.Env newEID <$> mapParams params



------------------------
-- Step 1 Type Definitions!
----------------------

data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , memoFunction :: Memo (T.Function, [M.IType], M.IType, M.IEnv, M.NeedsImplicitEnvironment) M.IFunction
  , memoDatatype :: Memo (T.DataDef, TypeMap) (M.IDataDef, Map T.DataCon M.IDataCon)
  , memoEnv :: Memo (T.EnvF M.IType) M.IEnv
  , memoUnion :: Memo (T.EnvUnionF M.IType) M.IEnvUnion

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo UnionID M.IEnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: Map EnvID (Set EnvUse)
  }
type Context = StateT Context' IO

startingContext :: Context'
startingContext = Context
  { tvarMap = mempty
  , memoFunction = emptyMemo
  , memoDatatype = emptyMemo
  , memoEnv = emptyMemo
  , memoUnion = emptyMemo

  , cuckedUnions = emptyMemo
  , envInstantiations = mempty
  -- , instantiationUsage = mempty
  }


-----------------------
-- TypeMap stuff
----------------------

-- HACK: EnvUnions are only needed when monomorphizing types. However, it's slightly easier right now to add this field. This should probably change later.
--  TODO: what did I mean???
data TypeMap = TypeMap (Map TVar M.IType) (Map UnionID M.IEnvUnion) deriving (Eq, Ord)

instance Semigroup TypeMap where
  TypeMap l1 l2 <> TypeMap r1 r2 = TypeMap (l1 <> r1) (l2 <> r2)

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty


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


withEnvContext :: Map EnvID (Set EnvUse) -> EnvContext a -> IO a
withEnvContext allInstantiations x = fst <$> RWS.evalRWST x envUse envMemo
  where
    envUse = EnvContextUse
      { allInsts = allInstantiations
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
    M.EnvDef envID -> do
      envs <- expandEnvironments [envID]
      case envs of
        -- NOTE: this case shouldn't technically get triggered, as we remove extraneous environments in RemoveUnused.
        [] -> error "wtffff. no envs left in EnvDef in Mono"
          -- pure Nothing

        (e:es) -> s $ M.EnvDef (e :| es)

    M.Pass -> s M.Pass
    M.ExprStmt e -> s $ M.ExprStmt e
    M.Assignment vid expr -> s $ M.Assignment vid expr
    M.Print e -> s $ M.Print e
    M.Mutation vid loc e -> s $ M.Mutation vid loc e
    M.If cond ifTrue elseIfs else' -> s $ M.If cond (body ifTrue) (fmap2 body elseIfs) (body <$> else')
    M.Switch _ _ -> undefined
    M.Return e -> s $ M.Return e

mfExpr :: M.IExpr -> EnvContext M.Expr
mfExpr expr = flip cata expr $ \(M.TypedExpr imt imexpr) -> do
  mt <- mfType imt
  fmap (embed . M.TypedExpr mt) $ case imexpr of
    M.Var loc v -> M.Var loc <$> mfVariable v
    M.Lam env args ret -> do
      margs <- traverse2 mfType args
      menv <- mfEnv $ mfType <$> env
      mret <- ret
      pure $ M.Lam menv margs mret

    M.Con con -> M.Con <$> mfConstructor con imt
    M.Lit lt -> pure $ M.Lit lt
    M.Op l op r -> M.Op <$> l <*> pure op <*> r
    M.Call c args -> M.Call <$> c <*> sequenceA args

mfVariable :: M.IVariable -> EnvContext M.Variable
mfVariable = \case
  M.DefinedVariable uv -> pure $ M.DefinedVariable uv
  M.DefinedFunction fun -> do
    mfun <- mfFunction fun
    pure $ M.DefinedFunction mfun


mfEnv :: M.EnvF M.IncompleteEnv (EnvContext M.Type) -> EnvContext M.Env
mfEnv (M.RecursiveEnv eid isEmpty) = pure $ M.RecursiveEnv eid isEmpty
mfEnv (M.Env eid envparams) = do
  menvparams <- traverse (\(v, loc, t) -> liftA2 (,loc,) (mfVariable v) t) envparams
  pure $ M.Env eid menvparams

mfType :: M.IType -> EnvContext M.Type
mfType = para $ fmap embed . \case
  M.ITCon dd _ unions -> do
    munions <- traverse mfUnion unions
    M.TCon . fst <$> mfDataDef (dd, munions)

  M.ITFun union args (_, ret) -> do
    munion <- mfUnion union
    margs <- traverse snd args
    mret <- ret
    pure $ M.TFun munion margs mret

  M.ITVar tv -> error $ printf "[COMPILER ERROR]: TVar %s not matched - types not applied correctly?" (ctx ppTVar tv)



mfUnion :: M.EnvUnionF (M.EnvF M.IncompleteEnv (M.IType, EnvContext M.Type)) -> EnvContext M.EnvUnion
mfUnion union = do
  usedEnvsFromThisEnv <- filterEnvs $ NonEmpty.toList union.union

  mappedEnvs <- fmap concat $ for usedEnvsFromThisEnv $ \env -> do
    if null (ftvEnvButIgnoreUnions $ fst <$> env)
      then fmap (:[]) $ mfEnv $ snd <$> env
      else do
        envMap <- RWS.asks allInsts
        traverse (mfEnv . fmap mfType . (\(EnvUse _ envInstantiation) -> envInstantiation)) $ Set.toList $ Map.findWithDefault Set.empty (M.envID env) envMap


  -- NOTE: I HATE THIS FUCKING ERROR LIKE YOU WOULDN'T BELIEVE.
  let mUsedEnvs = case mappedEnvs of
        [] -> error $ "[COMPILER ERROR] Empty union (" <> show union.unionID <> ") encountered... wut!??!??!?!? Woah.1>!>!>!>!>>!"
        (x:xs) -> x :| xs

  pure $ M.EnvUnion { M.unionID = union.unionID, M.union = mUsedEnvs }

  

expandEnvironments :: [EnvID] -> EnvContext [(M.Function, M.Env)]
expandEnvironments envIDs = do
  envInsts <- RWS.asks allInsts
  fmap concat $ for envIDs $ \envID ->
    case envInsts !? envID of
      Just envs -> do
        traverse (bitraverse mfFunction (mfEnv . fmap mfType)) $ mapMaybe (\(EnvUse fn env) -> fn <&> (,env)) $ Set.toList envs
      Nothing -> pure []



mfDataDef :: (M.IDataDef, [M.EnvUnion]) -> EnvContext (M.DataDef, Map M.IDataCon M.DataCon)
mfDataDef = memo memoIDatatype (\mem s -> s { memoIDatatype = mem }) $ \(idd, _) addMemo -> mdo
  mfAppliedTypes <- traverse mfType idd.appliedTypes
  let dd = M.DD idd.thisType cons idd.annotations mfAppliedTypes
  addMemo (dd, dcQuery)

  cons <- for idd.constructors $ \(M.DC _ uc imts ann) -> do
    mts <- traverse mfType imts
    pure $ M.DC dd uc mts ann

  let dcQuery = Map.fromList $ zip idd.constructors cons
  pure (dd, dcQuery)



mfFunction :: M.IFunction -> EnvContext M.Function
mfFunction fun = do
  ctxPrint' $ printf "MF function %s" (Common.ppVar Local fun.functionDeclaration.functionId)
  ctxPrint M.mtFunction fun

  -- just map everything.
  let fundec = fun.functionDeclaration
  env <- mfEnv $ mfType <$> fundec.functionEnv
  params <- traverse2 mfType fundec.functionParameters
  ret <- mfType fundec.functionReturnType

  let mfundec = M.FD { M.functionEnv = env, M.functionId = fundec.functionId, M.functionParameters = params, M.functionReturnType = ret, M.functionNeedsEnvironment = fundec.functionNeedsEnvironment }

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
  munions <- traverse (mfUnion . fmap2 (\t -> (t, mfType t))) imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  pure mdc



ftvEnvButIgnoreUnions :: M.IEnv -> Set TVar
ftvEnvButIgnoreUnions = \case
  M.RecursiveEnv _ _ -> Set.empty
  M.Env _ ts -> foldMap (\(_, _, t) -> ftvButIgnoreUnions t) ts

ftvButIgnoreUnions :: M.IType -> Set TVar
ftvButIgnoreUnions = cata $ \case
  M.ITVar tv -> Set.singleton tv
  M.ITCon _ ts _ -> mconcat ts
  M.ITFun _ args ret -> mconcat args <> ret



filterEnvs :: [M.EnvF envtype a] -> EnvContext [M.EnvF envtype a]
filterEnvs envs = do
  envIds <- RWS.asks allInsts

  let f (M.RecursiveEnv eid _) = Map.member eid envIds
      f (M.Env eid _) = Map.member eid envIds
  pure $ filter f envs



-------------------------
-- Step 2 Type defs!
------------------------


type EnvContext = RWST EnvContextUse () EnvMemo IO  -- TEMP: IO temporarily for debugging. should not be used for anything else.
-- Stores environment instantiations. 
--   NOTE: In the future, maybe more stuff (like which constructors were used!)
newtype EnvContextUse = EnvContextUse
  { allInsts :: Map EnvID (Set EnvUse)
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
