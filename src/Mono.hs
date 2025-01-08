{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, OverloadedStrings, RecursiveDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TupleSections #-}
module Mono (mono) where

import AST.Converged (Prelude(..))
import AST.Common (Annotated (..), UniqueVar (..), UniqueCon (..), UniqueType (..), TVar, TCon (..), UnionID (..), Ann, EnvID (..), VarName (..), (<+>), Locality (..), (:.) (..), printf, ctx, ppMap, ppLines, ctxPrint', ctxPrint, phase, ppTVar)
import qualified AST.Typed as T
import qualified AST.Mono as M
import qualified AST.Common as Common
import Data.Fix (Fix(..))
import Control.Monad.Trans.Reader (ReaderT, runReaderT, Reader)
import Data.Functor.Foldable (transverse, embed, cata, para, Base, project, hoist)
import Data.Bitraversable (bitraverse)
import Data.Biapplicative (first, second, bimap)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map, (!?), (!))
import Control.Monad.Trans.State (StateT)
import qualified Control.Monad.Trans.State as State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Data.Foldable (fold, traverse_, sequenceA_, for_)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)
import Data.Functor ((<&>))
import Data.Maybe (catMaybes, mapMaybe, fromMaybe, fromJust)
import Data.Functor.Identity (Identity(..))
import Data.Set (Set)
import Control.Monad (void, unless, join, (<=<))
import Data.Semigroup (sconcat)
import Misc.Memo (Memo (..), emptyMemo, memo, memoToMap, memo', isMemoed)
import Data.Monoid (Any (Any, getAny))
import Data.Foldable (find)
import Control.Monad.Trans.RWS (RWS, RWST)
import qualified Control.Monad.Trans.RWS as RWS
import Debug.Trace (traceShowWith)
import Data.Bool (bool)
import GHC.IO (unsafePerformIO)


data Context' = Context
  { tvarMap :: TypeMap  -- this describes the temporary mapping of tvars while monomorphizing.
  , memoFunction :: Memo (T.Function, [M.IType], M.IType, M.IEnv, M.NeedsImplicitEnvironment) M.IFunction
  , memoDatatype :: Memo (T.DataDef, [M.IType], [Maybe M.IEnvUnion]) (M.IDataDef, Map T.DataCon M.IDataCon)
  , memoEnv :: Memo (T.EnvF M.IType) M.IEnv
  , memoUnion :: Memo (T.EnvUnionF M.IType) M.IEnvUnion

  -- SPECIAL ENVIRONMENTS!!!
  , cuckedUnions :: Memo UnionID M.IEnvUnion  -- this tracks which environments couldn't be resolved. then, any time this environment is encountered, use this instead of `memoUnion`.
  -- we have to use EnvID, as the default comparator for Env checks arguments.
  -- TODO: all of this is todo. there might a better way, which only traverses everything once. (maybe? we still have to substitute remaining tvars in scope.)
  -- TODO: update above comments for Unions instead of Envs.

  -- burh, this is shit, literally
  -- like, maybe env usage can be merged into that kekekek.
  , envInstantiations :: Map EnvID (Set EnvUse)
  -- , instantiationUsage :: Map TVar (Set TypeMap)  -- kind of wasteful? we only need to track TVars which could not be solved before.

  -- HACK: Map old unique var + types to 
  }
type Context = StateT Context' IO


mono :: [T.AnnStmt] -> IO M.Module
mono mod = do
  (mistmts, ctx) <- flip State.runStateT startingContext $ mStmts mod
  -- let mtypeIDs = Map.elems ctx.typeFind

  let (Memo fm) = ctx.memoFunction
  let ifns = Map.elems fm

  -- let (Memo dm) = ctx.memoDatatype
  -- let idds = map fst $ Map.elems dm


  -- REMEMBER TO
  -- 1. substitute environments
  -- 2. check function usage and remove unused EnvDefs
  --      note, that EnvDefs might monomorphize unused functions. Thus, you should keep environments Typed, filter EnvDefs and then substitute environments. Maybe actually do it in the same step. Empty Unions would be removed also.
  -- liftIO $ for_ ifns $ \ifn -> putStrLn $ Common.ctx M.mtFunction ifn
  -- liftIO $ putStrLn $ Common.ctx M.mtStmts mistmts
  -- liftIO $ do
  --   putStrLn "Env Inst"
  --   for_ (Map.toList ctx.envInstantiations) $ \(eid, envs) ->
  --     putStrLn $ "  " <> show eid <> " => " <> show (M.envID <$> (Set.toList envs))

  phase "Monomorphisation (env instantiations)"
  ctxPrint (Common.ppMap . fmap (bimap Common.ppEnvID (Common.encloseSepBy "[" "]" ", " . fmap (\(EnvUse _ env) -> M.mtEnv env) . Set.toList)) . Map.toList) ctx.envInstantiations

  phase "Monomorphisation (first part)"
  ctxPrint M.mtStmts mistmts


  let envUsage = Map.keysSet ctx.envInstantiations
  (mstmts, dds, fns) <- withEnvContext envUsage ctx.envInstantiations $ do
        mstmts <- mfAnnStmts mistmts
        -- fns <- traverse mfFunction ifns
        let fns = undefined

        -- retrieve datatypes
        mapDDs <- RWS.gets memoIDatatype
        let dds = map fst $ Map.elems $ memoToMap  mapDDs
        pure (mstmts, dds, fns)


  -- Change the representation of a funFind map from (UV, Type) -> UV to UV -> [UV]
  -- let usageFind = toUsageFind ctx.funFind

  -- let mstmts = substEnv usageFind <$> mistmts
  -- let mfuns = substEnv usageFind `fmap3` mifuns
  let mmod = M.Mod { M.toplevelStatements = mstmts, M.functions = fns, M.datatypes = dds }
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

    -- note, that we don't have to do anything here...
    -- maybe sometime later order will matter?
    -- or just SYB
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

mCase :: T.Case M.IExpr M.AnnIStmt -> M.CaseF M.IExpr M.AnnIStmt
mCase kase = undefined -- M.Case <$> mDecon kase.deconstruction <*> sequenceA kase.caseCondition <*> sequenceA kase.body
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

variable :: T.Variable -> M.IType -> Context M.IVariable
variable (T.DefinedVariable uv) _ = pure $ M.DefinedVariable uv
variable (T.DefinedFunction vfn) et = do
  ctxPrint' $ "in function: " <> show vfn.functionDeclaration.functionId.varName.fromVN
  -- Unsound deconstruction...
  let (tts, tret, envEmptiness) = case project et of
        M.ITFun union mts mret -> (mts, mret, not $ M.areAllEnvsEmpty union)
        _ -> undefined

  -- OUTSIDE of withTypeMap... is this correct? I mean, these variables are only outside.
  -- TODO: this was related to env. it's possible for it to contain declaration vars. I'm not sure this is necessarily correct.
  let (mappedTs, mappedUs) = mapTypes (snd <$> vfn.functionDeclaration.functionParameters) tts <> mapType vfn.functionDeclaration.functionReturnType tret

  ctxPrint' $ printf "Decl (nomemo): %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> tts) (M.mtType tret)
  withTypeMap mappedTs mappedUs $ do
    menv <- mEnv' vfn.functionDeclaration.functionEnv

    fmap M.DefinedFunction $ flip (memo memoFunction (\mem s -> s { memoFunction = mem })) (vfn, tts, tret, menv, envEmptiness) $ \(tfn, ts, ret, env, needsEnv) addMemo -> mdo
      uv <- newUniqueVar tfn.functionDeclaration.functionId

      let fundec = M.FD env uv (zipWith (\mt (pv, _) -> (pv, mt)) ts tfn.functionDeclaration.functionParameters) ret needsEnv :: M.IFunDec
      ctxPrint' $ printf "Decl: %s -> %s" (Common.encloseSepBy "(" ")" ", " $ M.mtType <$> ts) (M.mtType ret)
      let fn = M.Function { M.functionDeclaration = fundec, M.functionBody = body } :: M.IFunction
      addMemo fn

      ctxPrint' $ printf "M function: %s" (Common.ppVar Local fundec.functionId)
      body <- mStmts tfn.functionBody

      -- remember to add this environment to the "used" environments.
      registerEnvMono (Just fn) (T.envID vfn.functionDeclaration.functionEnv) env

      pure fn

-- this is so bad ongggggggg, like literally.
--  but maybe it'll work.
registerEnvMono :: Maybe M.IFunction -> EnvID -> M.IEnv -> Context ()
registerEnvMono mvar oldEID nuEnv | null (ftvEnvButIgnoreUnions nuEnv) = State.modify $ \ctx -> ctx { envInstantiations = Map.insertWith (<>) (M.envID nuEnv) (Set.singleton (EnvUse mvar nuEnv)) (Map.insertWith (<>) oldEID (Set.singleton (EnvUse mvar nuEnv)) ctx.envInstantiations) }

-- ignore when the environment has TVars...???? i guess...
registerEnvMono _ _ _ = pure ()


-- registerTypeMapUsage :: TypeMap -> Context ()
-- registerTypeMapUsage tm@(TypeMap mt) = do
--   let tvars = Map.keys mt
--       newAdditions = Map.fromList $ tvars <&> (,Set.singleton tm)
--   State.modify $ \ctx -> ctx { instantiationUsage = Map.unionWith (<>) newAdditions ctx.instantiationUsage }

constructor :: T.DataCon -> T.Type -> Context M.IDataCon
constructor tdc@(T.DC dd@(T.DD ut _ _ _) _ _ _) et = do
  -- Extract type. Pretty bad, but should just work.
  let (ttypes, tunions) = case project et of
        T.TCon _ tts unions -> (tts, unions)
        T.TFun _ _ (Fix (T.TCon _ tts unions)) -> (tts, unions)

        -- COMPILER ERROR
        _ -> error $ printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (T.tType et)

  mtypes <- traverse mType ttypes
  munions <- traverse2 (mUnion . fmap mType) $ (\eu -> if not (T.isUnionEmpty eu) then Just eu else Nothing) <$> tunions  -- ISSUE(constructor-deduplication): filters unions kind of randomly. We expect that it's because a constructor is unused and not because of some other issue.

  (_, dcQuery) <- mDataDef (dd, mtypes, munions)
  -- liftIO $ putStrLn $ ctx T.tConDef tdc
  -- liftIO $ print $ bimap (\(T.DC _ uc _ _) -> uc) (\(M.DC _ uc _ _) -> uc) <$> Map.toList dcQuery
  -- liftIO $ putStrLn $ ctx M.tDataDef mdc
  -- liftIO $ putStrLn $ ctx (ppMap . fmap (bimap T.tConDef M.tConDef) . Map.toList) dcQuery
  let mdc = case dcQuery !? tdc of
        Just m -> m
        Nothing -> error $ "[COMPILER ERROR]: Failed to query an existing constructor for type " <> show ut.typeName.fromTC
  -- liftIO $ putStrLn $ ctx Common.ppCon $ (\(M.DC _ uc _ _) -> uc) mdc
  pure mdc

mType :: T.Type -> Context M.IType
mType = cata $ \case
    T.TCon dd pts unions -> do
      params <- sequenceA pts
      munions <- mUnion `traverse2` ((\eu -> if not (T.isUnionEmpty eu) then Just eu else Nothing) <$> unions)  -- ISSUE(constructor-deduplication): very hacky, but should work. I think it echoes the need for a datatype that correctly represents what we're seeing here - a possible environment definition, which might not be initialized.
      -- we need to represent this shit differently.
      -- munions <- traverse mUnion unions
      (mdd, _) <- mDataDef (dd, params, munions)
      let mt = Fix $ M.ITCon mdd params (catMaybes munions)
      pure mt

    T.TFun union params ret -> do
      union' <- mUnion union
      params' <- sequenceA params
      ret' <- ret

      pure $ Fix $ M.ITFun union' params' ret'

    T.TVar tv -> retrieveTV tv

    T.TyVar tv -> error $ printf "[COMPILER ERROR]: Encountered TyVar %s." (T.tTyVar tv)

mDataDef :: (T.DataDef, [M.IType], [Maybe M.IEnvUnion]) -> Context (M.IDataDef, Map T.DataCon M.IDataCon)
mDataDef = memo memoDatatype (\mem s -> s { memoDatatype = mem }) $ \(dd@(T.DD ut (T.Scheme tvs ogUnions) tdcs ann), mts, unions) addMemo -> withTypeMap (zip tvs mts) (mapMaybe sequenceA $ zip ogUnions unions) $ mdo
  nut <- newUniqueType ut
  let mdd = M.DD nut dcs ann mts
  addMemo (mdd, dcQuery)

  -- Strip constructors with empty unions.
  -- NOTE: This might be done in Typecheck, because we might strip constructors there as we want to typecheck things like: printLeft(Left(2)) (here, in Either e a, a is undefined and throws an error. Haskell doesn't care, so should I)

  let unionMap = Map.fromList $ mapMaybe sequenceA $ zip (T.unionID <$> ogUnions) unions
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

  ctxPrint' $ "Mono: " <> show ut.typeName.fromTC
  ctxPrint' "======"
  ctxPrint (ppLines T.tConDef) tdcs
  ctxPrint' "------"
  ctxPrint (ppLines T.tConDef) strippedDCs
  ctxPrint' ",,,,,,"
  ctxPrint (ppLines (\(M.DC _ uc _ _) -> Common.ppCon uc)) dcs
  ctxPrint' "======"
  let dcQuery = Map.fromList $ zip strippedDCs dcs

  pure (mdd, dcQuery)

retrieveTV :: TVar -> Context M.IType
retrieveTV tv = do
  TypeMap typeMap _ <- State.gets tvarMap
  pure $ case typeMap !? tv of
    Just t -> t

    -- this will happen (provided no compiler error) when an environment is outside of its scope.
    Nothing -> Fix $ M.ITVar tv

withTypeMap :: [(TVar, M.IType)] -> [(T.EnvUnion, M.IEnvUnion)] -> Context a -> Context a
withTypeMap tmv tmenv a = do
  ctxPrint' "Type map:"
  ctxPrint (ppMap . fmap (bimap (Common.pretty . Common.fromTV) M.mtType)) tmv
  ctxPrint (ppMap . fmap (bimap (T.tEnvUnion . fmap T.tType) (M.tEnvUnion . fmap M.mtEnv))) tmenv

  let tm = TypeMap (Map.fromList tmv) (Map.fromList ((map . first) T.unionID tmenv))
  -- registerTypeMapUsage tm

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
      cuckedMemo <- State.gets cuckedUnions
      case isMemoed tunion.unionID cuckedMemo of
        Just mu -> pure mu
        Nothing -> do
          tunion' <- sequenceA tunion
          let unionFTV = foldMap ftvButIgnoreUnions tunion'
          if not (null unionFTV)
            then
              memo' cuckedUnions (\mem ctx -> ctx { cuckedUnions = mem }) tunion'.unionID $ \eid _ -> do
                menvs <- traverse mEnv tunion'.union
                case menvs of
                  (e:es) -> do
                    -- preserve ID!!!!
                    pure $ M.EnvUnion { M.unionID = eid, M.union = e :| es }

                  -- literally impossible as there would be no FTVs otherwise...
                  [] -> error $ printf "[COMPILER ERROR]: Encountered an empty union (ID: %s) - should not happen." (show tunion.unionID)

            else
              memo' memoUnion (\mem ctx -> ctx { memoUnion = mem }) tunion' $ \tunion _ -> do
                menvs <- traverse mEnv tunion.union
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
mEnv env = do
  -- check if this is the special env (note that by now, TVars might be substituted, so we have to check first)
  -- cuckedMemo <- State.gets cuckedEnvs
  -- case isMemoed (T.envID env) cuckedMemo of
  --   Just menv -> pure menv
  --   Nothing -> do

  --     -- If not "cucked", check if this environment has any FTVs. If it has, it's our special cucked environment.
  --     let envFTV = foldMap ftv env
  --     if not (null envFTV)
  --       then
  --         memo' cuckedUnions (\mem ctx -> ctx { cuckedUnions = mem }) (T.envID env) $ \_ _ -> case env of
  --           -- can't even happen, but handle it.
  --           -- TODO: is this good?
  --           T.RecursiveEnv eid isEmpty -> pure $ M.RecursiveEnv eid isEmpty
  --           T.Env eid params -> do
  --             -- preserve ID! we don't need to create a new one, because they will all be the same environment!
  --             pure $ M.Env eid params

  --       -- If not, it's a normal environment.
  --       else 
          let mapParams = traverse $ \(v, loc, t) -> (,loc,t) <$> variable v t
          memo' memoEnv (\mem ctx -> ctx { memoEnv = mem }) env $ \env _ -> case env of
            T.RecursiveEnv eid isEmpty -> pure $ M.RecursiveEnv eid isEmpty

            -- xdddd, we don't create a new env id when it has shit inside.
            T.Env eid params | not (null (foldMap (\(_, _, t) -> ftvButIgnoreUnions t) params)) -> do
              M.Env eid <$> mapParams params

            T.Env _ params -> do
              newEID <- newEnvID
              M.Env newEID <$> mapParams params

  -- env' <- for env $ \(v, loc, ctxt) -> do
  --   ctxt' <- ctxt

  --   -- TODO: BAD! After I get deduplication, fix it.
  --   --  TODO: [update] what did I have in mind?????
  --   let uv' = v
  --   pure (uv', loc, ctxt')
  -- -- let env' = (fmap . fmap) fst env
  -- memo memoEnv undefined undefined (envID, env')
  -- -- pure $ M.Env envID env'





-- -- <---------8

-- -- Adds a new monomorphized type.
-- --   Reuses previously added types where possible.
-- typeCon :: UniqueType -> [Type] -> [EnvUnion] -> Text -> Context (Type)
-- typeCon t apps unions nameAppend = do
--   typeFind <- gets typeFind

--   -- Check if we've already monomorphized this type before.
--   case typeFind !? (t, apps, unions) of

--     -- Yes, we have. Just return it.
--     Just (tid, _, _) -> pure $ convertUT tid apps
--     -- No, do funny stuff.
--     Nothing -> do
--       -- Find the type
--       types <- gets types
--       let tdd = case types !? t of
--               Just t' -> t'

--               -- this should not happen when we add memoized definitions in types.
--               Nothing -> error "Should not happen. (But will happen in practice though due to environments) ((why? we still haven't fixed the problem of union'ing environments from outside of module))"

--       -- Make a new type.
--       newTID <- liftIO newUnique
--       let newUniqueType = TI { typeID = newTID, typeName = TC (fromTC t.typeName <> nameAppend) }
--       let newType = convertUT newUniqueType apps

--       -- Add the monotype (to be referred to later)
--       -- Add it here to prevent infinite recursion (for example, in case of pointers, which refer back to the structure, which are mono-ed in the constructor)
--       modify $ \ctx -> ctx { typeFind = Map.insert (t, apps, unions) (newUniqueType, tdd, newType) ctx.typeFind }

--       -- monomorphize by unifying applied
--       --  1. type variables (applied)
--       --  2. unions (from function types in the datatype)
--       -- mDataDef <- mapType (zip (Fix . T.TVar <$> tvs) apps) (zip tunions unions) $ do
--       --   let (T.DD _ _ _ dcs) = oldType
--       --   newDCs <- fmap catMaybes $ for dcs $ \(Annotated anns (T.DC uc ts)) ->
--       --     fmap (Just . Annotated anns) $ do
--       --       -- we need to update searchable constructors (used by 'constructor')
--       --       mts <- traverse mType ts
--       --       conType <- case mts of
--       --             [] -> pure newType
--       --             mts -> do
--       --               union <- emptyUnion
--       --               pure $ Fix $ M.TFun union mts newType

--       --       -- I don't think we need to change UniqueCon, as we will not directly compare constructors from now on? (and in codegen, they will be prefixed with the newUniqueType)
--       --       -- UPDATE: we need to do that. example: Proxy Int and Proxy Bool will use the same constructor, which uses the same enum -> type error in C.
--       --       newCID <- liftIO newUnique
--       --       let uc' = uc { conID = newCID }

--       --       modify $ \ctx -> ctx { conFind = Map.insert (uc, conType) uc' ctx.conFind }
--       --       pure $ M.DC uc' mts

--       --   let newDataDef = Annotated anns $ M.DD newUniqueType newDCs
--       --   pure newDataDef


--       pure newType

-- emptyUnion :: Context (EnvUnion)
-- emptyUnion = do
--   envID <- EnvID <$> liftIO newUnique
--   let env = M.Env { M.envID = envID, M.env = [] }
--   unionID  <- UnionID <$> liftIO newUnique
--   let union = M.EnvUnion { M.unionID = unionID, M.union = NonEmpty.singleton env }
--   pure union


-- -- TODO: Example why we need previous knowledge about applications/later substitutions.
-- -- x =& :1  # we need type knowledge here.
-- -- ....
-- -- f (x a)
-- --  x <&= :printThenReturn(x, 420)
-- -- f(1)
-- -- f(True)
-- retrieveTV :: TVar -> Context (Type)
-- retrieveTV tv = do
--   ctx <- get
--   case lookupTVarMap ctx.tvarMap tv of
--     Nothing -> error "It should not be possible. Probably, because the polymorphic application somehow leaked?"
--     Just t -> pure t


-- -- Both of these functions should contains this logic:
-- --  1. check if variable is a function
-- --     if it's not, leave it unchanged
-- --  2. when it's a function, we want to monomorphize this function. check if we already have the monomorphic version of this function somewhere (eg. from a (UniqueVar, Type) map)
-- --     if it is, return its UniqueVar
-- --  3. if it's not, apply the body and function declaration. then add it to those maps, so next time it will be selected like this.
-- variable :: UniqueVar -> Type -> Context UniqueVar
-- variable ti t = do
--   monofuns <- gets funFind
--   case monofuns !? (ti, t) of
--     Just (M.EnvDef (M.FD _ monofun _ _) _) -> pure monofun
--     Nothing -> do
--       funs <- gets functions
--       case funs !? ti of
--         Nothing -> pure ti
--         Just fun -> do
--           mFunction fun t



-- constructor :: UniqueCon -> Type -> Context UniqueCon
-- constructor ci t = do
--   monocons <- gets conFind

--   -- very stupid, but works. we want to use the type being constructed itself.
--   --  if it's a function, multiple parameters, so return return type
--   --  if it's a TCon, return itself, because enum value
--   let mt = case t of
--         Fix (M.TCon _ _) -> t
--         Fix (M.TFun _ _ mt) -> mt

--   case monocons !? (ci, mt) of
--     Just (M.DC monocon _) -> pure monocon
--     Nothing -> do
--       newCID <- liftIO newUnique
--       let muc = ci { conID = newCID }
--       let mdc = case project t of
--             M.TCon _ _ -> M.DC muc []
--             M.TFun _ args _ -> M.DC muc args

--             -- _ -> error $ "Should not happen. Type: " <> M.ctx M.tType t

--       modify $ \ctx -> ctx { conFind = Map.insert (ci, mt) mdc ctx.conFind }
--       pure muc


-- addFunction :: [Ann] -> Function -> Context ()
-- addFunction anns function@(Function (T.FD _ uv _ _) _) =
--   modify $ \ctx -> ctx { functions = Map.insert uv (Annotated anns function) ctx.functions }

-- addDatatype :: [Ann] -> T.DataDef -> Context ()
-- addDatatype anns dd@(T.DD ut _ _ dc) =
--   let cids = fmap (\(Annotated _ (T.DC uc _)) -> uc) dc

--   -- For each constructor ID adds this datatype.
--   in modify $ \ctx -> ctx
--     { constructors = foldr (`Map.insert` dd) ctx.constructors cids
--     , types = Map.insert ut (Annotated anns dd) ctx.types
--     }


-- -- These functions do
-- --   - map types
-- --   - type function
-- --   - order it and add it to context
-- -- then, these mappings are retrieved by the 'retrieveTV' function
-- mFunction :: Annotated Function -> Type -> Context UniqueVar
-- mFunction (Annotated anns (Function fundec@(T.FD _ tv _ _) ctxBody)) monoType = do
--   -- !!! THIS SHOULD BE REMOVED BECAUSE IT IS SHITTY (by that I meant the placeholderUnionID, which is used to create a function type. But "downcasting" the type to get a union is also very iffy. )
--   let union@(M.EnvUnion placeholderUnionID _) = case monoType of
--         Fix (M.TFun union _ _) -> union
--         tmono -> error $ "SHOULD NOT HAPPEN. This type should have been a function type: " <> show tmono

--   let funtype = fundec2type placeholderUnionID fundec  -- convert from function declaration to a Type Typed
--   mapType [(funtype, monoType)] [] $ do
--     mfd@(M.FD _ uv _ _) <- mFunDec fundec
--     body <- ctxBody

--     let mFun = M.Fun mfd union body

--     -- add it to monomorphized functions
--     modify $ \ctx -> ctx { funFind = Map.insert (tv, monoType) (M.EnvDef mfd union) ctx.funFind, funOrder = ctx.funOrder ++ [Annotated anns mFun] }

--     pure uv

-- mLambda :: Type -> Env Typed -> [(UniqueVar, Type Typed)] -> Context (Expr) -> Context (M.ExprF (Expr))
-- mLambda t tenv tparams tret = do
--   let (Fix (M.TFun union _ _)) = t  -- safe but unsafe cast.
--   env <- mEnv $ mType <$> tenv
--   params <- traverse2 mType tparams
--   expr@(Fix (M.ExprType ret _)) <- tret

--   -- Make fundec (outside :0)
--   uv <- mkLambdaUV
--   let fundec = M.FD env uv params ret
--   let body = NonEmpty.singleton $ Fix $ M.AnnStmt [] $ M.Return expr
--   let mFun = M.Fun fundec union body

--   -- add it to monomorphized functions
--   let envdef = M.EnvDef fundec union
--   modify $ \ctx -> ctx 
--     { funOrder = ctx.funOrder ++ [Annotated [] mFun]
--     }

--   pure $ M.EnvInit envdef

-- mFunDec :: T.FunDec -> Context M.FunDec
-- mFunDec (T.FD env oldUV params ret) = do
--   env' <- mEnv $ fmap mType env
--   newUV <- mkUV oldUV
--   params' <- traverse2 mType params
--   ret' <- mType ret
--   pure $ M.FD env' newUV params' ret'


-- -- Figures out TVar ->Type mappings from two types: one before and one after monomorphization.
-- --  it produces a type map which is then passed to the context in a stack-like way
-- --   Used only in mFunction (for mono-ing functions) and typeCon (for mono-ing types and data definitions)
-- --    however, the one in 'typeCon' is trivial - so much so, that we can specialize it for mFunction OR generalize it for both use cases (pass in a TVar ->Var map instead of two types.)
-- --      TODO: do the generalized version - will be cleaner
-- --   !!! It might not be needed (the interface might be bad)
-- mapType :: [(Type Typed, Type)] -> [(EnvUnion Typed, EnvUnion)] -> Context a -> Context a
-- mapType types2uni unions2uni ctx = do
--   let doMap :: Type Typed -> Type -> Context TypeMap
--       doMap (Fix (T.TFun tunion tparams tret)) (Fix (M.TFun munion mparams mret)) = do
--         -- not sure if we have to do that and how careful should we be with IDs
--         union <- doUnion tunion munion
--         ret <- doMap tret mret
--         pmap <- doMaps $ zip tparams mparams
--         pure $ union <> ret <> pmap

--       -- notice that we don't unify unions here. this information is absent from the type signature of monomorphic types as it is not really needed.
--       doMap (Fix (T.TCon _ tts _)) (Fix (M.TCon _ mts)) = doMaps $ zip tts mts

--       doMap (Fix (T.TVar tv)) mt = pure $ mkTVarMap tv mt
--       doMap mt mm = error $ "Mono: Type mapping failed. Should not happen: " <> show mt <> " | " <> show mm

--       doMaps :: [(Type Typed, Type)] -> Context TypeMap
--       doMaps = fmap fold . traverse (uncurry doMap)

--       doUnion :: EnvUnion Typed -> EnvUnion -> Context TypeMap
--       doUnion tunion@(T.EnvUnion _ tenvs) munion@(M.EnvUnion _ menvs) = do
--         -- make EnvID -> Env map
--         let tenvmap = Map.fromList $ fmap (\env -> (env.envID, env.env)) tenvs
--             menvmap = Map.fromList $ NonEmpty.toList $ fmap (\env -> (env.envID, env.env)) menvs

--         let doEnv :: [(UniqueVar, Locality, Type Typed)] -> [(UniqueVar, Locality, Type)] -> Context TypeMap
--             doEnv tenvs menvs =
--               let fromList = Map.fromList . fmap (\(uv, _, t) -> (uv, t))
--                   envmap = Map.intersectionWith doMap (fromList tenvs) (fromList menvs)
--               in fold <$> sequenceA (Map.elems envmap)

--         let envmap = Map.intersectionWith doEnv tenvmap menvmap
--         didmaps <- fold <$> sequenceA (Map.elems envmap)
--         let unionMap = mkUnionMap tunion munion
--         pure $ unionMap <> didmaps

--       doUnions :: [(EnvUnion Typed, EnvUnion)] -> Context TypeMap
--       doUnions = fmap fold . traverse (uncurry doUnion)

--   mapping <- liftA2 (<>) (doMaps types2uni) (doUnions unions2uni) -- generate this mapping (this will have greater precedence over other)

--   -- Temporarily add mapping in a stack-like way.
--   oldtvarMap <- gets tvarMap
--   modify $ \s -> s { tvarMap = mapping <> oldtvarMap }  -- Reminder: union prefers keys from first argument
--   result <- ctx
--   modify $ \s -> s { tvarMap = oldtvarMap }

--   pure result

-- -- just makes a new UniqueVar (creates a new ID for deduplication with the unmonomorphized)
-- mkUV :: UniqueVar -> Context UniqueVar
-- mkUV uv = do
--   newVar <- liftIO newUnique
--   pure $ uv { varID = newVar }

-- -- used by 'mLambda' (lambdas don't have UniqueVars)
-- mkLambdaUV :: Context UniqueVar
-- mkLambdaUV = do
--   newVar <- liftIO newUnique
--   pure $ VI
--     { varID = newVar
--     , varName = VN "lambda"
--     , mutability = Immutable
--     }

-- convertUT :: UniqueType -> [Type] -> Type
-- convertUT ut apps = Fix $ M.TCon ut apps

-- decoMonoType :: Type -> M.TypeF (Type)
-- decoMonoType = project

-- fundec2type :: UnionID -> T.FunDec -> Type Typed
-- fundec2type placeholderUnionID (T.FD env _ params ret) =
--   let union = T.EnvUnion placeholderUnionID [env]
--   in Fix $ T.TFun union (snd <$> params) ret


-- TypeMap stuff

-- HACK: EnvUnions are only needed when monomorphizing types. However, it's slightly easier right now to add this field. This should probably change later.
data TypeMap = TypeMap (Map TVar M.IType) (Map UnionID M.IEnvUnion) deriving (Eq, Ord)

instance Semigroup TypeMap where
  TypeMap l1 l2 <> TypeMap r1 r2 = TypeMap (l1 <> r1) (l2 <> r2)

instance Monoid TypeMap where
  mempty = TypeMap mempty mempty

-- ahhh, i hate it. TODO: try to figure out if there is a way to do it without doing this mapping.
mapType :: T.Type -> M.IType -> ([(TVar, M.IType)], [(T.EnvUnion, M.IEnvUnion)])
mapType tt mt = case (project tt, project mt) of
  (T.TFun tu tts tret, M.ITFun mu mts mret) -> mapTypes tts mts <> mapType tret mret <> ([], [(tu, mu)])
  (T.TCon _ tts tus, M.ITCon _ mts mus) -> mapTypes tts mts <> ([], zip tus mus)
  (T.TVar tv, t) -> ([(tv, embed t)], [])

  _ -> error $ printf "[COMPILER ERROR]: Fuck."


-- TODO: maybe make a custom datatype from this, since it literally outputs `withTypeMap` arguments.
mapTypes :: [T.Type] -> [M.IType] -> ([(TVar, M.IType)], [(T.EnvUnion, M.IEnvUnion)])
mapTypes tts mts = mconcat $ zipWith mapType tts mts

-- lookupTVarMap :: TypeMap -> TVar -> Maybe (Type)
-- lookupTVarMap (TypeMap tvars _) tvar = tvars !? tvar

-- lookupUnionMap :: TypeMap -> UnionID -> Maybe (EnvUnion)
-- lookupUnionMap (TypeMap _ unions) union = unions !? union

-- mkTVarMap :: TVar -> Type -> TypeMap
-- mkTVarMap tv ty = TypeMap (Map.singleton tv ty) mempty

-- mkUnionMap :: EnvUnion Typed -> EnvUnion -> TypeMap
-- mkUnionMap (T.EnvUnion { T.unionID = unionID }) munion = TypeMap mempty (Map.singleton unionID munion)


-- data Function = Function T.FunDec (Context (NonEmpty (AnnStmtInt)))

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



--------------------------------------------------------
-- THIS IS TYPESAFE BUT BAD. WE BASICALLY ARE REDOING MONOMORPHIZATION IN THE SAME AMOUNT OF LINES. Maybe a less typesafe data structure would be better, as it would cut down on half the file. Or somehow do it in real time - check when the scope exits and the map the instances.
--------------------------------------------------------

type EnvContext = RWST EnvContextUse () EnvMemo IO  -- TEMP: IO temporarily for debugging. should not be used for anything else.
data EnvContextUse = EnvContextUse -- bruh, i dunno
  { usedEnvs :: Set EnvID  -- keysSet of `allInsts` - maybe just call keysSet each time.
  , allInsts :: Map EnvID (Set EnvUse)

  -- this changes with withInstantiation
  -- , currentInst :: TypeMap
  }

data EnvUse = EnvUse (Maybe M.IFunction) M.IEnv

instance Eq EnvUse where
  EnvUse _ le == EnvUse _ re = le == re

instance Ord EnvUse where
  EnvUse _ le `compare` EnvUse _ re = le `compare` re



data EnvMemo = EnvMemo
  { memoIDatatype :: Memo (M.IDataDef, [M.EnvUnion]) (M.DataDef, Map M.IDataCon M.DataCon)
  }

withEnvContext :: Set EnvID -> Map EnvID (Set EnvUse) -> EnvContext a -> IO a
withEnvContext envs allInstantiations x = fst <$> RWS.evalRWST x envUse envMemo
  where
    envUse = EnvContextUse
      { usedEnvs = envIDs
      , allInsts = allInstantiations
      }

    envMemo = EnvMemo
      { memoIDatatype = emptyMemo
      }

    envIDs = envs


mfAnnStmts :: [M.AnnIStmt] -> EnvContext [M.AnnStmt]
mfAnnStmts stmts = fmap catMaybes $ for stmts $ cata $ \(O (Annotated anns stmt)) -> do
  stmt' <- bitraverse mfExpr id stmt
  let s = pure . Just
  let
    body :: NonEmpty (Maybe M.AnnStmt) -> NonEmpty M.AnnStmt
    body stmts =
      let eliminated = catMaybes $ NonEmpty.toList stmts
      in case eliminated of
        [] -> Fix (O (Annotated [] M.Pass)) :| []
        (st:sts) -> st :| sts

  fmap (embed . O . Annotated anns) <$> case stmt' of
    -- TODO: this case is not needed anymore, because of RemoveUnused.
    --  TODO: really?????
    M.EnvDef envID -> do
      envs <- expandEnvironments [envID]
      case envs of
        [] -> error "wtffff. no envs left in EnvDef in Mono"
          -- pure Nothing
        (e:es) -> s $ M.EnvDef (e :| es)
      -- envl <- filterEnvs [env]
      -- case envl of
      --   [] -> pure Nothing
      --   _ -> do
      --     menv <- mfEnv $ mfType <$> env
      --     pure $ Just $ M.EnvDef menv

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
  usedEnvs <- filterEnvs $ NonEmpty.toList union.union

  mappedEnvs <- fmap concat $ for usedEnvs $ \env -> do
    -- let tvs = ftvEnv $ fst <$> env
    -- insts <- instantiations tvs

    -- for (Set.toList insts) $ \inst -> do
    --   withInstantiation inst $ mfEnv $ snd <$> env
    if null (ftvEnvButIgnoreUnions $ fst <$> env)
      then fmap (:[]) $ mfEnv $ snd <$> env
      else do
        envMap <- RWS.asks allInsts
        -- TODO: bruh, why don't we just mfType it then??
        traverse (mfEnv . fmap mfType . (\(EnvUse _ env) -> env)) $ Set.toList $ Map.findWithDefault Set.empty (M.envID env) envMap

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

  -- i dunno if i have to do something stupid here.
  let fundec = fun.functionDeclaration
  env <- mfEnv $ mfType <$> fundec.functionEnv
  params <- traverse2 mfType fundec.functionParameters
  ret <- mfType fundec.functionReturnType

  let mfundec = M.FD { M.functionEnv = env, M.functionId = fundec.functionId, M.functionParameters = params, M.functionReturnType = ret, M.functionNeedsEnvironment = fundec.functionNeedsEnvironment }

  body <- mfAnnStmts $ NonEmpty.toList fun.functionBody
  let completedBody = case body of
        [] ->
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
        _ -> error $ printf "[COMPILER ERROR]: Constructor had an absolutely wrong type (%s)." (M.tType undefined)

  -- mtypes <- traverse mfType ttypes
  munions <- traverse (mfUnion . fmap2 (\t -> (t, mfType t))) imunions

  (_, dcQuery) <- mfDataDef (dd, munions)
  let mdc = fromJust $ dcQuery !? dc
  -- liftIO $ putStrLn $ ctx M.tConDef mdc
  pure mdc


ftvEnv :: M.IEnv -> Set TVar
ftvEnv (M.RecursiveEnv _ _) = Set.empty
ftvEnv (M.Env _ ts) = foldMap (\(_, _, t) -> ftv t) ts

ftv :: M.IType -> Set TVar
ftv = cata $ \case
  M.ITVar tv -> Set.singleton tv

  M.ITCon _ ts _ -> mconcat ts  -- TODO: bug? why am I ignoring union here?
  M.ITFun union args ret -> foldMap fold union <> mconcat args <> ret

-- special ftv
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
  envIds <- RWS.asks usedEnvs

  let f (M.RecursiveEnv eid _) = Set.member eid envIds
      f (M.Env eid _) = Set.member eid envIds
  pure $ filter f envs


-- instantiations :: Set TVar -> EnvContext (Set TypeMap)
-- instantiations tvs | null tvs = pure $ Set.singleton mempty  -- no need to instantiate anything.
-- instantiations tvs = do
--   insts <- RWS.asks allInsts
--   let findInst tv = fromMaybe Set.empty (insts !? tv)
--       separateInsts = Set.map findInst tvs

--   -- now we need to do a cartesian product of those fuken tings
--   let cartesianJoin :: Set TypeMap -> Set TypeMap -> Set TypeMap
--       cartesianJoin l r = Set.map (uncurry (<>)) $ Set.cartesianProduct l r

--       cartesiand = foldr1 cartesianJoin separateInsts

--   pure cartesiand


-- withInstantiation :: TypeMap -> EnvContext a -> EnvContext a
-- withInstantiation newInsts = do
--   -- Map.union t1 t2 prefers t1 keys. So, put newInst on the left.
--   RWS.withRWS $ \ectx s -> (ectx { currentInst = newInsts <> ectx.currentInst }, s)

-- findTV :: TVar -> EnvContext M.Type
-- findTV tv = do
--   TypeMap insts <- RWS.asks currentInst
--   case insts !? tv of
--     Just t -> mfType t

--     Nothing -> error $ printf "[COMPILER ERROR]: TVar %s not matched - types not applied correctly?" (show tv)


traverse2 :: (Traversable t1, Traversable t2, Applicative f) => (a -> f b) -> t1 (t2 a) -> f (t1 (t2 b))
traverse2 = traverse . traverse

sequenceA2 :: (Traversable t1, Traversable t2, Applicative f) => t1 (t2 (f a)) -> f (t1 (t2 a))
sequenceA2 = traverse sequenceA


-- fokin instances
instance Foldable ((,,) a b) where
  foldr f x (_, _, y) = f y x

instance Traversable ((,,) a b) where
  traverse f (a, b, x) = (a, b,) <$> f x

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 = fmap . fmap
-- fmap3 = fmap . fmap . fmap

