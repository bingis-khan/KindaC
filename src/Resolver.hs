{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, RecursiveDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# HLINT ignore "Use concatMap" #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
module Resolver (resolve, ResolveError) where

import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Foldable (fold, for_)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map, (!?))
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map

import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Applicative ((<|>))
import Data.Set (Set, (\\))
import Data.Bifoldable (bifold)
import qualified Data.Set as Set

import AST.Common
-- import AST.Converged (Prelude(..))
import qualified AST.Prelude as Prelude
import AST.Untyped (U)
import qualified AST.Untyped as U
import AST.Resolved
import qualified AST.Resolved as R
import qualified AST.Typed (Mod(..))
import Data.Fix (Fix(..))
import Data.Functor ((<&>))
import Data.Biapplicative (first)
import qualified Data.Text as Text
import Data.Maybe (mapMaybe)
import Data.Semigroup (sconcat)
import Data.Traversable (for)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Either (rights, lefts)
import Data.List (find)
import AST.Def (type (:.)(O), Annotated (..), Binding (..))
import qualified AST.Def as Def
import AST.Prelude (Prelude (..))
import Control.Monad (when, foldM)




-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> Module U -> IO ([ResolveError], Module R)
resolve mPrelude (U.Mod ustmts) = do
  let newState = maybe emptyState mkState mPrelude
  (rstmts, state, errs) <- RWST.runRWST (rStmts ustmts) () newState

  let topLevelScope = NonEmpty.head state.scopes
  let moduleExports = scopeToExports topLevelScope

  let rmod = R.Mod { toplevel = rstmts, exports = moduleExports, allFunctions = state.functions, allDatatypes = state.datatypes, allClasses = state.classes, allInstances = state.instances }

  return (errs, rmod)


rStmts :: [AnnStmt U] -> Ctx [AnnStmt R]
rStmts = traverse -- traverse through the list with Ctx
  rStmt' -- go through Stmt recursively with Ctx. cata (fmap embed . ...) is transverse without the forall type.
  where
    rStmt' = cata (fmap embed . (\(O utStmt) -> O <$> rStmt utStmt))
    -- actual logic
    -- maybe try to generalize it if possible using traverse n shit
    rStmt (Annotated anns uStmt) =
      let stmt = pure . Annotated anns
          pass = pure $ Annotated [] Pass
      in case uStmt of
      Print e -> do
        re <- rExpr e
        stmt $ Print re
      Assignment name e -> do
        re <- rExpr e
        vid <- newVar name
        stmt $ Assignment vid re
      Pass -> stmt Pass
      Mutation name () accesses e -> do
        re <- rExpr e
        let raccesses = flip map accesses $ \case  -- noop to map "phase"
              MutRef -> MutRef
              MutField mem -> MutField mem
        (loc, vf) <- resolveVar name

        case vf of
          R.DefinedVariable vid | loc == Def.Local ->
            stmt $ Mutation vid loc raccesses re

          -- when we're using a ref, we're actually mutating outside shit, so it's good.
          R.DefinedVariable vid | MutRef `elem` raccesses -> do
            stmt $ Mutation vid loc raccesses re

          R.DefinedVariable vid -> do
            err $ CannotMutateNonLocalVariable name

            stmt $ Mutation vid loc raccesses re

          R.DefinedFunction fun _ -> do
            err $ CannotMutateFunctionDeclaration fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ Mutation vid loc [] re

          R.ExternalFunction fun _ -> do
            err $ CannotMutateFunctionDeclaration fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ Mutation vid loc [] re

          R.DefinedClassFunction (CFD _ cfdUV _ _ _) _ -> do
            err $ CannotMutateFunctionDeclaration cfdUV.varName

            vid <- generateVar name
            stmt $ Mutation vid loc [] re

          R.ExternalClassFunction (CFD _ cfdUV _ _ _) _ -> do
            err $ CannotMutateFunctionDeclaration cfdUV.varName

            vid <- generateVar name
            stmt $ Mutation vid loc [] re


      If (IfStmt { condition, ifTrue, ifElifs, ifElse }) -> do
        rcond <- rExpr condition
        rIfTrue <- scope $ sequenceA ifTrue
        rElseIfs <- traverse (\(c, b) -> do
          rc <- rExpr c
          tb <- rBody b
          pure (rc, tb)) ifElifs
        rElseBody <- traverse rBody ifElse
        stmt $ If $ IfStmt rcond rIfTrue rElseIfs rElseBody
      Switch switch cases -> do
        rswitch <- rExpr switch
        rcases <- traverse rCase cases
        stmt $ Switch rswitch rcases
      ExprStmt e -> do
        re <- rExpr e
        stmt $ ExprStmt re
      Return e -> do
        mre <- traverse rExpr e
        re <- case mre of
          Just re -> pure re
          Nothing -> do
            uc <- unit
            eid <- newEnvID
            pure $ Fix $ N () (Con uc eid)

        stmt $ Return re

      While cond bod -> do
        rcond <- rExpr cond
        rbod <- scope $ sequenceA bod
        stmt $ While rcond rbod

      Other (U.DataDefinition dd) -> mdo
        tid <- generateType dd.ddName
        -- tying the knot for the datatype definition

        let dataDef = DD tid tvars rCons anns
        registerDatatype dataDef


        let tvars = mkTVars (Def.BindByType tid) dd.ddScheme
        rCons <- bindTVars tvars $ case dd.ddCons of
          Right cons ->
            fmap Right $ for cons $ \(DC () cname ctys conAnns) -> do
              cid <- generateCon cname

              -- TODO: throw an error if there is more than one constructor with the same name in the same datatype.
              -- TODO: also, can we redeclare constructors (in another datatype in the same scope?)
              rConTys <- traverse rType ctys
              let rCon = DC dataDef cid rConTys conAnns
              newCon rCon

              pure rCon

          Left recs ->
            fmap Left $ for recs $ \(Annotated recAnns (mem, t)) -> do
              t' <- rType t
              pure $ Annotated recAnns (mem, t')

        pass

      Fun (U.FunDef (FD () name params ret uconstraints) body) -> do
        vid <- generateVar name  -- NOTE: this is added to scope in `newFunction` (for some reason.) TODO: change it later (after I finish implementing records.) TODO: to what?????

        constraints <- rConstraints uconstraints

        -- get all unbound tvars
        let allTypes = catNotDeclared $ ret : (snd <$> params)
        tvars <- fmap mconcat $ for allTypes $ cata $ \case
              TO utv -> tryResolveTVar utv <&> \case
                Just _ ->  Set.empty  -- don't rebind existing tvars. (scoped tvars. but maybe a function declaration should rebind them.)
                Nothing -> Set.singleton $ bindTVar (defaultEmpty utv constraints) (BindByVar vid) utv
              t -> fold <$> sequenceA t

        rec
          let function = Function (FD env vid rparams rret (error "what should the scheme be here?")) rbody
          newFunction function

          eid <- newEnvID
          (rparams, rret, rbody) <- bindTVars (Set.toList tvars) $ closure eid $ do
            rparams' <- traverse (\(n, t) -> do
              rn <- rDecon n
              rt <- rDeclaredType t
              return (rn, rt)) params
            rret' <- rDeclaredType ret
            rbody' <- rBody $ rStmt' <$> body
            pure (rparams', rret', rbody')

          -- set the environment
          --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
          -- TODO: maybe just make it a part of 'closure'?
          let innerEnv = Set.delete (R.PDefinedVariable vid) $ sconcat $ gatherVariables <$> rbody
          env <- mkEnv eid innerEnv

        stmt $ Fun function

      -- REF: How are instances selected in Haskell: https://www.youtube.com/watch?v=XfIlhJFmw3c
      -- REF: https://wiki.haskell.org/index.php?title=Orphan_instance
      --  > Type class instances are special in that they don't have a name and cannot be imported explicitly. This also means that they cannot be excluded explicitly. All instances defined in a module A are imported automatically when importing A, or importing any module that imports A, directly or indirectly. 
      Other (U.ClassDefinition cd) -> do
        uc <- generateClass cd.classID

        -- scoped dependent types.
        rec
          let rcd = ClassDef
                { classID = uc
                -- , classDependentTypes = deps   -- TEMP remove
                , classFunctions = fundecs
                }

          -- TODO: define dependent types... at least, later
          -- let _ = cd.classDependentTypes
          -- let deps = []

          fundecs <- for cd.classFunctions $ \(CFD () name params ret uconstraints) -> do
            funid <- generateVar name

            constraints <- rConstraints uconstraints

            -- get all unbound tvars (HACK: copied from DefinedFunction)
            let allTypes = ret : (snd <$> params)
            tvars <- fmap mconcat $ for allTypes $ cata $ \case
                  NormalType (TO utv) -> tryResolveTVar utv <&> \case
                    Just _ ->  Set.empty  -- don't rebind existing tvars.
                    Nothing -> Set.singleton $ R.bindTVar (defaultEmpty utv constraints) (BindByVar funid) utv
                  t -> fold <$> sequenceA t

            -- HACK: ALSO COPIED FROM DefinedFunction!!
            (rparams, rret) <- bindTVars (Set.toList tvars) $ do
              rparams' <- traverse (\(n, t) -> do
                rn <- rDecon n
                rt <- rClassType t
                return (rn, rt)) params
              rret' <- rClassType ret
              pure (rparams', rret')

            pure $ CFD rcd funid rparams rret ()

          registerClass rcd
        pass


      Inst rinst -> mdo
        klass <- resolveClass rinst.instClass

        klassType <- resolveType $ fst rinst.instType
        constraints <- rConstraints rinst.instConstraints

        let instTVars = map (\utv -> R.bindTVar (Def.defaultEmpty utv constraints) (BindByInst (R.asUniqueClass klass)) utv) $ snd rinst.instType

        -- constraints <- rConstraints klass (zip (snd rinst.instType) instTVars) rinst.instConstraints

        let inst = InstDef
              { instClass = klass
              , instType = (klassType, instTVars)
              , instConstraints = ()
              -- , R.instDependentTypes = []  -- TODO: temporary!
              , instFuns = fns
              }

        -- TEMP: should `registerInst` here, but I have a problem with recursive definitions.
        -- It also fixed the problem


        fns <- for rinst.instFuns $ \ifn -> do
          cfd <- findFunctionInClass ifn.instFunDec.functionId klass
          vid <- generateVar ifn.instFunDec.functionId

          constraints <- rConstraints ifn.instFunDec.functionOther

          -- get all unbound tvars
          let allTypes = catNotDeclared $ ifn.instFunDec.functionReturnType : (snd <$> ifn.instFunDec.functionParameters)
          tvars <- fmap mconcat $ for allTypes $ cata $ \case
                TO utv -> tryResolveTVar utv <&> \case
                  Just _ ->  Set.empty  -- don't rebind existing tvars.
                  Nothing -> Set.singleton $ R.bindTVar (Def.defaultEmpty utv constraints) (BindByVar vid) utv
                t -> fold <$> sequenceA t

          eid <- newEnvID
          (rparams, rret, rbody) <- bindTVars (Set.toList tvars) $ closure eid $ do
            rparams' <- traverse (\(n, t) -> do
              rn <- rDecon n
              rt <- rDeclaredType t
              return (rn, rt)) ifn.instFunDec.functionParameters
            rret' <- rDeclaredType ifn.instFunDec.functionReturnType
            rbody' <- rBody $ rStmt' <$> ifn.instFunBody
            pure (rparams', rret', rbody')

          -- set the environment
          --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
          -- TODO: maybe just make it a part of 'closure'?
          let innerEnv = Set.delete (R.PDefinedVariable vid) $ sconcat $ gatherVariables <$> rbody
          env <- mkEnv eid innerEnv
          let fundec = FD env vid rparams rret ()

          pure InstFun
            { instFunDec = fundec
            , instFunBody = rbody
            , instDef = inst
            -- , classFunctionPrototypeUniqueVar = protovid  -- TEMP remove
            , instClassFunDec = cfd
            }


        registerInst inst

        stmt $ Inst inst

    rCase :: CaseF U (Expr U) (Ctx (AnnStmt R)) -> Ctx (CaseF R (Expr R) (AnnStmt R))
    rCase kase = do
      rdecon <- rDecon kase.deconstruction
      mrCond <- traverse rExpr kase.caseCondition
      rbody <- rBody kase.caseBody
      pure $ Case rdecon mrCond rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA

currentLevel :: Ctx Int
currentLevel = subtract 1 . length <$> RWS.gets scopes


-- must be called BEFORE binding tvars. It checks and errors out if there is a bound tvar that's being constrained.
rConstraints :: XClassConstraints U -> Ctx (Map Def.UnboundTVar (Set Class))
rConstraints constraints = do
  let f m (U.CC klass utv) = do
        rklass <- resolveClass klass
        tryResolveTVar utv >>= \case
          Just tv -> do
            err $ FurtherConstrainingExistingTVar tv (R.asUniqueClass rklass)
            pure m
          Nothing -> do
            pure $ Map.insertWith (<>) utv (Set.singleton rklass) m

  foldM f Map.empty constraints

rDecon :: Decon U -> Ctx (Decon R)
rDecon = transverse $ \(N () d) -> fmap (N ()) $ case d of
  CaseVariable var -> do
    rvar <- newVar var
    pure $ CaseVariable rvar
  CaseConstructor conname decons -> do
    con <- resolveCon conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor conname
        placeholderCon conname

    CaseConstructor con <$> sequenceA decons
  CaseRecord tyName members -> do
    ty <- resolveType tyName
    mems <- traverse sequenceA members

    -- NOTE: we can check here if members exist in datatype.
    -- however it won't be so simple if we add anonymous structs.
    -- basically, it'll be checked during typechecking..?
    -- TODO: what's better?
    case tryGetMembersFromDatatype ty of
      Nothing -> pure ()
      Just recs -> do
        let tyMems = Set.fromList $ NonEmpty.toList recs
        let currentMems = Set.fromList $ NonEmpty.toList $ fst <$> mems
        let extraneousMems = currentMems \\ tyMems

        for_ extraneousMems $ \mem ->
          err $ MemberNotInDataDef mem (R.asUniqueType ty, NonEmpty.toList recs)

        let memDefinitions = Map.unionsWith (+) $ flip Map.singleton (1 :: Int) . fst <$> mems
        let redefinedMems = fmap fst $ filter ((>1) . snd) $ Map.toList memDefinitions  -- find member variables that were defined more than once.
        for_ redefinedMems $ \mem ->
          err $ RedefinedMember mem

    pure $ CaseRecord ty mems

rExpr :: Expr U -> Ctx (Expr R)
rExpr = cata $ \(N () expr) -> embed . N () <$> case expr of  -- transverse, but unshittified
  Lit x -> pure $ Lit x
  Var v () -> do
    (l, vid) <- resolveVar v
    pure $ Var vid l
  Con conname () -> do
    con <- resolveCon conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor conname
        placeholderCon conname

    -- you may not use the constructor of a pointer!
    --  only when deconstructing!
    when (isPointer con) $ err UsingPointerConstructor

    eid <- newEnvID
    pure $ Con con eid
  MemAccess e memname -> do
    rexpr <- e
    pure $ MemAccess rexpr memname
  RecCon tyname mems -> do
    ty <- resolveType tyname
    mems' <- Def.sequenceA2 mems

    case R.tryGetMembersFromDatatype ty of
      Nothing -> pure ()
      Just recs -> do
        let tyMems = Set.fromList $ NonEmpty.toList recs
        let currentMems = Set.fromList $ NonEmpty.toList $ fst <$> mems

        -- TODO: I don't have a Show instance for DataDef because lazy, so this should suffice for now.
        let dd = (R.asUniqueType ty, NonEmpty.toList recs)

        -- report members not in the current datatype.
        let extraneousMems = currentMems \\ tyMems
        for_ extraneousMems $ \mem ->
          err $ MemberNotInDataDef mem dd

        -- report members that were not defined, but should have been.
        let undefinedMems = tyMems \\ currentMems
        for_ undefinedMems $ \mem ->
          err $ DidNotDefineMember mem dd

        -- report redefinitions.
        let memDefinitions = Map.unionsWith (+) $ flip Map.singleton (1 :: Int) . fst <$> mems
        let redefinedMems = fmap fst $ filter ((>1) . snd) $ Map.toList memDefinitions  -- find member variables that were defined more than once.
        for_ redefinedMems $ \mem ->
          err $ RedefinedMember mem

    pure $ RecCon ty mems'

  RecUpdate e mems -> do
    e' <- e
    mems' <- Def.sequenceA2 mems
    pure $ RecUpdate e' mems'

  Op l op r -> Op <$> l <*> pure op <*> r
  Call c args -> Call <$> c <*> sequenceA args
  As e t -> As <$> e <*> rType t
  Lam () params body -> do
    lamId <- lambdaVar
    eid <- newEnvID
    (rParams, rBody) <- closure eid $ do
      rParams <- traverse newVar params
      rBody <- scope body
      pure (rParams, rBody)

    let innerEnv = gatherVariablesFromExpr rBody -- TODO: environment making in 'closure' function.
    env <- mkEnv eid innerEnv
    pure $ Lam (R.LamDec lamId env) rParams rBody

  Ref e -> Ref <$> e
  Deref e -> Deref <$> e

rType :: Type U -> Ctx (Type R)
rType = transverse rType'

rDeclaredType :: DeclaredType U -> Ctx (DeclaredType R)
rDeclaredType = \case
  TypeNotDeclared -> pure TypeNotDeclared
  DeclaredType t -> DeclaredType <$> rType t

rClassType :: ClassType U -> Ctx (ClassType R)
rClassType = transverse $ \case
  Self -> pure Self
  NormalType t -> NormalType <$> rType' t

rType' :: TypeF U (Ctx a) -> Ctx (TypeF R a)
rType' = \case
  TCon t tapps () -> do
    rt <- resolveTypeOrClass t
    rtApps <- sequenceA tapps
    case (rt, rtApps) of
      (Left klass, []) ->
        pure $ TO $ TClass klass
      (Right dt, _) -> do
        pure $ TCon dt rtApps ()

      (Left klass, _:_) -> do
        err $ AppliedTypesToClassInType (R.asUniqueClass klass)

        -- what's better for error reporting here? returning a type or a class? what would produce better error messages?
        pure $ TO $ TClass klass

  TO v -> do
    tv <- resolveTVar v
    pure $ TO $ TVar tv
  TFun () args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ TFun () rArgs rret


------------
-- Utility
------------

scope :: Ctx a -> Ctx a
scope x = do
  oldScope <- RWST.get  -- enter scope
  x' <- x               -- evaluate body
  RWST.put oldScope     -- exit scope

  return x'

-- TODO: right now, it only creates a new scope... so it's a bit of a misnomer.
closure :: Def.EnvID -> Ctx a -> Ctx a
closure eid x = do
  oldScope <- RWST.get          -- enter scope

  RWST.modify $ \state@(CtxState { scopes = scopes', envStack = envStack' }) -> state { scopes = emptyScope <| scopes', envStack = eid : envStack' }
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] CtxState IO  -- I might add additional context later.

data CtxState = CtxState
  { scopes :: NonEmpty Scope
  , envStack :: [Def.EnvID]
  , inLambda :: Bool  -- hack to check if we're in a lambda currently. the when the lambda is not in another lambda, we put "Local" locality.
  , tvarBindings :: Map Def.UnboundTVar (TVar R)

  , prelude :: Maybe Prelude  -- Only empty when actually parsing prelude.

  -- we need to keep track of each defined function to actually typecheck it.
  , functions :: [Function R]
  , datatypes :: [DataDef R]
  , classes   :: [ClassDef R]
  , instances :: [InstDef R]
  }

data Scope = Scope
  { varScope :: Map Def.VarName R.VariableProto
  , conScope :: Map Def.ConName R.Constructor
  , tyScope :: Map Def.TCon (Either Class R.DataType)

  , instScope :: Map Class (Map R.DataType R.Inst)
  }

emptyState :: CtxState
emptyState =
  CtxState { scopes = NonEmpty.singleton emptyScope, envStack = mempty, tvarBindings = mempty, prelude = Nothing, inLambda = False, functions = mempty, datatypes = mempty, classes = mempty, instances = mempty }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty, instScope = mempty }

getScopes :: Ctx (NonEmpty Scope)
getScopes = RWST.gets scopes

-- Add later after I do typechecking.
mkState :: Prelude -> CtxState
mkState prel = CtxState
  { scopes = NonEmpty.singleton initialScope
  , envStack = mempty
  , tvarBindings = mempty
  , prelude = Just prel
  , inLambda = False
  , functions = mempty
  , datatypes = mempty
  , classes = mempty
  , instances = mempty
  } where

    -- convert prelude to a scope
    initialScope = Scope
      { varScope = exportedVariables <> exportedFunctions

      , conScope = Map.fromList $ concat $ preludeExports.datatypes <&> \dd -> foldMap (fmap (\dc -> (dc.conID.conName, R.ExternalConstructor dc))) dd.ddCons
      , tyScope  = Map.fromList $ preludeExports.datatypes <&> \dd -> (dd.ddName.typeName, Right $ R.ExternalDatatype dd)

      , instScope = Map.fromListWith (<>) $ preludeExports.instances <&> \inst -> (ExternalClass inst.instClass, Map.singleton (R.ExternalDatatype $ fst inst.instType) (ExternalInst inst))
      }

    exportedVariables = Map.fromList $ preludeExports.variables <&> \uv ->
      (uv.varName, PDefinedVariable uv)
    exportedFunctions = Map.fromList $ preludeExports.functions <&> \fn ->
      (fn.functionDeclaration.functionId.varName, PExternalFunction fn)

    preludeExports = prel.tpModule.exports

generateVar :: Def.VarName -> Ctx Def.UniqueVar
generateVar name = do
  vid <- liftIO newUnique
  let var = Def.VI { varID = vid, varName = name }
  pure var

newFunction :: Function R -> Ctx ()
newFunction fun = do
  let uv = fun.functionDeclaration.functionId
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.PDefinedFunction fun) sc.varScope }
  RWST.modify $ \s -> s { functions = fun : s.functions }

newVar :: Def.VarName -> Ctx Def.UniqueVar
newVar name = do
  uv <- generateVar name
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.PDefinedVariable uv) sc.varScope }
  pure uv

lambdaVar :: Ctx Def.UniqueVar
lambdaVar = do
  vid <- liftIO newUnique
  let var = Def.VI { varID = vid, varName = Def.VN (Text.pack "lambda") }
  return var

resolveVar :: Def.VarName -> Ctx (Def.Locality, R.Variable)
resolveVar name = do
  curlev <- currentLevel
  allScopes <- getScopes
  case lookupScope curlev name (fmap varScope allScopes) of
    Just (l, v) -> (l,) <$> protoVariableToVariable v
    Nothing -> do
      err $ UndefinedVariable name
      (Def.Local,) . R.DefinedVariable <$> placeholderVar name

protoVariableToVariable :: R.VariableProto -> Ctx R.Variable
protoVariableToVariable = \case
  R.PDefinedVariable uv -> pure $ R.DefinedVariable uv
  R.PDefinedFunction fn -> do
    snapshot <- getScopeSnapshot
    pure $ R.DefinedFunction fn snapshot
  R.PExternalFunction fn -> do
    snapshot <- getScopeSnapshot
    pure $ R.ExternalFunction fn snapshot
  R.PDefinedClassFunction cfd -> do
    snapshot <- getScopeSnapshot
    pure $ R.DefinedClassFunction cfd snapshot
  R.PExternalClassFunction cfd -> do
    snapshot <- getScopeSnapshot
    pure $ R.ExternalClassFunction cfd snapshot

placeholderVar :: Def.VarName -> Ctx Def.UniqueVar
placeholderVar = generateVar


generateCon :: Def.ConName -> Ctx Def.UniqueCon
generateCon name = do
  cid <- liftIO newUnique
  let con = Def.CI { conID = cid, conName = name }
  pure con

newCon :: DataCon R -> Ctx ()
newCon dc = do
  modifyThisScope $ \sc -> sc { conScope = Map.insert dc.conID.conName (R.DefinedConstructor dc) sc.conScope }

resolveCon :: Def.ConName -> Ctx (Maybe R.Constructor)
resolveCon name = do
  allScopes <- getScopes
  curlev <- currentLevel
  -- This has been generalized to return Maybe instead of throwing an error.
  --   WHY? I needed this function somewhere else AND I the usage should be the same.
  --    This is more in line with the spiritual usage of Haskell - bubble up errors and handle them there. this makes it obvious what is happening with the value - no need to check inside the function. (remember this :3)
  let maybeCon = snd <$> lookupScope curlev name (fmap conScope allScopes)
  pure maybeCon

placeholderCon :: Def.ConName -> Ctx R.Constructor
placeholderCon name = do
  uc <- generateCon name

  ti <- generateType $ Def.TC $ "PlaceholderTypeForCon" <> name.fromCN

  -- fill in later with a placeholder type.
  let dc = DC dd uc [] []
      dd = DD ti [] (Right [dc]) []
  pure $ DefinedConstructor dc


generateClass :: Def.ClassName -> Ctx Def.UniqueClass
generateClass cn = do
  cid <- liftIO newUnique
  let uc = Def.TCI { classID = cid, className = cn }
  pure uc

-- memo stuff
registerClass :: ClassDef R -> Ctx ()
registerClass cd = do
  modifyThisScope $ \sc -> sc
    -- class itself
    { tyScope = Map.insert (Def.uniqueClassAsTypeName cd.classID) (Left (R.DefinedClass cd)) sc.tyScope

    -- inner functions
    , varScope = foldr (\cfd@(CFD _ uv _ _ _) -> Map.insert uv.varName (R.PDefinedClassFunction cfd)) sc.varScope cd.classFunctions
    }

  RWST.modify $ \ctx -> ctx { classes = cd : ctx.classes }

resolveClass :: Def.ClassName -> Ctx R.Class
resolveClass cn = do
  allScopes <- getScopes
  curlev <- currentLevel
  let cnAsTCon = Def.TC cn.fromTN :: Def.TCon
  case lookupScope curlev cnAsTCon (fmap tyScope allScopes) of
    Just (_, Left c) -> pure c
    Just (_, Right dd) -> do
      err $ ExpectedClassNotDatatype cn (R.asUniqueType dd)
      placeholderClass cn
    Nothing -> do
      err $ UndefinedClass cn
      placeholderClass cn

placeholderClass :: Def.ClassName -> Ctx R.Class
placeholderClass = undefined

findFunctionInClass :: Def.VarName -> R.Class -> Ctx (XClassFunDec R)
findFunctionInClass vn ecd =
  let
    mcfd = case ecd of
      R.DefinedClass cd -> R.DefinedClassFunDec <$> find (\(CFD _ uv _ _ _) -> uv.varName == vn) cd.classFunctions
      R.ExternalClass cd -> R.ExternalClassFunDec <$> find (\(CFD _ uv _ _ _) -> uv.varName == vn) cd.classFunctions
    cid = R.asUniqueClass ecd
  in case mcfd of
    Just cfd -> pure cfd
    Nothing -> do
      err $ UndefinedFunctionOfThisClass cid vn
      uv <- generateVar vn
      pure $ case ecd of
        R.DefinedClass cd -> R.DefinedClassFunDec $ CFD cd uv [] (Fix Self) ()
        R.ExternalClass cd -> R.ExternalClassFunDec $ CFD cd uv [] (Fix Self) ()


getScopeSnapshot :: Ctx R.ScopeSnapshot
getScopeSnapshot = do
  allScopes <- getScopes

  -- Merge scopes into a flattened projection. Choose left keys, as they are from inner scopes.
  pure $ foldr (Map.unionWith (<>) . instScope) Map.empty allScopes


registerInst :: InstDef R -> Ctx ()
registerInst inst = do
  modifyThisScope $ \sc -> sc
    { instScope = Map.insertWith (<>) inst.instClass (Map.singleton (fst inst.instType) (R.DefinedInst inst)) sc.instScope
    }

  RWST.modify $ \ctx -> ctx { instances = inst : ctx.instances }




-- Generate a new unique type.
generateType :: Def.TCon -> Ctx Def.UniqueType
generateType name = do
  tid <- liftIO newUnique
  let ty = Def.TI { typeID = tid, typeName = name }
  pure ty

registerDatatype :: DataDef R -> Ctx ()
registerDatatype dd = do
  -- Check for duplication first
  -- if it exists, we still replace it, but an error is signaled.
  -- TODO: All of this is iffy. I don't really know what it's doing.
  let name = dd.ddName.typeName
  currentScope <- NonEmpty.head <$> getScopes
  case currentScope.tyScope !? name of
    Just (Right (R.DefinedDatatype _)) -> pure ()
    Just (Right (R.ExternalDatatype _)) -> err $ TypeRedeclaration name  -- maybe we should shadow still?????
    _ -> pure ()

  modifyThisScope $ \sc -> sc { tyScope = Map.insert name (Right $ R.DefinedDatatype dd) sc.tyScope }
  RWST.modify $ \s -> s { datatypes = dd : s.datatypes }
  pure ()

-- NOTE: used only in DataDefs... remove?
mkTVars :: Def.Binding -> [Def.UnboundTVar] -> [TVar R]
mkTVars b = fmap $ R.bindTVar mempty b

bindTVars :: [TVar R] -> Ctx a -> Ctx a
bindTVars tvs cx = do
    oldBindings <- RWS.gets tvarBindings

    -- make bindings and merge them with previous bindings
    let bindings = Map.fromList $ fmap (\tv -> (Def.UTV tv.fromTV, tv)) tvs
    RWS.modify $ \ctx -> ctx { tvarBindings = bindings <> ctx.tvarBindings }

    x <- cx

    RWS.modify $ \ctx -> ctx { tvarBindings = oldBindings }

    pure x

tryResolveTVar :: Def.UnboundTVar -> Ctx (Maybe (TVar R))
tryResolveTVar utv = do
  tvs <- RWS.gets tvarBindings
  pure $ tvs !? utv

resolveTVar :: Def.UnboundTVar -> Ctx (TVar R)
resolveTVar utv = do
  mtv <- tryResolveTVar utv
  case mtv of
    Just tv -> pure tv
    Nothing -> do
      err $ UnboundTypeVariable utv
      placeholderTVar utv

placeholderTVar :: Def.UnboundTVar -> Ctx (TVar R)
placeholderTVar utv = do
  var <- generateVar $ Def.VN $ "placeholderVarForTVar" <> utv.fromUTV
  pure (R.bindTVar mempty (BindByVar var) utv)

resolveType :: Def.TCon -> Ctx R.DataType
resolveType name = do
  tOrC <- resolveTypeOrClass name
  case tOrC of
    Right t -> pure t
    Left c -> do
      let cid = R.asUniqueClass c
      err $ UsingClassNameInPlaceOfType cid
      placeholderType name

resolveTypeOrClass :: Def.TCon -> Ctx (Either R.Class R.DataType)
resolveTypeOrClass name = do
  allScopes <- getScopes
  curlev <- currentLevel
  case lookupScope curlev name (fmap tyScope allScopes) of
    Just (_, typeOrClass) -> pure typeOrClass

    Nothing -> do
      err $ UndefinedType name
      Right <$> placeholderType name

placeholderType :: Def.TCon -> Ctx R.DataType
placeholderType name = do
  -- generate a placeholder type.
  ti <- generateType $ Def.TC $ "PlaceholderType" <> name.fromTC

  let dd = DD ti [] (Right []) []
  pure $ DefinedDatatype dd

modifyThisScope :: (Scope -> Scope) -> Ctx ()
modifyThisScope f =
  let modifyFirstScope (sc :| scs) = f sc :| scs
  in RWST.modify $ \sctx -> sctx { scopes = modifyFirstScope sctx.scopes }

lookupScope :: (Ord b) => Int -> b -> NonEmpty (Map b c) -> Maybe (Def.Locality, c)
lookupScope curlev k = foldr (\(locality, l) r -> (locality,) <$> Map.lookup k l <|> r) Nothing . (\(cur :| envs) -> (Def.Local, cur) :| fmap (\(l, sc) -> (Def.FromEnvironment l, sc)) (zip [curlev-1, curlev-2 .. 0] envs))


unit :: Ctx R.Constructor
unit = do
  ctx <- RWST.get
  case ctx.prelude of
    -- When prelude was already typechecked, it should always be available.
    Just prelud -> pure $ R.ExternalConstructor prelud.unitValue

    -- When we're resolving prelude, find it from the environment.
    Nothing ->
      resolveCon Prelude.unitName <&> \case
        Just uc -> uc
        Nothing -> error $ "[COMPILER ERROR]: Could not find Unit type with the name: '" <> show Prelude.unitName <> "'. This must not happen."

err :: ResolveError -> Ctx ()
err = RWST.tell .  (:[])

data ResolveError
  = UndefinedVariable Def.VarName
  | UndefinedConstructor Def.ConName
  | UndefinedType Def.TCon
  | UnboundTypeVariable Def.UnboundTVar
  | FurtherConstrainingExistingTVar (TVar R) Def.UniqueClass
  | TypeRedeclaration Def.TCon
  | CannotMutateFunctionDeclaration Def.VarName
  | CannotMutateNonLocalVariable Def.VarName

  | DidNotDefineMember Def.MemName (Def.UniqueType, [Def.MemName])
  | MemberNotInDataDef Def.MemName (Def.UniqueType, [Def.MemName])
  | RedefinedMember    Def.MemName

  | NotARecordType Def.UniqueType

  | UndefinedClass Def.ClassName
  | ExpectedClassNotDatatype Def.ClassName Def.UniqueType
  | UsingClassNameInPlaceOfType Def.UniqueClass  -- IDs are only, because I'm currently too lazy to make a Show instance.
  | UndefinedFunctionOfThisClass Def.UniqueClass Def.VarName

  | AppliedTypesToClassInType Def.UniqueClass

  | UsingPointerConstructor
  deriving Show


-- environment stuff
mkEnv :: Def.EnvID -> Set VariableProto -> Ctx (XEnv R)
mkEnv eid innerEnv = do
  currentEnvStack <- RWS.gets envStack
  locality <- localityOfVariablesAtCurrentScope
  pure $ Env eid currentEnvStack (mapMaybe (\v -> (locality !? R.asPUniqueVar v) <&> \(_, loc) -> (v, loc)) $ Set.toList innerEnv)  -- filters variables to ones that are in the environment.

-- Make a new env ID.
newEnvID :: Ctx Def.EnvID
newEnvID = Def.EnvID <$> liftIO newUnique

localityOfVariablesAtCurrentScope :: Ctx (Map Def.UniqueVar (R.VariableProto, Def.Locality))
localityOfVariablesAtCurrentScope = do
  allScopes <- getScopes
  curlev <- currentLevel
  pure $ foldr (\(locality, l) r -> Map.fromList (fmap (\v -> (R.asPUniqueVar v, (v, locality))) $ Map.elems l.varScope) <> r) mempty $ (\(cur :| envs) -> (Def.Local, cur) :| fmap (\(l, sc) -> (Def.FromEnvironment l, sc)) (zip [curlev-1, curlev-2 .. 0] envs)) allScopes

-- used for function definitions
gatherVariables :: AnnStmt R -> Set R.VariableProto
gatherVariables = cata $ \(O (Annotated _ bstmt)) -> case first gatherVariablesFromExpr bstmt of
  Mutation v _ _ expr -> Set.insert (R.PDefinedVariable v) expr
  Return expr -> gatherVariablesFromExpr expr
  Fun fn ->
    let dec = fn.functionDeclaration
        envVars = Set.fromList $ fst <$> dec.functionEnv.fromEnv
    in envVars
  Inst idef -> foldMap (\fn -> Set.fromList $ fst <$> fn.instFunDec.functionEnv.fromEnv) idef.instFuns
  stmt -> bifold stmt

-- used for lambdas
gatherVariablesFromExpr :: Expr R -> Set VariableProto
gatherVariablesFromExpr = cata $ \(N () e) -> case e of
  Var v _ -> Set.singleton (R.asProto v)  -- TODO: Is this... correct? It's used for making the environment, but now we can just use this variable to know. This is todo for rewrite.
                                --   Update: I don't understand the comment above.
  expr -> fold expr


scopeToExports :: Scope -> Exports R
scopeToExports sc = Exports
  { variables = vars
  , functions = funs
  , datatypes = dts
  , classes   = cls
  , instances = insts
  } where
    vars = mapMaybe (\case { PDefinedVariable var -> Just var; _ -> Nothing }) $ Map.elems sc.varScope

    funs = mapMaybe (\case { PDefinedFunction fun -> Just fun; _ -> Nothing }) $ Map.elems sc.varScope

    dts = mapMaybe (\case { DefinedDatatype dt -> Just dt; _ -> Nothing }) $ rights $ Map.elems sc.tyScope

    cls = mapMaybe (\case { R.DefinedClass cd -> Just cd; _ -> Nothing }) $ lefts $ Map.elems sc.tyScope

    insts = concatMap (mapMaybe (\case { R.DefinedInst inst -> Just inst; _ -> Nothing })) $ Map.elems $ Map.elems <$> sc.instScope


isPointer :: Constructor -> Bool
isPointer con =
  let anns = case con of
        DefinedConstructor dc -> dc.conDataDef.ddAnns
        ExternalConstructor dc -> dc.conDataDef.ddAnns
  in Def.AActualPointerType `elem` anns
