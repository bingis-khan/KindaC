{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, RecursiveDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# HLINT ignore "Use concatMap" #-}
{-# LANGUAGE OverloadedStrings #-}
module Resolver (resolve, ResolveError) where

import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse, cata, embed)
import Data.Foldable (fold)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map, (!?))
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map

import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Applicative ((<|>))
import Data.Set (Set)
import Data.Bifoldable (bifold)
import qualified Data.Set as Set

import AST.Common (UniqueVar (..), UniqueCon (..), UniqueType (..), Locality (..), VarName (..), TCon (..), ConName (..), Annotated (..), (:.) (..), UnboundTVar (..), TVar (..), Binding (..), bindTVar)
import AST.Converged (Prelude(..))
import qualified AST.Converged as Prelude
import AST.Untyped (StmtF (..), DataDef (..), DataCon (..), FunDec (..), ExprF (..), TypeF (..))
import qualified AST.Untyped as U
import AST.Resolved (Env (..), Exports (..), Variable (..), Datatype (..), Constructor (..))
import qualified AST.Resolved as R
import qualified AST.Typed as T
import Data.Fix (Fix(..))
import Data.Functor ((<&>))
import Data.Biapplicative (first)
import qualified Data.Text as Text
import Data.Maybe (mapMaybe, catMaybes)
import Data.Semigroup (sconcat)
import Data.Traversable (for)
import qualified Control.Monad.Trans.RWS as RWS




-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> U.Module -> IO ([ResolveError], R.Module)
resolve mPrelude (U.Mod ustmts) = do
  let newState = maybe emptyState mkState mPrelude
  (rstmts, state, errs) <- RWST.runRWST (rStmts ustmts) () newState

  let topLevelScope = NonEmpty.head state.scopes
  let moduleExports = scopeToExports topLevelScope

  let rmod = R.Mod { toplevel = rstmts, exports = moduleExports, functions = state.functions, datatypes = state.datatypes }

  return (errs, rmod)


rStmts :: [U.AnnStmt] -> Ctx [R.AnnStmt]
rStmts = traverse -- traverse through the list with Ctx
  $ cata (fmap embed . (\(O utStmt) -> O <$> rStmt utStmt)) -- go through Stmt recursively with Ctx. cata (fmap embed . ...) is transverse without the forall type.
  where
    -- actual logic
    -- maybe try to generalize it if possible using traverse n shit
    rStmt (Annotated anns uStmt) =
      let stmt = pure . Annotated anns
          pass = pure $ Annotated [] R.Pass
      in case uStmt of
      Print e -> do
        re <- rExpr e
        stmt $ R.Print re
      Assignment name e -> do
        re <- rExpr e
        vid <- newVar name
        stmt $ R.Assignment vid re
      Pass -> stmt R.Pass
      Mutation name e -> do
        re <- rExpr e
        (loc, vf) <- resolveVar name

        case vf of
          R.DefinedVariable vid ->
            stmt $ R.Mutation vid loc re

          R.DefinedFunction fun -> do
            err $ CannotMutateFunctionDeclaration fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ R.Mutation vid Local re
            
          R.ExternalFunction fun -> do
            err $ CannotMutateFunctionDeclaration fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ R.Mutation vid Local re


      If cond ifTrue elseIfs elseBody -> do
        rcond <- rExpr cond
        rIfTrue <- scope $ sequenceA ifTrue
        rElseIfs <- traverse (\(c, b) -> do
          rc <- rExpr c
          tb <- rBody b
          pure (rc, tb)) elseIfs
        rElseBody <- traverse rBody elseBody
        stmt $ R.If rcond rIfTrue rElseIfs rElseBody
      Switch switch cases -> do
        rswitch <- rExpr switch
        rcases <- traverse rCase cases
        stmt $ R.Switch rswitch rcases
      ExprStmt e -> do
        re <- rExpr e
        stmt $ R.ExprStmt re
      Return e -> do
        mre <- traverse rExpr e
        re <- case mre of
          Just re -> pure re
          Nothing -> do
            uc <- unit
            pure $ Fix (R.Con uc)

        stmt $ R.Return re
      DataDefinition (DD tyName unboundTyParams cons) -> mdo
        tid <- generateType tyName
        -- tying the knot for the datatype definition

        let dataDef = R.DD tid tvars rCons anns
        registerDatatype dataDef

        let tvars = mkTVars (BindByType tid) unboundTyParams
        rCons <- bindTVars tvars $ do
          for cons $ \(Annotated conAnns (DC cname ctys)) -> do
            cid <- generateCon cname

            -- TODO: throw an error if there is more than one constructor with the same name in the same datatype.
            -- TODO: also, can we redeclare constructors (in another datatype in the same scope?)
            rConTys <- traverse rType ctys
            let rCon = R.DC dataDef cid rConTys conAnns
            newCon rCon

            pure rCon
        pass

      FunctionDefinition (FD name params ret) body -> do
        vid <- generateVar name

        -- get all unbound tvars
        let allTypes = catMaybes $ ret : (snd <$> params)
        tvars <- fmap mconcat $ for allTypes $ cata $ \case
              TVar utv -> tryResolveTVar utv <&> \case
                Just _ ->  Set.empty  -- don't rebind existing tvars.
                Nothing -> Set.singleton $ bindTVar (BindByVar vid) utv
              t -> fold <$> sequenceA t

        rec
          let function = R.Function (R.FD env vid rparams rret) rbody
          newFunction function

          (rparams, rret, rbody) <- bindTVars (Set.toList tvars) $ closure $ do
            rparams' <- traverse (\(n, t) -> do
              rn <- newVar n
              rt <- traverse rType t
              return (rn, rt)) params
            rret' <- traverse rType ret
            rbody' <- rBody body
            pure (rparams', rret', rbody')

          -- set the environment
          --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
          -- TODO: maybe just make it a part of 'closure'?
          let innerEnv = Set.delete vid $ sconcat $ gatherVariables <$> rbody
          env <- mkEnv innerEnv

        stmt $ R.EnvDef function

    rCase :: U.CaseF U.Expr (Ctx R.AnnStmt) -> Ctx (R.Case R.Expr R.AnnStmt)
    rCase kase = do
      rdecon <- rDecon kase.deconstruction
      mrCond <- traverse rExpr kase.caseCondition
      rbody <- rBody kase.body
      pure $ R.Case rdecon mrCond rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA

rDecon :: U.Decon -> Ctx R.Decon
rDecon = transverse $ \case
  U.CaseVariable var -> do
    rvar <- newVar var
    pure $ R.CaseVariable rvar
  U.CaseConstructor conname decons -> do
    con <- resolveCon conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor conname
        placeholderCon conname

    R.CaseConstructor con <$> sequenceA decons

rExpr :: U.Expr -> Ctx R.Expr
rExpr = cata $ fmap embed . \case  -- transverse, but unshittified
  Lit x -> pure $ R.Lit x
  Var v -> do
    (l, vid) <- resolveVar v
    pure $ R.Var l vid
  Con conname -> do
    con <- resolveCon conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor conname
        placeholderCon conname

    pure $ R.Con con
  Op l op r -> R.Op <$> l <*> pure op <*> r
  Call c args -> R.Call <$> c <*> sequenceA args
  As e t -> R.As <$> e <*> rType t
  Lam params body -> do
    lamId <- lambdaVar
    (rParams, rBody) <- closure $ do
      rParams <- traverse newVar params
      rBody <- scope body
      pure (rParams, rBody)

    let innerEnv = gatherVariablesFromExpr rBody -- TODO: environment making in 'closure' function.
    env <- mkEnv innerEnv
    pure $ R.Lam lamId env rParams rBody


rType :: U.Type -> Ctx R.Type
rType = transverse $ \case
  TCon t tapps -> do
    rt <- resolveType t
    rtApps <- sequenceA tapps
    pure $ R.TCon rt rtApps
  TVar v -> do
    tv <- resolveTVar v
    pure $ R.TVar tv
  TFun args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ R.TFun rArgs rret


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
closure :: Ctx a -> Ctx a
closure x = do
  oldScope <- RWST.get          -- enter scope

  RWST.modify $ \state@(CtxState { scopes = scopes' }) -> state { scopes = emptyScope <| scopes' }
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


type Ctx = RWST () [ResolveError] CtxState IO  -- I might add additional context later.

data CtxState = CtxState
  { scopes :: NonEmpty Scope
  , inLambda :: Bool  -- hack to check if we're in a lambda currently. the when the lambda is not in another lambda, we put "Local" locality.
  , tvarBindings :: Map UnboundTVar TVar

  , prelude :: Maybe Prelude  -- Only empty when actually parsing prelude.

  -- we need to keep track of each defiend function to actually typecheck it.
  , functions :: [R.Function]
  , datatypes :: [R.DataDef]
  }

data Scope = Scope
  { varScope :: Map VarName R.Variable
  , conScope :: Map ConName R.Constructor
  , tyScope :: Map TCon R.Datatype
  }

emptyState :: CtxState
emptyState =
  CtxState { scopes = NonEmpty.singleton emptyScope, tvarBindings = mempty, prelude = Nothing, inLambda = False, functions = mempty, datatypes = mempty }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty }

getScopes :: Ctx (NonEmpty Scope)
getScopes = RWST.gets scopes

-- Add later after I do typechecking.
mkState :: Prelude -> CtxState
mkState prel = CtxState
  { scopes = NonEmpty.singleton initialScope
  , tvarBindings = mempty
  , prelude = Just prel
  , inLambda = False
  , functions = mempty
  , datatypes = mempty
  } where

    -- convert prelude to a scope
    initialScope = Scope
      { varScope = exportedVariables <> exportedFunctions

      , conScope = Map.fromList $ concat $ preludeExports.datatypes <&> \(T.DD _ _ dcs _) -> dcs <&> \dc@(T.DC _ uc _ _) -> (uc.conName, R.ExternalConstructor dc)
      , tyScope  = Map.fromList $ preludeExports.datatypes <&> \dd@(T.DD ut _ _ _) -> (ut.typeName, R.ExternalDatatype dd)
      }

    exportedVariables = Map.fromList $ preludeExports.variables <&> \uv -> 
      (uv.varName, DefinedVariable uv)
    exportedFunctions = Map.fromList $ preludeExports.functions <&> \fn -> 
      (fn.functionDeclaration.functionId.varName, ExternalFunction fn)

    preludeExports = prel.tpModule.exports

generateVar :: VarName -> Ctx UniqueVar
generateVar name = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = name }
  pure var

newFunction :: R.Function -> Ctx ()
newFunction fun = do
  let uv = fun.functionDeclaration.functionId
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.DefinedFunction fun) sc.varScope }
  RWST.modify $ \s -> s { functions = fun : s.functions }

newVar :: VarName -> Ctx UniqueVar
newVar name = do
  uv <- generateVar name
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.DefinedVariable uv) sc.varScope }
  pure uv

lambdaVar :: Ctx UniqueVar
lambdaVar = do
  vid <- liftIO newUnique
  let var = VI { varID = vid, varName = VN (Text.pack "lambda") }
  return var

resolveVar :: VarName -> Ctx (Locality, R.Variable)
resolveVar name = do
  allScopes <- getScopes
  case lookupScope name (fmap varScope allScopes) of
    Just v -> pure v
    Nothing -> do
      err $ UndefinedVariable name
      (Local,) . R.DefinedVariable <$> placeholderVar name

placeholderVar :: VarName -> Ctx UniqueVar
placeholderVar = generateVar


generateCon :: ConName -> Ctx UniqueCon
generateCon name = do
  cid <- liftIO newUnique
  let con = CI { conID = cid, conName = name }
  pure con

newCon :: R.DataCon -> Ctx ()
newCon dc@(R.DC _ uc _ _) = do
  modifyThisScope $ \sc -> sc { conScope = Map.insert uc.conName (R.DefinedConstructor dc) sc.conScope }

resolveCon :: ConName -> Ctx (Maybe R.Constructor)
resolveCon name = do
  allScopes <- getScopes
  -- This has been generalized to return Maybe instead of throwing an error.
  --   WHY? I needed this function somewhere else AND I the usage should be the same.
  --    This is more in line with the spiritual usage of Haskell - bubble up errors and handle them there. this makes it obvious what is happening with the value - no need to check inside the function. (remember this :3)
  let maybeCon = snd <$> lookupScope name (fmap conScope allScopes)
  pure maybeCon

placeholderCon :: ConName -> Ctx R.Constructor
placeholderCon name = do
  uc <- generateCon name

  ti <- generateType $ TC $ "PlaceholderTypeForCon" <> name.fromCN

  -- fill in later with a placeholder type.
  let dc = R.DC dd uc [] []
      dd = R.DD ti [] [dc] []
  pure $ DefinedConstructor dc


-- Generate a new unique type.
generateType :: TCon -> Ctx UniqueType
generateType name = do
  tid <- liftIO newUnique
  let ty = TI { typeID = tid, typeName = name }
  pure ty

registerDatatype :: R.DataDef -> Ctx ()
registerDatatype dd@(R.DD ut _ _ _) = do
  -- Check for duplication first
  -- if it exists, we still replace it, but an error is signaled.
  let name = ut.typeName
  currentScope <- NonEmpty.head <$> getScopes
  case currentScope.tyScope !? name of
    Nothing -> pure ()
    Just (R.DefinedDatatype _) -> pure ()
    Just (R.ExternalDatatype _) -> err $ TypeRedeclaration name

  modifyThisScope $ \sc -> sc { tyScope = Map.insert name (R.DefinedDatatype dd) sc.tyScope }
  RWST.modify $ \s -> s { datatypes = dd : s.datatypes }
  pure ()

mkTVars :: Binding -> [UnboundTVar] -> [TVar]
mkTVars b = fmap $ bindTVar b

bindTVars :: [TVar] -> Ctx a -> Ctx a
bindTVars tvs cx = do
    oldBindings <- RWS.gets tvarBindings

    -- make bindings and merge them with previous bindings
    let bindings = Map.fromList $ fmap (\tv -> (UTV tv.fromTV, tv)) tvs
    RWS.modify $ \ctx -> ctx { tvarBindings = bindings <> ctx.tvarBindings }

    x <- cx

    RWS.modify $ \ctx -> ctx { tvarBindings = oldBindings }

    pure x

tryResolveTVar :: UnboundTVar -> Ctx (Maybe TVar)
tryResolveTVar utv = do
  tvs <- RWS.gets tvarBindings
  pure $ tvs !? utv

resolveTVar :: UnboundTVar -> Ctx TVar
resolveTVar utv = do
  mtv <- tryResolveTVar utv
  case mtv of
    Just tv -> pure tv
    Nothing -> do
      err $ UnboundTypeVariable utv
      placeholderTVar utv

placeholderTVar :: UnboundTVar -> Ctx TVar
placeholderTVar utv = do
  var <- generateVar $ VN $ "placeholderVarForTVar" <> utv.fromUTV
  pure $ bindTVar (BindByVar var) utv

resolveType :: TCon -> Ctx R.Datatype
resolveType name = do
  allScopes <- getScopes
  case lookupScope name (fmap tyScope allScopes) of
    Just (_, c) -> pure c  -- rn we will ignore the scope
    Nothing -> do
      err $ UndefinedType name
      placeholderType name

placeholderType :: TCon -> Ctx R.Datatype
placeholderType name = do
  -- generate a placeholder type.
  ti <- generateType $ TC $ "PlaceholderType" <> name.fromTC

  let dd = R.DD ti [] [] []
  pure $ DefinedDatatype dd

modifyThisScope :: (Scope -> Scope) -> Ctx ()
modifyThisScope f =
  let modifyFirstScope (sc :| scs) = f sc :| scs
  in RWST.modify $ \sctx -> sctx { scopes = modifyFirstScope sctx.scopes }

lookupScope :: (Ord b) => b -> NonEmpty (Map b c) -> Maybe (Locality, c)
lookupScope k = foldr (\(locality, l) r -> (locality,) <$> Map.lookup k l <|> r) Nothing . (\(cur :| envs) -> (Local, cur) :| fmap (FromEnvironment,) envs)


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
  = UndefinedVariable VarName
  | UndefinedConstructor ConName
  | UndefinedType TCon
  | UnboundTypeVariable UnboundTVar
  | TypeRedeclaration TCon
  | CannotMutateFunctionDeclaration VarName
  deriving Show


-- environment stuff
mkEnv :: Set UniqueVar -> Ctx Env
mkEnv innerEnv = do
  locality <- localityOfVariablesAtCurrentScope
  pure $ Env $ mapMaybe (locality !?) $ Set.toList innerEnv

localityOfVariablesAtCurrentScope :: Ctx (Map UniqueVar (R.Variable, Locality))
localityOfVariablesAtCurrentScope = do
  allScopes <- getScopes
  pure $ foldr (\(locality, l) r -> Map.fromList (fmap (\v -> (R.asUniqueVar v, (v, locality))) $ Map.elems l.varScope) <> r) mempty $ (\(cur :| envs) -> (Local, cur) :| fmap (FromEnvironment,) envs) allScopes

-- used for function definitions
gatherVariables :: R.AnnStmt -> Set UniqueVar
gatherVariables = cata $ \(O (Annotated _ bstmt)) -> case first gatherVariablesFromExpr bstmt of
  R.Mutation v _ expr -> Set.insert v expr
  R.EnvDef fn -> 
    let dec = fn.functionDeclaration
        envVars = Set.fromList $ R.asUniqueVar . fst <$> dec.functionEnv.fromEnv
    in envVars
  stmt -> bifold stmt

-- used for lambdas
gatherVariablesFromExpr :: R.Expr -> Set UniqueVar
gatherVariablesFromExpr = cata $ \case
  R.Var _ v -> Set.singleton (R.asUniqueVar v)  -- TODO: Is this... correct? It's used for making the environment, but now we can just use this variable to know. This is todo for rewrite.
                                --   Update: I don't understand the comment above.
  expr -> fold expr


scopeToExports :: Scope -> Exports
scopeToExports sc = Exports
  { variables = vars
  , functions = funs
  , datatypes = dts
  } where
    vars = mapMaybe (\case { DefinedVariable var -> Just var; _ -> Nothing }) $ Map.elems sc.varScope

    funs = mapMaybe (\case { DefinedFunction fun -> Just fun; _ -> Nothing }) $ Map.elems sc.varScope

    dts = mapMaybe (\case { DefinedDatatype dt -> Just dt; _ -> Nothing }) $ Map.elems sc.tyScope
