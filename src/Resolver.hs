{-# LANGUAGE LambdaCase, OverloadedStrings, BangPatterns #-}
module Resolver where

import AST
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Either (lefts, rights)
import Data.List (sort, group)
import Lens.Micro
import Lens.Micro.TH
import Data.Map (Map, (!?), (!))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Unique (newUnique)
import Control.Monad.Trans.RWS (RWS, evalRWST, RWST, get, modify, put, tell, ask, runRWST, withRWST)
import Data.Biapplicative (bimap)
import Data.Fix (Fix(..))
import Control.Monad.Trans.Class (lift)
import Control.Monad.IO.Class (liftIO)
import Control.Applicative (liftA2, liftA3)
import Data.Traversable (for)
import Control.Monad ((<=<), when, unless)
import Data.Bitraversable (bisequenceA, bitraverse)
import Data.Maybe (mapMaybe, fromMaybe)
import Debug.Trace (traceShowId)
import Data.Foldable (traverse_)
import Data.Set (Set)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO


data ResolveError
  = UndeclaredVariable Text
  | RedeclaredVariable Text
  | FunctionDeclaredAfterTopLevelVariable Text

  | UndeclaredType Text Int -- Type name & arity
  | RedeclaredType Text

  | RepeatingTVar TVar
  | FTVInDataConstructor TVar
  deriving Show


-- Plan
-- 1. Collect function names (make sure they don't repeat) and assign globals to them.
-- 2. Go through each line and assign a local to a top level variable (and lookup a global for the function).
-- 2.1. Assign locals to the body.

newtype TopLevelVariables = TopLevelVariables (Map Text Local) 
newtype Functions = Functions (Map Text Global)
newtype Datatypes = Datatypes (Map Text TypeID)

type TopLevelResolve = RWST (Functions, Datatypes) [ResolveError] TopLevelVariables IO


data TopLevelEnv = TopLevelEnv Functions TopLevelVariables Datatypes
newtype Locals = Locals (NonEmpty (Map Text Local)) deriving Show

type Resolve = RWST TopLevelEnv [ResolveError] Locals IO



addTopLevelVariable :: Text -> TopLevelResolve Local
addTopLevelVariable name = do
    (TopLevelVariables tlVars) <- get
    case tlVars !? name of
      Nothing -> return ()
      Just l -> resolveError $ RedeclaredVariable name

    -- Even if it's redeclared, we still create a new local.
    l <- Local <$> liftIO newUnique
    put $ TopLevelVariables $ M.insert name l tlVars
    return l


runResolve :: Map Text Local -> Resolve a -> TopLevelResolve a
runResolve initialLocals res = do
    (funs, dts) <- ask
    tlVars <- get
    (x, errs) <- liftIO $ evalRWST res (TopLevelEnv funs tlVars dts) (Locals (initialLocals :| mempty))
    tell errs
    return x

resolveError :: Monad m => ResolveError -> RWST r [ResolveError] s m ()
resolveError = tell . pure

addVariable :: Text -> Resolve Local
addVariable name = do
    (Locals (vars :| rest)) <- get
    case vars !? name of
      Just l -> resolveError $ RedeclaredVariable name
      Nothing -> pure ()

    l <- Local <$> liftIO newUnique
    put $ Locals $ M.insert name l vars :| rest
    return l

runEmptyResolve :: Resolve a -> TopLevelResolve a
runEmptyResolve = runResolve mempty


findVar :: Text -> Resolve (Either Global Local)
findVar name = do
    (Locals scopes) <- get
    let findInScopes = case mapMaybe (!? name) $ NE.toList scopes of
          l : _ -> Just l
          [] -> Nothing

    (TopLevelEnv (Functions funs) (TopLevelVariables tlVars) _) <- ask
    -- todo: search for constructor.
    let findTopLevel = case tlVars !? name of
          Nothing -> (Just . Left) =<< (funs !? name)
          Just l -> Just $ Right l

    case findInScopes of
      Nothing -> case findTopLevel of
        Nothing -> liftIO (TIO.putStrLn (name <> ": name")) >> return (Right undefined) -- Dunno, maybe sentinel value?
        Just egl -> return egl
      Just l -> return $ Right l

resolveExpr :: UExpr -> Resolve RExpr
resolveExpr = mapARS $ \case
    Lit x -> pure (Lit x)
    Var vars ->
        let var = either id id vars  -- I think this either is only a type for later phases (to differentiate Global and Local). It does not matter during parsing.
        in Var <$> findVar var
    Op l op r -> liftA3 Op l (pure op) r
    Call f params -> liftA2 Call f (sequenceA params)
    Lam params expr -> withScope $ do
      -- First, add new variables (in a new scope)
      params' <- traverse (addVariable . either id id) params
      Lam (map Right params') <$> expr  -- TODO: This is definitely bad. Make global/local parameters of expression later.

withScope :: Resolve a -> Resolve a
withScope m = do
  -- looks kinda shit, but we don't want to modify that state, yo.
  locals@(Locals scopes) <- get
  put $ Locals (NE.insert mempty scopes)
  x <- m
  put locals

  return x

    

withBody :: NonEmpty (Resolve RStmt) -> Resolve (NonEmpty RStmt)
withBody = withScope . sequenceA

resolveStmt :: UStmt -> Resolve RStmt
resolveStmt = mapARS $ go <=< bindExpr resolveExpr
    where
        go :: StmtF Text Text RExpr (Resolve RStmt) -> Resolve (StmtF Local Global RExpr RStmt)
        go = \case
          Print expr -> pure $ Print expr
          Assignment name expr -> 
            liftA2 Assignment (addVariable name) (pure expr)
          If cond ifTrue elseIfs ifFalse
            ->  If cond
            <$> withBody ifTrue
            <*> (traverse . traverse) withBody elseIfs
            <*> traverse withBody ifFalse

          ExprStmt expr -> pure $ ExprStmt expr
          Return expr -> pure $ Return expr

resolveType :: Type Text -> Resolve (Type TypeID)
resolveType = mapARS $ \case
    TCon name types -> do
      (TopLevelEnv _ _ (Datatypes dts)) <- ask
      tcon <- case dts !? name of
        Nothing -> do
          resolveError $ UndeclaredType name (length types)
          return undefined
        Just t -> return t
      TCon tcon <$> sequenceA types
    TVar tv -> pure $ TVar tv
    TDecVar tv -> pure $ TDecVar tv
    TFun params ret -> liftA2 TFun (sequenceA params) ret

resolveDataConstructor :: Set TVar -> UDataCon -> TopLevelResolve RDataCon
resolveDataConstructor tvs (DC name types) = do
  (Functions funs, _) <- ask
  DC (funs ! name) <$> traverse (runEmptyResolve . resolveType) types

resolveDataDeclaration :: UDataDec -> TopLevelResolve RDataDec
resolveDataDeclaration (DD name tvs cons) = do
  (_, Datatypes dts) <- ask
  let g = dts ! name
  let repeatingTVs = map head $ filter ((>1) . length) $ group $ sort tvs
  unless (null repeatingTVs) $
    traverse_ (resolveError . RepeatingTVar) repeatingTVs
  let tvSet = S.fromList tvs
  rCons <- traverse (resolveDataConstructor tvSet) cons
  return $ DD g tvs rCons

typeIDsFromBuiltins :: Builtins -> (Map Text TypeID, Map Text Global)
typeIDsFromBuiltins (Builtins builtinTypes _ builtinConstructors _) = (M.map (\(Fix (TCon g _)) -> g) builtinTypes, M.map fst builtinConstructors)

-- Need to check for circular references here.
resolveAll :: Builtins -> [UDataDec] -> [Either UFunDec UStmt] -> IO (Either (NonEmpty ResolveError) RModule)
resolveAll ttBuiltins dataDeclarations funStmt =
    let (builtinTypes, builtinConstructors) = typeIDsFromBuiltins ttBuiltins

        funNames = map (\(FD name _ _ _) -> name) $ lefts funStmt
        dtNames = map (\(DD name _ _) -> name) dataDeclarations
        duplicateFunNames = map (RedeclaredVariable . head) $ filter ((>1) . length) $ group $ sort funNames
        duplicateDataNames = map (RedeclaredType . head) $ filter ((> 1) . length) $ group $ sort dtNames
    in case duplicateFunNames <> duplicateDataNames of
      s : ss -> pure $ Left $ s :| ss
      [] -> do
        dtsWithGlobals <- Datatypes . (<> builtinTypes) . M.fromList <$> traverse (\name -> (,) name . TypeID <$> newUnique) dtNames
        funsWithGlobals <- M.fromList <$> traverse (\name -> (,) name . Global <$> newUnique) funNames
        dataConstructors <- M.fromList <$> traverse (\name -> (,) name . Global <$> newUnique) (concatMap (\(DD _ _ dcs) -> map (\(DC g _) -> g) (NE.toList dcs)) dataDeclarations)
        let allFunctions = Functions $ funsWithGlobals <> dataConstructors <> builtinConstructors  -- Treat data constructor as a function. Maps should be disjoint.

        let prepareDatatypes :: [UDataDec] -> TopLevelResolve [RDataDec]
            prepareDatatypes dds = do
              traverse_ addTopLevelVariable $ concatMap (\(DD _ _ cons) -> map (\(DC name _) -> name) (NE.toList cons)) dds
              for dds resolveDataDeclaration

        -- Resolve top level, yo.
        let onTopLevel :: UStmt -> TopLevelResolve RStmt
            onTopLevel (Fix stmt) = Fix <$> case stmt of
              Assignment name expr -> do
                expr' <- runEmptyResolve (resolveExpr expr) -- Check expression before assigning the variable - no circular dependencies.
                liftA2 Assignment (addTopLevelVariable name) (pure expr')

              Print expr -> Print <$> runEmptyResolve (resolveExpr expr)
              If cond ifTrue elifs mIfFalse
                ->  If
                <$> runEmptyResolve (resolveExpr cond)
                <*> runEmptyResolve (traverse resolveStmt ifTrue)
                <*> traverse (\(cond, stmts) -> runEmptyResolve (liftA2 (,) (resolveExpr cond) (traverse resolveStmt stmts))) elifs
                <*> runEmptyResolve ((traverse . traverse) resolveStmt mIfFalse)
              ExprStmt expr -> ExprStmt <$> runEmptyResolve (resolveExpr expr)
              Return expr -> Return <$> runEmptyResolve (resolveExpr expr)

            onFunction :: UFunDec -> TopLevelResolve RFunDec
            onFunction (FD name params ret body) = do
                (TopLevelVariables tlVars) <- get
                case tlVars !? name of
                  Just l -> resolveError $ FunctionDeclaredAfterTopLevelVariable name
                  Nothing -> pure ()

                -- Parameters
                (params', body', ret') <- runEmptyResolve $ do
                    params <- for params $ \(name, mt) -> do
                        l <- addVariable name
                        t <- traverse resolveType mt
                        return (l, t)
                    body <- traverse resolveStmt body
                    ret <- traverse resolveType ret
                    return (params, body, ret)

                -- Function name.
                g <- (\(Functions funs, _) -> funs ! name) <$> ask
                return $ FD g params' ret' body'

        (rDataDecs, dtsErrs) <- evalRWST (prepareDatatypes dataDeclarations) (allFunctions, dtsWithGlobals) (TopLevelVariables mempty)
        (rFunStmts, errs) <- evalRWST (traverse (bitraverse onFunction onTopLevel) funStmt) (allFunctions, dtsWithGlobals) (TopLevelVariables mempty)
        return $ case errs <> dtsErrs of
          re : res -> Left (re :| res)
          [] ->
            let stmts = rights rFunStmts
                funs = S.fromList $ lefts rFunStmts
            in Right (RModule { rmFunctions = funs, rmDataDecs = S.fromList rDataDecs, rmTLStmts = stmts })
