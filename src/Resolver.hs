{-# LANGUAGE LambdaCase #-}
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
import Control.Monad ((<=<))
import Data.Bitraversable (bisequenceA, bitraverse)
import Data.Maybe (mapMaybe, fromMaybe)
import Debug.Trace (traceShowId)


data ResolveError
  = UndeclaredVariable String
  | RedeclaredVariable String
  | FunctionDeclaredAfterTopLevelVariable String

  | UndeclaredType String Int -- Type name & arity
  | RedeclaredType String

  | RepeatingTVar TVar
  | FTVInDataConstructor TVar
  deriving Show


-- Plan
-- 1. Collect function names (make sure they don't repeat) and assign globals to them.
-- 2. Go through each line and assign a local to a top level variable (and lookup a global for the function).
-- 2.1. Assign locals to the body.

newtype TopLevelVariables = TopLevelVariables (Map String Local)
newtype Functions = Functions (Map String Global)

type TopLevelResolve = RWST Functions [ResolveError] TopLevelVariables IO


data TopLevelEnv = TopLevelEnv Functions TopLevelVariables
newtype Locals = Locals (NonEmpty (Map String Local))

type Resolve = RWST TopLevelEnv [ResolveError] Locals IO



addTopLevelVariable :: String -> TopLevelResolve Local
addTopLevelVariable name = do
    (TopLevelVariables tlVars) <- get
    case tlVars !? name of
      Nothing -> return ()
      Just l -> resolveError $ RedeclaredVariable name

    -- Even if it's redeclared, we still create a new local.
    l <- Local <$> liftIO newUnique
    put $ TopLevelVariables $ M.insert name l tlVars
    return l


runResolve :: Map String Local -> Resolve a -> TopLevelResolve a
runResolve initialLocals res = do
    funs <- ask
    tlVars <- get
    (x, errs) <- liftIO $ evalRWST res (TopLevelEnv funs tlVars) (Locals (initialLocals :| mempty))
    tell errs
    return x

resolveError :: Monad m => ResolveError -> RWST r [ResolveError] s m ()
resolveError = tell . pure

addVariable :: String -> Resolve Local
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


findVar :: String -> Resolve (Either Global Local)
findVar name = do
    (Locals scopes) <- get
    let findInScopes = case mapMaybe (!? name) $ NE.toList scopes of
          l : _ -> Just l
          [] -> Nothing

    (TopLevelEnv (Functions funs) (TopLevelVariables tlVars)) <- ask
    let findTopLevel = case tlVars !? name of
          Nothing -> (Just . Left) =<< (funs !? name)
          Just l -> Just $ Right l

    case findInScopes of
      Nothing -> case findTopLevel of
        Nothing -> liftIO (putStrLn (name ++ ": name")) >> return (Right undefined) -- Dunno, maybe sentinel value?
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

beginScope :: NonEmpty (Resolve RStmt) -> Resolve (NonEmpty RStmt)
beginScope body =
    withRWST (\tl (Locals scopes) -> (tl , Locals (NE.insert mempty scopes))) $ sequenceA body

resolveStmt :: UStmt -> Resolve RStmt
resolveStmt = mapARS $ go <=< bindExpr resolveExpr
    where
        go :: StmtF String String RExpr (Resolve RStmt) -> Resolve (StmtF Local Global RExpr RStmt)
        go = \case
          Print expr -> pure $ Print expr
          Assignment name expr -> liftA2 Assignment (addVariable name) (pure expr)
          If cond ifTrue elseIfs mIfFalse
            ->  If cond
            <$> beginScope ifTrue
            <*> (traverse . traverse) beginScope elseIfs
            <*> traverse beginScope mIfFalse

          ExprStmt expr -> pure $ ExprStmt expr
          Return expr -> pure $ Return expr

resolveType :: Type String -> Resolve (Type TypeID)
resolveType = mapARS $ \case
    -- Temporary, since we cannot declare any datatypes right now.
    TCon name types -> TCon (M.findWithDefault undefined name (M.fromList [("Int", TypeID 0), ("Bool", TypeID 1)])) <$> sequenceA types
    TVar tv -> pure $ TVar tv
    TDecVar tv -> pure $ TDecVar tv
    TFun params ret -> liftA2 TFun (sequenceA params) ret


resolveAll :: TypeID -> [UDataDec] -> [Either UFunDec UStmt] -> IO (Either (NonEmpty ResolveError) (TypeID, RModule))
resolveAll tId _ funStmt =
    let funNames = map (\(FD name _ _ _) -> name) $ lefts funStmt
        duplicateFunNames = map head $ filter ((>1) . length) $ group $ sort funNames
    in case duplicateFunNames of
      s : ss -> pure $ Left $ fmap RedeclaredVariable $ s :| ss
      [] -> do
        funsWithGlobals <- M.fromList <$> traverse (\name -> (,) name . Global <$> newUnique) funNames

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
                g <- (\(Functions funs) -> funs ! name) <$> ask
                return $ FD g params' ret' body'

        (rFunStmts, errs) <- evalRWST (traverse (bitraverse onFunction onTopLevel) funStmt) (Functions (traceShowId funsWithGlobals)) (TopLevelVariables mempty)
        return $ case errs of
          re : res -> Left (re :| res)
          [] ->
            let stmts = rights rFunStmts
                funs = S.fromList $ lefts rFunStmts
            in Right (TypeID 2, RModule { rmFunctions = funs, rmDataDecs = mempty, rmTLStmts = stmts })
