{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}

module Typecheck (typecheck) where

import AST

import Data.Map (Map, (!), (!?))
import qualified Data.Map as M

import Data.Fix (Fix (Fix), hoistFix, unFix)
import Control.Monad ((<=<), zipWithM, replicateM, zipWithM_)
import Data.Functor.Foldable (transverse, Base, embed, project, cata, histo)
import Debug.Trace (trace, traceShowId)
import Data.Bifunctor (first, Bifunctor, bimap)
import Data.Foldable (fold, traverse_, Foldable (foldl'), sequenceA_)
import Control.Monad.Trans.RWS (RWST, ask, tell, get, put, RWS, evalRWS, local, withRWST, withRWS, listen)
import Control.Monad.Trans.Except (Except)
import Data.Tuple (swap)
import Data.Set (Set, (\\))
import qualified Data.Set as S
import Data.Bifunctor.TH (deriveBifunctor)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Bifoldable (bifold, bifoldMap)
import Data.Maybe (isNothing, fromJust)
import TypecheckAdditional (poukładaj)
import Data.Graph (SCC (..))
import ASTPrettyPrinter (ppModule, ppShow)


-- Okay, what types do we need?
--  Concrete datatypes (eg. Int)
--  User-defined datatypes (eg. Bool, whatever) (yeah, Bool will technically be user-defined /╲/\╭( ͡° ͡° ͜ʖ ͡° ͡°)╮/\╱\)
--  In functions: polymorphic types, also: polymorphic types of functions, datatypes, etc.

-- Some examples:
-- a -> b, Poly Int Bool, Poly Int a, Poly (Ptr (Poly Int Bool)) Int, (a, b) -> b, Ptr a => (a, a) -> Bool


data TypeError
  = UnificationMismatch TypedType TypedType
  | InfiniteType TVar TypedType
  | Ambiguous TVar
  | ParameterMismatch [TypedType] [TypedType]
  deriving (Show)


------------------------------------------
-- Constraint Generation
-----------------------------
-- Context / Typing environment (Gamma)
-- FEnv (normal 'let' env) ('letrec' env - don't instantiate) (teturn type)
newtype Env = Env (Map Global TypedType) deriving (Show)
data FEnv = FEnv (Map (Either Global Local) TypedType) (Map Global TypedType) TypedType deriving Show
type Constraint = (TypedType, TypedType)
newtype TVarGen = TVG Int deriving (Show, Eq, Ord)

type Infer a = RWS FEnv [Constraint] TVarGen a  -- For now, not even possible to throw an error.
type TLInfer a = RWS Env [Constraint] TVarGen a


-- We don't really need a type scheme.
-- We collect all of the ftvs, then make fresh variables for them.
instantiate :: TypedType -> Infer TypedType
instantiate t = do
  let ftvs = ftv t
  freshSubst <- Subst . M.fromList <$> traverse (\t -> (,) t <$> fresh) (S.toList ftvs)
  return $ apply freshSubst t

lookupEnv :: Either Global Local -> Infer TypedType
lookupEnv (Left g) = do
  (FEnv env letrecEnv _) <- ask

  case letrecEnv !? g of
    Nothing -> instantiate $ env ! Left g
    Just t -> return t
lookupEnv (Right l) = do
  (FEnv env _ _) <- ask
  return $ env ! Right l

-- Straight outta dev.stephendiehl.com
letters :: [String]
letters = map ('\'': ) $ [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer TypedType
fresh = do
  (TVG nextVar) <- get
  put $ TVG $ nextVar + 1
  return $ Fix $ TVar $ TV $ letters !! nextVar

noopFEnv :: Env -> TVarGen -> (FEnv, TVarGen)
noopFEnv (Env env) tvg = (FEnv (M.mapKeys Left env) mempty undefined, tvg)

fresh' :: TLInfer TypedType
fresh' = withRWST noopFEnv fresh

uni ::TypedType -> TypedType -> Infer ()
uni t t' = tell [(t, t')]

inferExpr :: RExpr -> Infer TExpr
inferExpr = mapARS $ go <=< sequenceA   -- Apply inference and THEN modify the current expression. 
  where
    go exprt =
      let t = go' $ fmap (\(Fix (ExprType t _)) -> t) exprt
      in ExprType <$> t <*> pure exprt

    go' :: ExprF (Either Global Local) TypedType -> Infer TypedType
    go' = \case
      Lit (LInt _) -> return intType
      Lit (LBool _) -> return boolType
      Var gl -> lookupEnv gl

      Op t Equals t' -> do
        uni t t'
        return boolType

      Op t NotEquals t' -> do
        uni t t'
        return boolType

      -- All arithmetic operators.
      Op t op t' -> do
        uni t intType
        uni t' intType
        return intType

      Call f args -> do
        ret <- fresh
        let funType = Fix (TFun args ret) :: TypedType

        uni f funType
        return ret


inferStmt :: RStmt -> Infer TStmt
inferStmt = mapARS $ go <=< bindExpr inferExpr <=< sequenceA
  where
    go stmtt =
      let ts = first (\(Fix (ExprType t _)) -> t) stmtt
      in go' ts >> return stmtt

    go' :: StmtF Local Global TypedType TStmt -> Infer ()
    go' = \case
      If cond _ elifs _ -> do
        uni cond boolType
        traverse_ (uni boolType . fst) elifs
      Assignment name t -> do
        varType <- lookupEnv (Right name)
        uni varType t
      Return t -> do
        (FEnv _ _ ret) <- ask
        uni t ret
      stmt -> return ()


type Globals = Map Global TypedType

localDefs :: (Foldable f) => f (Stmt Local a b) -> Set Local
localDefs = foldMap $ cata $ \case
  Assignment l _ -> S.singleton l
  stmt -> fold stmt

-- For now, used only for the statement list.
-- inferFunction :: Globals -> RFunDec -> ([Constraint], TFunDec)
-- inferFunction globals (FD name params ret body) = undefined $ swap $ evalRWS go (Env (M.mapKeys Left M.empty)) (TVG 0)
--   where
--     numLocals = S.size $ localDefs body
--     go = do
--       locals <- M.fromList . zip (map (Right . Local) [1..numLocals]) <$> replicateM numLocals fresh
--       local (\(Env globals) -> Env $ locals `M.union` globals) (traverse inferStmt body)


-------------------------------------------------------------
-- Constraint Solving
-------------------------------------
newtype Subst = Subst (Map TVar TypedType) deriving Show


class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set TVar

instance Substitutable TypedType where
  apply s@(Subst subst) = cata $ \case
    t@(TVar tv) -> M.findWithDefault (Fix t) tv subst
    t -> Fix t
  ftv = cata $ \case
    t@(TVar tv) -> S.singleton tv
    t -> fold t

instance Substitutable TExpr where
  apply s = mapRS $ \(ExprType t e) -> ExprType (apply s t) e
  ftv = cata $ \(ExprType t ftvs) -> ftv t <> fold ftvs

instance Substitutable TStmt where
  apply s = cata $ Fix . first (apply s)
  ftv = cata $ bifold . first ftv

instance Substitutable TFunDec where
  apply s = bimap (apply s) (apply s)
  ftv (FD _ params ret body) =
    let
      declared = ftv $ (ret:) $ map snd params
      inferred = ftv body
    in inferred \\ declared

instance Substitutable a => Substitutable [a] where
  apply s = fmap (apply s)
  ftv = foldMap ftv

instance Substitutable a => Substitutable (NonEmpty a) where
  apply s = fmap (apply s)
  ftv = foldMap ftv

instance (Ord a, Substitutable a) => Substitutable (Set a) where
  apply s = S.map (apply s)
  ftv = foldMap ftv


instance Semigroup Subst where
  Subst s1 <> Subst s2 = Subst $ fmap (apply (Subst s1)) s2 `M.union` s1 -- Uncomment if I stop using foldl and the right Subst can contain substitutions not in the left one. fmap (apply (Subst s2)) s1

instance Monoid Subst where
  mempty = Subst M.empty


instance Substitutable Constraint where
  apply s = bimap (apply s) (apply s)
  ftv = bifoldMap ftv ftv

data Validation e a
  = Success a
  | Failure e
  deriving (Show, Functor)

$(deriveBifunctor ''Validation)

instance Applicative (Validation e) where
  pure = Success
  Success f <*> Success x = Success (f x)
  Failure e <*> _ = Failure e
  _ <*> Failure e = Failure e

instance Monad (Validation e) where
  Success x >>= f = f x
  Failure x >>= _ = Failure x



occursCheck :: TVar -> TypedType -> Bool
occursCheck tv t = S.member tv (ftv t)

bind :: TVar -> TypedType -> Validation (NonEmpty TypeError) Subst
bind tv t | t == Fix (TVar tv)  = mempty
          | occursCheck tv t    = Failure $ NE.singleton $ InfiniteType tv t
          | otherwise           = pure $ Subst $ M.singleton tv t

unifyMany :: [TypedType] -> [TypedType] -> Validation (NonEmpty TypeError) Subst
unifyMany [] [] = mempty
unifyMany t t' | length t /= length t' = Failure $ NE.singleton $ ParameterMismatch t t'
unifyMany t t' = mconcat $ zipWith unify t t'

unify :: TypedType -> TypedType -> Validation (NonEmpty TypeError) Subst
unify t t' | t == t' = mempty
unify (Fix (TVar v)) t = bind v t
unify (Fix (TDecVar v)) t = bind v t
unify t (Fix (TVar v)) = bind v t
unify t (Fix (TDecVar v)) = bind v t
unify (Fix (TFun ps r)) (Fix (TFun ps' r')) = unifyMany ps ps' <> unify r r'
unify t t' = Failure $ NE.singleton $ UnificationMismatch t t'

toEither :: Validation e a -> Either e a
toEither (Success s) = Right s
toEither (Failure e) = Left e


instance (Semigroup e, Semigroup a) => Semigroup (Validation e a) where
  Failure e <> Failure e' = Failure (e <> e')
  Success s <> Success s' = Success (s <> s')
  Failure e <> _ = Failure e
  _ <> Failure e = Failure e

instance (Semigroup e, Monoid a) => Monoid (Validation e a) where
  mempty = Success mempty



-- Typechecking strategies.
solve :: [Constraint] -> Either (NonEmpty TypeError) Subst
solve = toEither . go mempty
  where
    go subst cts =
      case cts of
        [] -> pure subst
        ((t, t') : cs) -> do
          subst' <- unify t t'
          go (subst' <> subst) (apply subst' cs)


inferLet :: Map Global TypedType -> RFunDec -> TLInfer (TypedType, TFunDec)
inferLet letrecDefs (FD name params ret body) = do
  let vars = localDefs body <> S.fromList (map fst params)
  freshParams <- (traverse . traverse) (maybe fresh' pure) params
  freshVars <- M.fromList <$> traverse (\local -> (,) local <$> fresh') (S.toList vars)
  let typedVars = M.fromList $ (fmap . first) Right $ M.toList $ M.fromList freshParams <> freshVars
  freshReturn <- maybe fresh' pure ret

  withRWST (\(Env env) tvg -> (FEnv (M.mapKeys Left env <> typedVars) letrecDefs freshReturn, tvg)) $ do
    body' <- traverse inferStmt body

    let inferredType = Fix $ TFun (map snd freshParams) freshReturn
    return (inferredType, FD name freshParams freshReturn body')

inferLetrec :: [RFunDec] -> TLInfer (Map Global TypedType, Set TFunDec)
inferLetrec mrfds = do
  ((ts, funs), cts) <- listen $ do

    -- Assign fresh names to each letrec thingy.
    lrTypes <- traverse (\(FD g _ _ _) -> (,) g <$> fresh') mrfds

    -- We're gonna do this a bit differently - we're not gonna wait 'til we check if the "normal" constraints are correct.
    tfs <- traverse (inferLet (M.fromList lrTypes)) mrfds

    -- Then, gather the inferred global -> fun type. And unify them with the fresh bois, since they are not instantiated.
    withRWST noopFEnv $ zipWithM_ (\(_, t) (t', _) -> uni t t') lrTypes tfs
    return (M.fromList (map (\(t, FD g _ _ _) -> (g, t)) tfs), S.fromList $ map snd tfs)
  
  let esubst = solve cts
  return $ case esubst of
    Left _ -> (ts, funs)
    Right subst -> (apply subst <$> ts, apply subst funs)

climb' :: [SCC RFunDec] -> TLInfer (Set TFunDec)
climb' = go
  where
    go :: [SCC RFunDec] -> TLInfer (Set TFunDec)
    go [] = do
      (Env !env) <- traceShowId <$> ask
      return mempty
    go (AcyclicSCC fd@(FD g _ _ _) : rest) = do
      ((t, tfd), cts) <- listen $ inferLet mempty fd
      let (t', tfd') = case solve cts of
              Left ne -> (t, tfd)
              Right subst -> (apply subst t, apply subst tfd)
      S.insert tfd' <$> local (\(Env env) -> Env $ M.insert g t' env) (go rest)
    go (CyclicSCC fds : rest) = do
      (ts, letrecs) <- inferLetrec fds
      S.union letrecs <$> local (\(Env env) -> Env $ M.union ts env) (go rest)

climb :: Set RFunDec -> [RStmt] -> ([Constraint], Set TFunDec, [TStmt])
climb fds stmts = (\((fds, stmts), cts) -> (cts, fds, stmts)) $ (\m -> evalRWS m (Env mempty) (TVG 0)) $ do
  --
  withRWS (\_ tvg -> (Env mempty, tvg)) $ do
    tfds <- climb' $ (\x -> show ((map . fmap) (\(FD g _ _ _) -> g) x) `trace` x) $ poukładaj fds
    tstmts <- withRWST noopFEnv $ traverse inferStmt stmts  -- Should be U8 as return type. 
    return (tfds, tstmts)

typecheck :: RModule -> Either (NonEmpty TypeError) TModule
typecheck (RModule { rmFunctions, rmDataDecs, rmTLStmts }) =
  let
    (cts, tfuns, stmts) = climb rmFunctions rmTLStmts
    valSubst = fmap (\(Subst x) -> concatMap (("\t" ++) . (++ "\n") . show . bimap show ppShow) (M.toList x) `trace` Subst x) $ solve $ (\x -> ("Constraints: " ++ show (length x) ++ "\n" ++ concatMap (("\t" ++) . (++ "\n") . show . bimap ppShow ppShow) x) `trace` x) cts
  in case valSubst of
    Left tes -> Left tes
    Right su ->
      let
        finalFuns = apply su tfuns
        finalStmts = apply su stmts
      in case S.toList (ftv finalStmts <> ftv finalFuns) of
        []    -> Right $ TModule finalFuns mempty finalStmts
        (tv : tvs) -> Left $ (\x -> ppShow (TModule finalFuns mempty finalStmts) `trace` x) $ (\x -> ppShow (TModule tfuns mempty stmts) `trace` x) $ Ambiguous <$> (tv :| tvs)
  -- let withUniqueTypes = assignUniqueTypes rstmts  -- Assign each expression (only expressions right now) a unique type.
  -- env <- infer withUniqueTypes                    -- Then, try to infer them.

  -- return $ assignTypes env withUniqueTypes        -- If it works, create actual types from them.
