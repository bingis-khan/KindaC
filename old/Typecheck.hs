{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Typecheck (typecheck, Substitutable(..), Subst(..)) where

import AST

import Data.Map (Map, (!), (!?))
import qualified Data.Map as M

import Data.Fix (Fix (Fix), hoistFix, unFix)
import Control.Monad ((<=<), zipWithM, replicateM, zipWithM_, when)
import Data.Functor.Foldable (transverse, Base, embed, project, cata, histo)
import Debug.Trace (trace, traceShowId)
import Data.Bifunctor (first, Bifunctor, bimap)
import Data.Foldable (fold, traverse_, Foldable (foldl'), sequenceA_, for_)
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
import Data.Traversable (for)
import Data.Text (Text)
import qualified Data.Text as T


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
  | NoPartialDeclarationInLetrec Global TypedType
  deriving (Show)


------------------------------------------
-- Constraint Generation
-----------------------------
-- Context / Typing environment (Gamma)
-- FEnv (normal 'let' env) ('letrec' env - don't instantiate) (teturn type)

-- Builtins are used for getting a type for stuff like 'if'.
data Env = Env Builtins (Map (Either Global Local) TypedType) deriving (Show)
data FEnv = FEnv Builtins (Map (Either Global Local) TypedType) (Map Global TypedType) TypedType deriving Show
type Constraint = (TypedType, TypedType)
newtype TVarGen = TVG Int deriving (Show, Eq, Ord)

type Infer a = RWS FEnv [Constraint] TVarGen a  -- For now, not even possible to throw an error.
type TLInfer a = RWS Env [Constraint] TVarGen a


-- We don't really need a type scheme.
-- We collect all of the ftvs, then make fresh variables for them.
instantiate' :: (TypedType -> Set TVar) -> TypedType -> Infer TypedType
instantiate' f t = do
  let ftvs = (\x -> concat ["wtf ftvs: ", show x, " for type: ", show t] `trace` x) (f t)
  freshSubst <- Subst . M.fromList <$> traverse (\t -> (,) t <$> fresh) (S.toList ftvs)
  return $ apply freshSubst t

instantiate :: TypedType -> Infer TypedType
instantiate = instantiate' ftv

-- This here assumes that fresh variables start with '. Maybe later enforce it with a type.
instantiateDeclared :: TypedType -> Infer TypedType
instantiateDeclared = instantiate' $ S.filter (\(TV tv) -> T.head tv /= '\'') . ftv



lookupEnv :: Either Global Local -> Infer TypedType
lookupEnv (Left g) = do
  (FEnv _ env letrecEnv _) <- ask

  case letrecEnv !? g of
    Nothing -> instantiate $ env ! Left g
    Just t -> instantiateDeclared t
lookupEnv (Right l) = do
  fenv@(FEnv _ env env' _) <- ask
  return $ env ! (\x -> (show l <> " " <> show env) `trace` x) (Right l)  -- fucks up here

-- Straight outta dev.stephendiehl.com
letters :: [Text]
letters = map (T.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer TypedType
fresh = do
  (TVG nextVar) <- get
  put $ TVG $ nextVar + 1
  return $ Fix $ TVar $ TV $ letters !! nextVar

noopFEnv :: Env -> TVarGen -> (FEnv, TVarGen)
noopFEnv (Env builtins env) tvg = (FEnv builtins env mempty undefined, tvg)

fresh' :: TLInfer TypedType
fresh' = withRWST noopFEnv fresh

uni :: TypedType -> TypedType -> Infer ()
uni t t' = tell [(t, t')]

builtin :: Text -> Infer TypedType
builtin name = do
  (FEnv (Builtins builtins _ _ _) _ _ _) <- ask
  return $ builtins ! name

intType, boolType :: Infer TypedType
intType = builtin "Int"
boolType = builtin "Bool"


inferExpr :: RExpr -> Infer TExpr
inferExpr = mapARS $ go <=< sequenceA   -- Apply inference and THEN modify the current expression. 
  where
    go exprt =
      let t = go' $ fmap (\(Fix (ExprType t _)) -> t) exprt
      in ExprType <$> t <*> pure exprt

    go' :: ExprF Global Local TypedType -> Infer TypedType
    go' = \case
      Lit (LInt _) -> intType
      Lit (LBool _) -> boolType
      Var gl -> lookupEnv gl

      Op t Equals t' -> do
        uni t t'
        boolType

      Op t NotEquals t' -> do
        uni t t'
        boolType

      -- All arithmetic operators.
      Op t op t' -> do
        it <- intType
        uni t it
        uni t' it
        intType

      Call f args -> do
        ret <- fresh
        let funType = traceShowId $ Fix (TFun args ret) :: TypedType

        uni f funType
        return ret
      
      Lam params ret -> do
        paramTypes <- traverse (lookupEnv . Right) params 
        return $ Fix $ TFun paramTypes ret


inferStmt :: RStmt -> Infer TStmt
inferStmt = mapARS $ go <=< bindExpr inferExpr <=< sequenceA
  where
    go stmtt =
      let ts = first (\(Fix (ExprType t _)) -> t) stmtt
      in go' ts >> return stmtt

    go' :: StmtF Local Global TypedType TStmt -> Infer ()
    go' = \case
      If cond _ elifs _ -> do
        bt <- boolType
        uni cond bt
        traverse_ (uni bt . fst) elifs
      Assignment name t -> do
        varType <- lookupEnv (Right name)
        uni varType t
      Return t -> do
        (FEnv _ _ _ ret) <- ask
        uni t ret
      stmt -> return ()


type Globals = Map Global TypedType

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
    t@(TDecVar tv) -> M.findWithDefault (Fix t) tv subst
    t -> Fix t
  ftv = cata $ \case
    t@(TVar tv) -> S.singleton tv
    t@(TDecVar tv) -> S.singleton tv
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

instance Substitutable TDataCon where
  apply s (DC g ts) = DC g (apply s ts)
  ftv (DC g ts) = ftv ts

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
unifyMany (t : rest) (t' : rest') = do
  su1 <- unify t t'
  su2 <- unifyMany (apply su1 rest) (apply su1 rest')
  return $ su2 <> su1
unifyMany _ _ = error "Should not happen. (should be covered by the length check)"

unify :: TypedType -> TypedType -> Validation (NonEmpty TypeError) Subst
unify t t' | t == t' = mempty
unify (Fix (TVar v)) t = bind v t
--unify (Fix (TDecVar v)) t = bind v t
unify t (Fix (TVar v)) = bind v t
--unify t (Fix (TDecVar v)) = bind v t
unify (Fix (TFun ps r)) (Fix (TFun ps' r')) = unifyMany (ps ++ [r]) (ps' ++ [r'])
unify (Fix (TCon t params)) (Fix (TCon t' params')) | t == t' = unifyMany params params'
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


instantiateFunction (FD _ params ret _) = do
  freshParams <- (traverse . traverse) (maybe fresh' pure) params
  freshReturn <- maybe fresh' pure ret
  return (map snd freshParams, freshReturn)

inferLet' :: ([TypedType], TypedType) -> Map Global TypedType -> RFunDec -> TLInfer (TypedType, TFunDec)
inferLet' (freshParamTypes, freshReturn) letrecDefs fd@(FD name params ret body) = do
  let vars = localDefs body <> S.fromList (map fst params)
  freshVars <- M.fromList <$> traverse (\local -> (,) local <$> fresh') (S.toList vars)
  let freshParams = zip (map fst params) freshParamTypes
  let typedVars = M.fromList $ (fmap . first) Right $ M.toList $ M.fromList freshParams <> freshVars
  freshReturn <- maybe fresh' pure ret

  withRWST (\(Env builtins env) tvg -> (FEnv builtins (env <> typedVars) letrecDefs freshReturn, tvg)) $ do
    body' <- traverse inferStmt body

    let inferredType = Fix $ TFun freshParamTypes freshReturn
    (FEnv _ env _ _) <- ask
    let t = env ! Left name
    uni t inferredType

    return (inferredType, FD name freshParams freshReturn body')

inferLet :: Map Global TypedType -> RFunDec -> TLInfer (TypedType, TFunDec)
inferLet letrecDefs fd = do
  paramsRet <- instantiateFunction fd
  inferLet' paramsRet letrecDefs fd

hasPartialDeclaration :: RFunDec -> Bool
hasPartialDeclaration (FD _ params ret _) =
  let types = ret : map snd params
  in any isNothing types && not (all isNothing types)

inferLetrec :: [RFunDec] -> TLInfer (Map Global TypedType, Set TFunDec)
inferLetrec mrfds = do
  ((ts, funs), cts) <- listen $ do
    (Env _ funs) <- ask

    -- Globals are instatiated at the beginning for every global...
    let ogGlobals = map (\(FD g _ _ _) -> (g, funs ! Left g)) mrfds

    -- Shit, partial declarations don't work in letrecs (at least the way we do it).
    -- Either declare function type fully, or let me infer it. No middle ground.
    lrTypes <- for mrfds $ \fd@(FD g _ _ _) -> if not (hasPartialDeclaration fd) then (,) g <$> instantiateFunction fd else error "Can't have fuckin' partial declarations for letrec. Also, I'll have to think of a way to signal this error better, but I don't feel like it right now."

    let lrTypesAsFuns = M.fromList $ (map . fmap) (Fix . uncurry TFun) lrTypes
    withRWST noopFEnv $ zipWithM_ (\(_, t) (param, ret) -> uni t (Fix (TFun param ret))) ogGlobals (map snd lrTypes)
    -- We're gonna do this a bit differently - we're not gonna wait 'til we check if the "normal" constraints are correct.
    tfs <- traverse (\(ft, fd) -> inferLet' ft lrTypesAsFuns fd) $ zip (map snd lrTypes) mrfds

    -- Then, gather the inferred global -> fun type. And unify them with the fresh bois, since they are not instantiated.
    return (M.fromList (map (\(t, FD g _ _ _) -> (g, t)) tfs), S.fromList $ map snd tfs)

  let esubst = solve cts
  return $ case esubst of
    Left _ -> (ts, funs)
    Right subst -> (apply subst <$> ts, apply subst funs)

climb' :: [RStmt] -> [SCC RFunDec] -> TLInfer ([TStmt], Set TFunDec)
climb' tlStmts = go
  where
    go :: [SCC RFunDec] -> TLInfer ([TStmt], Set TFunDec)
    go [] = do
      (Env _ !env) <- traceShowId <$> ask
      tstmts <- withRWST noopFEnv $ traverse inferStmt tlStmts
      return (tstmts, mempty)
    go (AcyclicSCC fd@(FD g _ _ _) : rest) = do
      ((t, tfd), cts) <- (\x@((_, fun), _) -> ppShow undefined fun `trace` x) <$> listen (inferLet mempty fd)
      let (t', tfd') = case solve cts of
              Left ne -> (t, tfd)
              Right subst -> (apply subst t, apply subst tfd)
      fmap (S.insert tfd') <$> local (\(Env builtins env) -> Env builtins $ M.insert (Left g) t' env) (go rest)
    go (CyclicSCC fds : rest) = do
      (ts, letrecs) <- inferLetrec fds
      fmap (S.union letrecs) <$> local (\(Env builtins env) -> Env builtins $ M.union (M.mapKeys Left ts) env) (go rest)

climb :: Builtins -> Map Global TypedType -> Set RFunDec -> [RStmt] -> ([Constraint], Set TFunDec, [TStmt])
climb builtins dcs fds stmts = (\((fds, stmts), cts) -> (cts, fds, stmts)) $ (\m -> evalRWS m (Env builtins mempty) (TVG 0)) $ do
  -- Don't forget to declare top level globals first.
  tlVars <- M.fromList <$> traverse (\local -> (,) local <$> fresh') (S.toList (localDefs stmts))
  funs <- M.fromList <$> traverse (\(FD g _ _ _) -> (,) g <$> fresh') (S.toList fds)
  withRWS (\_ tvg -> (Env builtins (M.mapKeys Right tlVars <> M.mapKeys Left (funs <> dcs)), tvg)) $ do
    (tstmts, tfds) <- climb' stmts $ (\x -> show ((map . fmap) (\(FD g _ _ _) -> g) x) `trace` x) $ poukładaj fds
    return (tfds, tstmts)

dataConstructors :: Set RDataDec -> Map Global TypedType
dataConstructors = M.fromList . concatMap (\dd@(DD _ _ dcs) -> map (\case DC g [] -> (g, dataDeclarationToType dd); DC g args -> (g, Fix $ TFun args $ dataDeclarationToType dd)) (NE.toList dcs)) . S.toList

typecheck :: Builtins -> RModule -> Either (NonEmpty TypeError) TModule
typecheck builtins@(Builtins _ _ ogDCs _) (RModule { rmFunctions, rmDataDecs, rmTLStmts }) =
  let
    dcs = dataConstructors rmDataDecs <> M.fromList (M.elems ogDCs)
    (cts, tfuns, stmts) = climb builtins dcs rmFunctions rmTLStmts
    valSubst = fmap (\(Subst x) -> concatMap (("\t" ++) . (++ "\n") . show . bimap show (ppShow undefined)) (M.toList x) `trace` Subst x) $ solve $ (\x -> ("Constraints: " ++ show (length x) ++ "\n" ++ concatMap (("\t" ++) . (++ "\n") . show . bimap (ppShow undefined) (ppShow undefined)) x) `trace` x) cts
  in case valSubst of
    Left tes -> Left tes
    Right su ->
      let
        finalFuns = apply su tfuns
        finalStmts = apply su stmts
        finalDataDecs = rmDataDecs -- same structure
      in case S.toList (ftv finalStmts <> ftv finalFuns) of
        []    -> Right $ TModule finalFuns finalDataDecs finalStmts
        (tv : tvs) -> Left $ (\x -> ppShow undefined (TModule finalFuns finalDataDecs finalStmts) `trace` x) $ (\x -> ppShow undefined (TModule tfuns finalDataDecs stmts) `trace` x) $ Ambiguous <$> (tv :| tvs)
  -- let withUniqueTypes = assignUniqueTypes rstmts  -- Assign each expression (only expressions right now) a unique type.
  -- env <- infer withUniqueTypes                    -- Then, try to infer them.

  -- return $ assignTypes env withUniqueTypes        -- If it works, create actual types from them.
