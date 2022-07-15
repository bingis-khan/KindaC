{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
module Typecheck (typecheck) where

import AST

import Data.Map (Map, (!))
import qualified Data.Map as M

import Data.Fix (Fix (Fix), hoistFix, unFix)
import Control.Monad ((<=<), zipWithM, replicateM)
import Data.Functor.Foldable (transverse, Base, embed, project, cata, histo)
import Debug.Trace (trace)
import Data.Bifunctor (first, Bifunctor)
import Data.Foldable (fold, traverse_, Foldable (foldl'))
import Control.Monad.Trans.RWS (RWST, ask, tell, get, put, RWS, evalRWS, local)
import Control.Monad.Trans.Except (Except)
import Data.Tuple (swap)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bifunctor.TH (deriveBifunctor)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import Data.Bifoldable (bifold)


-- Okay, what types do we need?
--  Concrete datatypes (eg. Int)
--  User-defined datatypes (eg. Bool, whatever) (yeah, Bool will technically be user-defined /╲/\╭( ͡° ͡° ͜ʖ ͡° ͡°)╮/\╱\)
--  In functions: polymorphic types, also: polymorphic types of functions, datatypes, etc.

-- Some examples:
-- a -> b, Poly Int Bool, Poly Int a, Poly (Ptr (Poly Int Bool)) Int, (a, b) -> b, Ptr a => (a, a) -> Bool


data TypeError
  = UnificationMismatch TypedType TypedType
  | InfiniteType TVar TypedType
  | Ambigious TVar
  | ParameterMismatch [TypedType] [TypedType]
  deriving (Show)


------------------------------------------
-- Constraint Generation
-----------------------------
-- Context / Typing environment (Gamma)
newtype Env = Env (Map (Either Global Local) TypedType) deriving (Show)
type Constraint = (TypedType, TypedType)
newtype TVarGen = TVG Int deriving (Show, Eq, Ord)

type Infer a = RWS Env [Constraint] TVarGen a  -- For now, not even possible to throw an error.

lookupEnv :: Either Global Local -> Infer TypedType
lookupEnv gl = do
  (Env env) <- ask
  return $ env ! gl

-- Straight outta dev.stephendiehl.com
letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

fresh :: Infer TypedType
fresh = do
  (TVG nextVar) <- get
  put $ TVG $ nextVar + 1
  return $ Fix $ TVar $ TV $ letters !! nextVar

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
      stmt -> return ()


type Globals = Map Global TypedType

localDefs :: (Foldable f) => f (Stmt Local a b) -> Set Local
localDefs = foldMap $ cata $ \case
  Assignment l _ -> S.singleton l
  stmt -> fold stmt

-- For now, used only for the statement list.
inferFunction :: Globals -> RFunDec -> ([Constraint], TFunDec)
inferFunction globals (FD name params ret body) = undefined $ swap $ evalRWS go (Env (M.mapKeys Left M.empty)) (TVG 0)
  where
    numLocals = S.size $ localDefs body
    go = do
      locals <- M.fromList . zip (map (Right . Local) [1..numLocals]) <$> replicateM numLocals fresh 
      local (\(Env globals) -> Env $ locals `M.union` globals) (traverse inferStmt body)

inferModule :: RModule -> ([Constraint], TModule)
inferModule RModule {} = undefined
  where
    

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
  apply s = cata $ \(ExprType t e) -> Fix $ ExprType (apply s t) e
  ftv = cata $ \(ExprType t ftvs) -> ftv t <> fold ftvs

instance Substitutable TStmt where
  apply s = cata $ Fix . first (apply s)
  ftv = cata $ bifold . first ftv

instance Substitutable a => Substitutable [a] where
  apply s = fmap (apply s)
  ftv = foldMap ftv


instance Semigroup Subst where
  Subst s1 <> Subst s2 = Subst $ fmap (apply (Subst s1)) s2 `M.union` s1 -- Uncomment if I stop using foldl and the right Subst can contain substitutions not in the left one. fmap (apply (Subst s2)) s1

instance Monoid Subst where
  mempty = Subst M.empty


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


occursCheck :: TVar -> TypedType -> Bool
occursCheck tv t = S.member tv (ftv t)

bind :: TVar -> TypedType -> Validation (NonEmpty TypeError) Subst
bind tv t | t == Fix (TVar tv)  = mempty
          | occursCheck tv t    = Failure $ NE.singleton $ InfiniteType tv t
          | otherwise           = pure $ Subst $ M.singleton tv t

unifyMany :: [TypedType] -> [TypedType] -> Validation (NonEmpty TypeError) Subst
unifyMany [] [] = mempty
unifyMany t t' | length t /= length t' = Failure $ NE.singleton $ ParameterMismatch t t'
unifyMany t t' = foldl' (<>) mempty $ zipWith unify t t'

unify ::TypedType -> TypedType -> Validation (NonEmpty TypeError) Subst
unify t t' | t == t' = mempty
unify (Fix (TVar v)) t = bind v t
unify t (Fix (TVar v)) = bind v t
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


solve :: [Constraint] -> Either (NonEmpty TypeError) Subst
solve = toEither . foldl' (<>) mempty . fmap (uncurry unify)


typecheck :: RModule -> Either (NonEmpty TypeError) [TStmt]
typecheck (RModule { rmFunctions, rmDataDecs, rmTLStmts }) =
  let (cts, stmts) = undefined
      valSubst = solve cts
  in case valSubst of
    Left tes -> Left tes
    Right su ->
      let finalStmts = apply su stmts
      in case S.toList (ftv finalStmts) of
        []    -> Right finalStmts
        tvars -> Left $ Ambigious <$> NE.fromList tvars
  -- let withUniqueTypes = assignUniqueTypes rstmts  -- Assign each expression (only expressions right now) a unique type.
  -- env <- infer withUniqueTypes                    -- Then, try to infer them.

  -- return $ assignTypes env withUniqueTypes        -- If it works, create actual types from them.
