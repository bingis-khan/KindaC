{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
module Typecheck (typecheck, TypeError(..), dbgTypecheck, dbgPrintConstraints) where

import Typecheck.Types
import AST
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans.RWS (RWS, evalRWS)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (transverse, Base, cata, embed, hoist, project)
import Control.Monad (replicateM)
import Data.Bitraversable (bitraverse)
import Data.Foldable (for_, fold)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Control.Monad.Trans.Writer (runWriter, Writer)
import qualified Control.Monad.Trans.Writer as Writer
import Data.Tuple (swap)
import Data.Bifunctor (bimap, Bifunctor)
import Data.Maybe (mapMaybe, fromMaybe)
import Data.List (find)
import Data.Bifoldable (bifoldMap)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List (intercalate)
import qualified Data.Either as Either


-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)




typecheck :: Maybe Prelude -> Module Resolved -> Either (NonEmpty TypeError) (Module Typed)
typecheck mprelude rStmts =
    let env = makeEnv mprelude
        senv = makeSEnv mprelude
        -- Three phases
        (tyStmts, constraints) = generateConstraints env senv rStmts
        (errors, su) = solveConstraints constraints
    in case finalizeSubst su of
          Left ambiguousTyvars ->
            let ambiguousTyvarsErrors = fmap AmbiguousType ambiguousTyvars
            in Left $ NonEmpty.prependList errors ambiguousTyvarsErrors
          Right fsu -> case errors of
            (e:es) -> Left (e :| es)
            [] ->
              let tstmts = substituteTypes fsu tyStmts
              in Right tstmts



-----------------------------
-- ENVIRONMENT PREPARATION --
-----------------------------

makeEnv :: Maybe Prelude -> Env
makeEnv mprelude = Env { preludeDefines = fmap dataTypes mprelude }
  where
    dataTypes :: Prelude -> Map Text (Type Typed)
    dataTypes 
      = Map.fromList 
      . mapMaybe
        (\case 
          Fix (AnnStmt _ (DataDefinition (DD tid tvars _))) -> Just (tid.typeName,  dataType tid tvars)
          _ -> Nothing
        )

makeSEnv :: Maybe Prelude -> StatefulEnv
makeSEnv Nothing = emptySEnv
makeSEnv (Just prelude) = StatefulEnv
  { variables = mempty
  , tvargen = newTVarGen
  , constructors = cons
  , types = ts
  } where
    cons = Map.fromList $ foldMap manyCons $ mapMaybe (\case { Fix (AnnStmt _ (DataDefinition dd)) -> Just dd; _ -> Nothing }) prelude
    manyCons dd@(DD tid tvars cons) =
      let dt = t2ty $ dataType tid tvars
      in fmap
        (\(DC ci ts _) ->
          let cont = case fmap t2ty ts of
                [] -> dt
                tys -> makeType $ TFun tys dt
          in (ci, Forall (Set.fromList tvars) cont)
        ) cons

    ts = Map.fromList $ fmap oneType $ mapMaybe (\case { Fix (AnnStmt _ (DataDefinition dd)) -> Just dd; _ -> Nothing }) prelude
    oneType (DD tid tvars _) = (tid, t2ty $ dataType tid tvars)


---------------------------
-- CONSTRAINT GENERATION --
---------------------------

generateConstraints :: Env -> StatefulEnv -> Module Resolved -> (Module TyVared, [Constraint])
generateConstraints env senv utModule = (tvModule, constraints)
  where
    (tvModule, constraints) = evalRWS inferModule env senv
    inferModule = inferStmts utModule


-- Parses the top level part of the file.
--  Note: for top level, the return value will be set as U8 in order to "exit" the program.
inferStmts :: (Traversable t) => t (AnnStmt Resolved) -> Infer (t (AnnStmt TyVared))
inferStmts = traverse conStmtScaffolding  -- go through the list (effectively)
  where
    -- go through each statement
    conStmtScaffolding :: AnnStmt Resolved -> Infer (AnnStmt TyVared)
    conStmtScaffolding = transverse inferAnnStmt  -- i think it's possible to only map expressions and selectively typecheck this stuff. because you can control the order of evaluation, so, for a function, we can add the fujction name type, then evaluate the statement part.

    -- go through additional layers (in the future also position information)
    inferAnnStmt :: Base (AnnStmt Resolved) (Infer a) -> Infer (Base (AnnStmt TyVared) a)
    inferAnnStmt (AnnStmt anns rStmt) = do
      tStmt <- inferBigStmt rStmt
      pure $ AnnStmt anns tStmt

    inferBigStmt = \case
      NormalStmt (Assignment v rexpr) -> do
        texpr@(Fix (ExprType texprt _)) <- subSolve $ inferExpr rexpr
        -- substitution done in subSolve

        -- generalization
        envFtv <- foldMap (\(Forall _ e) -> ftv e) . Map.elems <$> RWS.gets variables  -- 
        let texprtFtv = ftv texprt
        let schemeTyVars = texprtFtv \\ envFtv
        -- Do amibguous check at the end. 

        let (scheme, schemeExpr) = makeScheme schemeTyVars texpr -- Replace Left -> Right

        newVar v scheme

        pure $ NormalStmt $ Assignment v schemeExpr

      NormalStmt rstmt -> do
        tstmt <- bitraverse inferExpr id rstmt

        -- Map expr -> type for unification
        let ttstmt = first (\(Fix (ExprType t _)) -> t) tstmt
        inferStmt ttstmt  -- Then 
        pure $ NormalStmt tstmt

      FunctionDefinition (FD name params ret) rbody -> do
        undefined

      DataDefinition dd@(DD tid tvars cons) -> do
        let dt = t2ty $ dataType tid tvars
        newType tid dt

        for_ cons $ \(DC c ts _) ->
          let cont =
                case fmap t2ty ts of
                  [] -> dt
                  tys -> makeType $ TFun tys dt

          in newCon c (Forall (Set.fromList tvars) cont)

        pure $ DataDefinition dd

    -- this is the actual logic.
    -- wtf, for some reason \case produces an error here....
    inferStmt stmt = case stmt of
      Assignment _ _ ->
        error "Assignment should not be handled here."

      MutDefinition v met -> do
        f <- fresh
        newVar v $ Forall Set.empty f  -- no generalization for mutable variables
        for_ met $ \et ->
          f `uni` et

      MutAssignment v et -> do
        vt <- lookupVar v
        vt `uni` et

      If cond _ elseIfs _ -> do
        boolt <- findType "Bool"

        cond `uni` boolt

        for_ elseIfs $ \(t, _) ->
          t `uni` boolt

      _ -> pure ()

      -- FunctionDefinition (FD name params ret) body -> do
      --   -- function name
      --   ft <- newVar name

      --   -- create new scope here
      --   scope $ do
      --     -- params
      --     tparams <- t (\(p, mpt) -> do
      --       tp <- newVar p
      --       tpt <- maybe fresh (pure . t2ty) mpt
      --       tp `uni` tpt

      --       pure (p, tpt)) params
      --     undefined



inferExpr :: Expr Resolved -> Infer (Expr TyVared)
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType e = do
      e' <- sequenceA e
      t <- inferExprLayer $ fmap (\(Fix (ExprType t _)) -> t) e'
      pure $ ExprType t e'

    inferExprLayer = \case
      Lit (LInt _ ) -> findType "Int"

      Var v -> lookupVar v
      Con c -> lookupCon c

      Op l op r | op == NotEquals || op == Equals -> do
        l `uni` r
        findType "Bool"

      -- arithmetic
      Op l _ r -> do
        intt <- findType "Int"
        l `uni` intt
        r `uni` intt

        pure intt

      As x t -> do
        let ty = t2ty t
        x `uni` ty
        pure ty

      Call f args -> do
        ret <- fresh
        let ft = makeType $ TFun args ret

        f `uni` ft
        pure ret

      Lam params ret -> do
        vars <- traverse lookupVar params
        let t = makeType $ TFun vars ret
        pure t


uni :: Type TyVared -> Type TyVared -> Infer ()
uni t1 t2 = RWS.tell [(t1, t2)]

lookupVar  :: VarInfo -> Infer (Type TyVared)
lookupVar v = do
  vars <- RWS.gets variables
  case Map.lookup v vars of
    Just t ->
      instantiate t
    Nothing -> do
      -- Special case used for errors, but also not!
      -- Function parameters need not create a scheme, thus we define variables without the whole scheme thing.
      -- also, they are needed once referenced, so this simplifies it.
      --    I thing I should change the names of those functions.
      t' <- fresh
      let scheme = Forall Set.empty t'
      RWS.modify $ \s -> s { variables = Map.insert v scheme s.variables }
      pure t'

lookupCon :: ConInfo -> Infer (Type TyVared)
lookupCon c = do
  cons <- RWS.gets constructors
  case Map.lookup c cons of
    Just t ->
      instantiate t
    Nothing -> do
      -- This means that the constructor does not exist. This is always an error (caught by the resolver).
      t' <- fresh
      let scheme = Forall Set.empty t'
      RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }
      pure t'


instantiate :: Scheme -> Infer (Type TyVared)
instantiate (Forall tvars est) = do
  -- Instantiate variables for TVars
  let tvarsList = Set.toList tvars
  freshlyMade <- traverse (const freshTyvar) tvarsList  -- make new tyvars (unpacked, used later)
  let tvMapping = Map.fromList $ zip tvarsList freshlyMade  -- Make a TVar -> TyVar mapping

  -- Replace each tvar from the scheme with a customized tyvar.
  let mapTvs :: Base (Type TyVared) a -> Base (Type TyVared) a
      mapTvs = \case
        t@(TF' (Right (TVar tv))) -> case Map.lookup tv tvMapping of
          Just tyv -> TF' $ Left tyv
          Nothing -> t
        t -> t

  pure $ hoist mapTvs est

-- A scheme turns closed over TyVars into TVars. This requires it to traverse through the expression and replace appropriate vars.
-- We use Substitutable's subst function for this.
makeScheme :: Set TyVar -> Expr TyVared -> (Scheme, Expr TyVared)
makeScheme tyvars e = (Forall tvars est, es)
  where
    es@(Fix (ExprType est _)) = subst newSubst e  -- substituted expression
    tvars = Set.map (\(TyVar tname) -> TV tname) tyvars  -- change closed over tyvars into tvars
    newSubst = Map.fromList $ map (\tv@(TyVar tname) -> (tv, makeType $ TVar $ TV tname)) $ Set.toList tyvars  -- that substitution


-- maybe merge lookupVar and newVar,
--   because that's what the resolving step should... resolve.
newVar :: VarInfo -> Scheme -> Infer ()
newVar v scheme = do
  RWS.modify $ \s -> s { variables = Map.insert v scheme s.variables }

newCon :: ConInfo -> Scheme -> Infer ()
newCon c scheme = RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }

newType :: TypeInfo -> Type TyVared -> Infer ()
newType ti t = RWS.modify $ \s -> s { types = Map.insert ti t s.types }



-- Returns a fresh new tyvare
fresh :: Infer (Type TyVared)
fresh = tyvar <$> freshTyvar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyvar :: Infer TyVar
freshTyvar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ TyVar $ letters !! nextVar

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']



findType :: Text -> Infer (Type TyVared)
findType tname = do
  Env { preludeDefines = mprelude } <- RWS.ask
  case mprelude of
    -- Typechecking module WITH imported prelude.
    Just ts -> case Map.lookup tname ts of
      Just t -> pure $ t2ty t
      Nothing -> error $ "Missing prelude type '" <> show tname <> "'. Exiting."

    -- Typechecking without imported prelude. (parsing prelude itself probably, or debugging.)
    -- Use current environment to find required types.
    Nothing -> do
      ts <- RWS.gets types
      case findMap tname (\ti -> ti.typeName) ts of
        Just t -> pure t
        Nothing -> error $ "Required prelude type '" <> show tname <> "' not in scope. Exiting."


-- todo: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer a = RWS Env [Constraint] StatefulEnv a


data Env = Env
  { preludeDefines :: Maybe PreludeTypes
  }

type PreludeTypes = Map Text (Type Typed)

type Constraint = (Type TyVared, Type TyVared)

data StatefulEnv = StatefulEnv
  { variables :: Map VarInfo Scheme
  , constructors :: Map ConInfo Scheme
  , types :: Map TypeInfo (Type TyVared)
  , tvargen :: TVarGen
  }

emptySEnv :: StatefulEnv
emptySEnv = StatefulEnv
  { variables = mempty
  , constructors = mempty
  , tvargen = newTVarGen
  , types = mempty
  }


data Scheme = Forall (Set TVar) (Type TyVared)


newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


type Subst = Map TyVar (Type TyVared)
type FullSubst = Map TyVar (Type Typed)  -- The last substitution after substituting all the types

finalizeSubst :: Subst -> Either (NonEmpty TyVar) FullSubst
finalizeSubst = eitherize . sesu
  where
    sesu = traverse $ transverse $ \case
      TF' (Left tyv) -> SLeft (NonEmpty.singleton tyv)
      TF' (Right t) -> sequenceA t

-- Special, semigrouped Either
data SEither e a
  = SLeft e
  | SRight a
  deriving (Foldable, Functor, Traversable)

instance Semigroup e => Applicative (SEither e) where
  SLeft e1 <*> SLeft e2 = SLeft $ e1 <> e2
  SRight f <*> SRight x = SRight $ f x
  SLeft e <*> _ = SLeft e
  _ <*> SLeft e = SLeft e

  pure = SRight

eitherize :: SEither e a -> Either e a
eitherize (SLeft e) = Left e
eitherize (SRight a) = Right a


------------------------
-- CONSTRAINT SOLVING --
------------------------

subSolve :: Substitutable a => Infer a -> Infer a
subSolve ctx = do
  r <- RWS.ask
  s <- RWS.get
  let (x, _, constraints) = RWS.runRWS ctx r s
  let (_, sub) = solveConstraints constraints
  let substituted = subst sub x

  RWS.tell constraints
  pure substituted


newtype Solve a = Solve { unSolve :: Writer [TypeError] a } deriving (Functor, Applicative, Monad)
data TypeError
  = InfiniteType TyVar (Type TyVared)
  | TypeMismatch (Type TyVared) (Type TyVared)
  | AmbiguousType TyVar
  deriving Show

-- Solve constraints and generate a substitution from those constraints.
-- TODO: Why is do we return a substitution and an error list?
solveConstraints :: [Constraint] -> ([TypeError], Subst)
solveConstraints = swap . runWriter . unSolve .  solve emptySubst
  where
    solve :: Subst -> [Constraint] -> Solve Subst
    solve su [] = pure su
    solve su ((tl, tr):cs) = do
      newsu <- unify tl tr
      solve (newsu `compose` su) (subst newsu cs)

    unify :: Type TyVared -> Type TyVared -> Solve Subst
    unify tl tr =
      case bidmap (fromTF' . project) (tl, tr) of
        (l, r) | l == r -> pure emptySubst
        (Left tyv, _) -> tyv `bind` tr
        (_, Left tyv) -> tyv `bind` tl
        (Right (TFun lps lr), Right (TFun rps rr)) -> do
          su1 <- unifyMany lps rps
          su2 <- unify (subst su1 lr) (subst su1 rr)
          pure $ su2 `compose` su1

        (_, _) -> report $ TypeMismatch tl tr

    unifyMany :: [Type TyVared] -> [Type TyVared] -> Solve Subst
    unifyMany [] [] = pure emptySubst
    unifyMany (tl:ls) (tr:rs) = do
      su1 <- unify tl tr
      su2 <- unifyMany (subst su1 ls) (subst su1 rs)
      pure $ su2 `compose` su1
    unifyMany tl tr = error $ "Should not happen! Type mismatch: " <> show tl <> " and " <> show tr <> "."


    bind :: TyVar -> Type TyVared -> Solve Subst
    bind tyv t | t == tyvar tyv = pure emptySubst
               | occursCheck tyv t =
                  report $ InfiniteType tyv t
                | otherwise = pure $ Map.singleton tyv t

    occursCheck :: Substitutable a => TyVar -> a -> Bool
    occursCheck tyv t = tyv `Set.member` ftv t

    report :: TypeError -> Solve Subst
    report te = do
      Solve $ Writer.tell [te]
      pure emptySubst

    emptySubst = Map.empty :: Subst

compose :: Subst -> Subst -> Subst
compose sl sr = Map.map (subst sl) sr `Map.union` sl


substituteTypes :: FullSubst -> Module TyVared -> Module Typed
substituteTypes fsu tmod = fmap subAnnStmt tmod
  where
    subAnnStmt :: AnnStmt TyVared -> AnnStmt Typed
    subAnnStmt = hoist $ \(AnnStmt ann bstmt) -> AnnStmt ann $ case bstmt of
      NormalStmt stmt -> NormalStmt $ first subExpr stmt
      DataDefinition dd -> DataDefinition dd
      FunctionDefinition dec body -> FunctionDefinition (fmap subType dec) body

    subExpr :: Expr TyVared -> Expr Typed
    subExpr = hoist $ \(ExprType t expr) -> ExprType (subType t) expr

    subType :: Type TyVared -> Type Typed
    subType = cata $ \case
      TF' (Left tyv) -> case Map.lookup tyv fsu of
        Just t -> t
        Nothing ->
          error $ "Failed finding tyvar '" <> show tyv <> "' in Full Subst, which should not happen." <> show (fsu, length tmod)

      TF' (Right t) -> Fix t


tyvar :: TyVar -> Type TyVared
tyvar = Fix . TF' . Left

makeType :: TypeF TypeInfo (Type TyVared) -> Type TyVared
makeType = Fix . TF' . Right

dataType :: TypeInfo -> [TVar] -> Type Typed
dataType tid tvars = Fix $ TCon tid $ fmap (Fix . TVar) tvars


class Substitutable a where
  ftv :: a -> Set TyVar
  subst :: Subst -> a -> a


-- maybe I should just set new types
instance Substitutable (Fix TypeF') where
  ftv = cata $ \case
    TF' (Left ty) -> Set.singleton ty
    t -> fold t

  subst su = cata $ \case
    TF' (Left ty) -> fromMaybe (tyvar ty) $ Map.lookup ty su
    t -> Fix t

instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv
  subst su = bimap (subst su) (subst su)

instance Substitutable (Fix (ExprType (Fix TypeF') (Fix (TypeF TypeInfo)))) where
  ftv = cata $ \(ExprType t expr) -> ftv t <> fold expr
  subst su = cata $ \(ExprType t expr) -> Fix $ ExprType (subst su t) (fmap (subst su) expr)


t2ty :: Type Typed -> Type TyVared
t2ty = hoist (TF' . Right)

bidmap :: Bifunctor p => (c -> d) -> p c c -> p d d
bidmap f = bimap f f

findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList


-----
-- DEBUG
----

dbgTypecheck :: Maybe Prelude -> Module Resolved -> ([TypeError], Module Typed)
dbgTypecheck mprelude rStmts =
    let env = makeEnv mprelude
        senv = makeSEnv mprelude
        -- Three phases
        (tyStmts, constraints) = generateConstraints env senv rStmts
        (errors, su) = solveConstraints constraints
    in case finalizeSubst su of
          Left ambiguousTyvars ->
            let ambiguousTyvarsErrors = fmap AmbiguousType ambiguousTyvars
                errs = errors ++ NonEmpty.toList ambiguousTyvarsErrors

                addMissing :: NonEmpty TyVar -> Subst -> Subst
                addMissing tyvs su =
                  let tyvsu = Map.fromList $ fmap (\tyv@(TyVar tyvName) -> (tyv, makeType (TVar (TV tyvName)))) $ NonEmpty.toList tyvs
                  in tyvsu `compose` su

                su' = addMissing ambiguousTyvars su 
                fsu = Either.fromRight (error "Should not happen") $ finalizeSubst su'

                tstmts = substituteTypes fsu tyStmts
            in (errs, tstmts)
          Right fsu -> case errors of
            errs ->
              let tstmts = substituteTypes fsu tyStmts
              in (errs, tstmts)



dbgPrintConstraints :: [Constraint] -> String
dbgPrintConstraints = unlines . fmap pc
  where
    pc (tl, tr) = pt tl <> " <=> " <> pt tr
    pt = cata $ \(TF' t) -> case t of
      Left tyv -> "#" <> show tyv
      Right rt -> case rt of
        TCon ti apps -> "(" <> show ti <> unwords apps <> ")"
        TFun args ret -> "(" <> intercalate ", " args <> ") -> " <> ret
        TVar tv -> show tv
