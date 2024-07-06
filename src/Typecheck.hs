{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Typecheck (typecheck, TypeError(..), dbgTypecheck, dbgPrintConstraints, ftv, unSolve, Subst(..)) where

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
import Data.List ( find, intercalate )
import Data.Bifoldable (bifoldMap)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Either as Either
import Data.Traversable (for)
import Debug.Trace (traceWith, traceShowId)
import ASTPrettyPrinter (tyModule)


-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)




typecheck :: Maybe Prelude -> Module Resolved -> Either (NonEmpty TypeError) (Module Typed)
typecheck mprelude rStmts =
    let env = topLevelEnv mprelude
        senv = makeSEnv mprelude
        -- Three phases
        (tyStmts, constraints) = generateConstraints env senv rStmts
        (errors, su@(Subst _ tysu)) = solveConstraints constraints
        ambiguousTyVars = Set.toList $ ftv tyStmts \\ Map.keysSet tysu
    in case ambiguousTyVars of
        (amb:ambs) ->
            let ambiguousTyVarsErrors = AmbiguousType <$> (amb :| ambs)
            in Left $ NonEmpty.prependList errors ambiguousTyVarsErrors
        _ -> case errors of
            (e:es) -> Left (e :| es)
            [] ->
              let tstmts = substituteTypes (finalizeSubst su) tyStmts
              in Right tstmts



-----------------------------
-- ENVIRONMENT PREPARATION --
-----------------------------

topLevelEnv :: Maybe Prelude -> Env
topLevelEnv mprelude = case mprelude of
  Nothing -> Env { preludeDefines = Nothing, returnType = Nothing }
  Just prelude ->
    let
        defines = dataTypes prelude

        defaultReturnTypeName = "Int"
        defaultReturnType = case Map.lookup defaultReturnTypeName defines of
          Nothing -> error $ "Could not find the default return type '" <> show defaultReturnTypeName <> " in Prelude."
          Just t -> t2ty t
    in Env { preludeDefines = Just defines, returnType = Just defaultReturnType }
  where
    dataTypes :: Prelude -> Map Text (Type Typed)
    dataTypes
      = Map.fromList
      . mapMaybe
        (\case
          Fix (AnnStmt _ (DataDefinition (DD tid tvars _))) -> Just (tid.typeName,  dataType tid tvars)
          _ -> Nothing
        )

-- TODO: explain what makeSEnv is for (after coming back to this function after some time, I have no idea what it does)
makeSEnv :: Maybe Prelude -> StatefulEnv
makeSEnv Nothing = emptySEnv
makeSEnv (Just prelude) = StatefulEnv
  { variables = mempty
  , tvargen = newTVarGen
  , constructors = cons
  , types = ts
  } where
    cons = Map.fromList $ foldMap manyCons $ mapMaybe (\case { Fix (AnnStmt _ (DataDefinition dd)) -> Just dd; _ -> Nothing }) prelude
    manyCons (DD tid tvars cons) =
      let dt = t2ty $ dataType tid tvars
      in fmap
        (\(DC ci ts _) ->
          let cont = case fmap t2ty ts of
                [] -> dt
                tys -> makeType $ TFun (mkFunEnv []) tys dt
          in (ci, Forall (Set.fromList tvars) cont)
        ) cons

    ts = Map.fromList $ oneType <$> mapMaybe (\case { Fix (AnnStmt _ (DataDefinition dd)) -> Just dd; _ -> Nothing }) prelude
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
    conStmtScaffolding = cata (fmap embed . inferAnnStmt)  -- i think it's possible to only map expressions and selectively typecheck this stuff. because you can control the order of evaluation, so, for a function, we can add the fujction name type, then evaluate the statement part.

    -- go through additional layers (in the future also position information)
    inferAnnStmt :: Substitutable a => Base (AnnStmt Resolved) (Infer a) -> Infer (Base (AnnStmt TyVared) a)
    inferAnnStmt (AnnStmt anns rStmt) = case rStmt of
      NormalStmt (Assignment v rexpr) -> do
        texpr@(Fix (ExprType texprt _)) <- subSolve $ inferExpr rexpr
        -- substitution done in subSolve

        -- generalization
        envFtv <- foldMap (\(Forall _ e) -> ftv e) . Map.elems <$> RWS.gets variables  -- 
        let texprtFtv = ftv texprt
        let schemeTyVars = texprtFtv \\ envFtv
        -- Do amibguous check at the end. 

        let (scheme, schemeExpr) = closeOverExpr schemeTyVars texpr -- Replace Left -> Right

        newVar v scheme

        pure $ AnnStmt anns $ NormalStmt $ Assignment v schemeExpr

      NormalStmt rstmt -> do
        tstmt <- bitraverse inferExpr id rstmt

        -- Map expr -> type for unification
        let ttstmt = first (\(Fix (ExprType t _)) -> t) tstmt
        inferStmt ttstmt  -- Then 
        pure $ AnnStmt anns $ NormalStmt tstmt

      FunctionDefinition (FD name params varenv@(VarEnv env) ret) rbody -> do
        (fnt, fdec, fbody) <- subSolve $ do  -- (fnt, fdec, fbody)

          -- RECURSION: Add the (monotype) function to the environment
          f <- fresh
          newVar name (Forall Set.empty f)  -- Empty scheme will prevent instantiation.

          -- Define parameters
          tparams <- (lookupVar . fst) `traverse` params

          -- Unify parameters with their types.
          for_ (zip tparams (fmap snd params)) $ \(v, mt) -> do
            t <- maybe fresh (pure . rt2ty) mt  -- get declared type if any
            uni v t

          -- Unify return type
          tret <- maybe fresh (pure . rt2ty) ret

          -- Actual function typechecking
          tbody <- withReturn tret $ sequenceA rbody

          -- Create env for the function
          envid <- freshTyvar
          envparams <- (\v -> (,) v <$> lookupVar v) `traverse` env
          let tyfunenv = TyFunEnv envid $ mkFunEnv envparams


          let fnt = Fix $ TF' $ Right $ TFun tyfunenv tparams tret
          let fdec = FD name (zip (fmap fst params) tparams) varenv tret
          let fbody = tbody

          pure (fnt, fdec, fbody)

        -- generalization
        envFtv <- foldMap (\(Forall _ e) -> ftv e) . Map.elems <$> RWS.gets variables
        let fntFtv = ftv fnt
        let schemeTyVars = fntFtv \\ envFtv  -- Only variables that exist in the "front" type. (front = the type that we will use as a scheme and will be able to generalize)

        let (scheme, (schemeBody, schemeParams)) = closeOver schemeTyVars (fbody, fdec) fnt

        newVar name scheme

        pure $ AnnStmt anns $ FunctionDefinition schemeParams schemeBody

      DataDefinition (DD tid tvars cons) -> do
        let dt = t2ty $ dataType tid tvars
        newType tid dt

        for_ cons $ \(DC c ts _) -> do
          let tyts = fmap rt2ty ts
          let cont =
                case tyts of
                  [] -> dt
                  tys -> makeType $ TFun (mkFunEnv []) tys dt

          newCon c (Forall (Set.fromList tvars) cont)

        let nucons = fmap (\(DC c ts ann) -> DC c (fmap rt2t ts) ann) cons
        let nudd = DD tid tvars nucons
        pure $ AnnStmt anns $ DataDefinition nudd -- DataDefinition dd

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

      Return mret -> do
        emret <- RWS.asks returnType

        -- Nothing -> Void / ()
        let opty = maybe (findType "Void") pure  -- TODO: Right now, the default is "Void". Should be an empty tuple or something.
        eret <- opty emret
        ret <- opty mret

        ret `uni` eret

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
    inferExprType :: Base (Expr Resolved) (Infer (Expr TyVared)) -> Infer (Base (Expr TyVared) (Expr TyVared))
    inferExprType e = do
      e' <- sequenceA $ mapInnerExprType rt2t e
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
        let ft = makeType $ TFun noFunEnv args ret  -- TODO: very dangerous. only because we know there's going to be a unification later. dangerous like the `restrict` thing ig

        f `uni` ft
        pure ret

      Lam (VarEnv env) params ret -> do
        vars <- traverse lookupVar params  -- creates variables. i have to change the name from lookupVar i guess...
        envvars <- traverse (\v -> (,) v <$> lookupVar v) env
        envid <- freshTyvar  -- TODO: this should be in a function most likely -> all of the env stuff

        let funenv = mkFunEnv envvars
        let t = makeType $ TFun funenv vars ret
        pure t


withReturn :: Type TyVared -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }

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

  -- prepare env mapping
  let envftvs = flip cata est $ \case
        TF' (Right (TFun (TyFunEnv tid envtvs) args ret)) -> Set.singleton tid <> fold envtvs <> fold args <> ret  -- (not anymore -> this fixed the bug) i ignore the env tyvars on purpose - my theory is that they are can be ignored
        t -> fold t

  envmap <- Map.fromList <$> traverse (\tyv -> (,) tyv <$> freshTyvar) (Set.toList envftvs)

  -- Replace each tvar from the scheme with a customized tyvar.
  -- TODO: shouldn't all of this be a part of `subst`?
  let mapTvs :: Base (Type TyVared) a -> Base (Type TyVared) a
      mapTvs = \case
        t@(TF' (Right (TVar tv))) -> case Map.lookup tv tvMapping of
          Just tyv -> TF' $ Left tyv
          Nothing -> t
        (TF' (Right (TFun (TyFunEnv envid fe) args ret))) -> case Map.lookup envid envmap of
          Nothing -> error $ "Should not happen. (" <> show envid <> ") " <> dbgt est
          Just tyv -> TF' $ Right $ TFun (TyFunEnv tyv fe) args ret
        t -> t

  pure $ hoist mapTvs est

-- A scheme turns closed over TyVars into TVars. This requires it to traverse through the expression and replace appropriate vars.
-- We use Substitutable's subst function for this.
closeOver :: Substitutable a => Set TyVar -> a -> Type TyVared -> (Scheme, a)
closeOver tyvars s t = (Forall tvars st, ss)
  where
    (ss, st) = subst newSubst (s, t)  -- substituted expression
    tvars = Set.map (\(TyVar tname) -> TV tname) tyvars  -- change closed over tyvars into tvars
    newSubst = Subst Map.empty $ Map.fromList $ map (\tv@(TyVar tname) -> (tv, makeType $ TVar $ TV tname)) $ Set.toList tyvars  -- that substitution

-- utility for expressions
closeOverExpr :: Set TyVar -> Expr TyVared -> (Scheme, Expr TyVared)
closeOverExpr tyvars e@(Fix (ExprType t _)) = closeOver tyvars e t


-- maybe merge lookupVar and newVar,
--   because that's what the resolving step should... resolve.
newVar :: VarInfo -> Scheme -> Infer ()
newVar v scheme = RWS.modify $ \s -> s { variables = Map.insert v scheme s.variables }

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


-- Actually, all of the member variables are Maybe depending on Prelude. TODO: change it in the future, so It's a sort of Maybe Env.
data Env = Env
  { preludeDefines :: Maybe PreludeTypes
  , returnType :: Maybe (Type TyVared)
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


data Scheme = Forall (Set TVar) (Type TyVared) deriving Show


newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst = Subst (Map TyFunEnv TyFunEnv) (Map TyVar (Type TyVared))
type FullSubst = Map TyVar (Type Typed)  -- The last substitution after substituting all the types


-- Before, this function had a return type Either (NonEmpty TyVar) FullSubst
-- however, it's actually not needed.
-- during generalization, we substitute variables, but we don't add any constraints.
--   for example, in the function, if an argument is unused, two fresh vars are added unified.
--    this unification generates a constraint. substitutions are generated per generalization and during the last substitution. because this constraint exists, on the last substitution it generates a mapping 'a -> 'b, despite none of the tyvars being in the function... which generated the error.
finalizeSubst :: Subst -> FullSubst
finalizeSubst (Subst _ su) = flip Map.mapMaybe su $ transverse $ \case
  TF' (Left _) -> Nothing
  TF' (Right t) -> mapTypeEnv (\(TyFunEnv _ fe) -> fe) <$> sequenceA t
  -- where
    -- sesu = traverse $ transverse $ \case
    --   TF' (Left tyv) -> undefined
    --   TF' (Right t) -> mapTypeEnv (\(TyFunEnv _ fe) -> fe) <$> sequenceA t

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
  ogvars <- RWS.gets variables  -- variables are used to generalize - these will represent the new env. TODO: maybe I should get ftvs from constructors???? From defined types???? Examples???
  (x, constraints) <-  RWS.mapRWS (\(x, s, constraints) -> ((x, constraints), s { variables = ogvars }, constraints)) ctx
  let (_, sub) = solveConstraints constraints  -- TODO: why am I ignoring errors here???????? Is it because it's subSolve - they will also be reported at the end.
  let substituted = sub `subst` x

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
        (Right (TFun lenv lps lr), Right (TFun renv rps rr)) -> do
          su1 <- unifyMany lps rps
          su2 <- unify (subst su1 lr) (subst su1 rr)
          let su3 = lenv `unifyFunEnv` renv

          pure $ compose su3 $ compose su2 su1

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
               | otherwise = pure $ Subst Map.empty $ Map.singleton tyv t

    unifyFunEnv :: TyFunEnv -> TyFunEnv -> Subst
    unifyFunEnv lenv@(TyFunEnv lid _) renv@(TyFunEnv rid _) =
      Subst (Map.fromList [(lenv, env), (renv, env)]) Map.empty -- i don't think we need an occurs check
      where
        newTyVar = joinTyVars lid rid
        env = TyFunEnv newTyVar funEnv

        fe2s = Set.fromList . (\case (TyFunEnv _ (FunEnv ne)) -> ne)
        s2fe = FunEnv . Set.toList
        funEnv = s2fe  $ fe2s lenv <> fe2s renv

    -- small hack to generate unique tyvars from existing ones. now we only need to compare tyvars
    -- TODO: probably find a better way later. also, because theoretically, this string can grow forever...
    joinTyVars :: TyVar -> TyVar -> TyVar
    joinTyVars (TyVar l) (TyVar r) = TyVar $ l <> "_" <> r


    occursCheck :: Substitutable a => TyVar -> a -> Bool
    occursCheck tyv t = tyv `Set.member` ftv t

    report :: TypeError -> Solve Subst
    report te = do
      Solve $ Writer.tell [te]
      pure emptySubst

    emptySubst = Subst Map.empty Map.empty :: Subst

compose :: Subst -> Subst -> Subst
compose sl@(Subst envsl tysl) (Subst envsr tysr) = Subst (Map.map (subst sl) envsr `Map.union` envsl) (Map.map (subst sl) tysr `Map.union` tysl)


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

      TF' (Right t) -> Fix $ mapTypeEnv (\(TyFunEnv _ fe) -> fe) t


tyvar :: TyVar -> Type TyVared
tyvar = Fix . TF' . Left

makeType :: TypeF FunEnv TypeInfo (Type TyVared) -> Type TyVared
makeType = Fix . TF' . Right . mapTypeEnv (TyFunEnv reserved) -- TODO: this is a disgusting hack

reserved :: TyVar
reserved = TyVar $ "''reserved"


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

  subst su@(Subst envsu tysu) = cata $ \case
    TF' (Left ty) -> fromMaybe (tyvar ty) $ Map.lookup ty tysu
    TF' (Right (TFun env params ret)) -> Fix $ TF' $ Right $ TFun (subst su env) params ret
    t -> Fix t

instance Substitutable (TyFunEnv' (Fix TypeF')) where
  ftv (TyFunEnv _ (FunEnv ne)) = (foldMap . foldMap) (ftv . snd) ne -- the big question - is envid an ftv? my answer: no
  subst (Subst envsu _) env = fromMaybe env $ Map.lookup env envsu -- i almost forgot: i added an another field in subst... so yeah, we should substitute.

instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance Substitutable a => Substitutable (NonEmpty a) where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv
  subst su = bimap (subst su) (subst su)

instance (Substitutable a, Substitutable b, Substitutable c) => Substitutable (a, b, c) where
  ftv (x, y, z) = ftv x <> ftv y <> ftv z
  subst su (x, y, z) = (subst su x, subst su y, subst su z)

-- TODO: I want to off myself...
instance Substitutable (Fix (ExprType (Fix TypeF') (Fix (TypeF env TypeInfo)))) where
  ftv = cata $ \(ExprType t expr) -> ftv t <> fold expr
  subst su = cata $ \(ExprType t expr) -> Fix $ ExprType (subst su t) (fmap (subst su) expr)


instance Substitutable (GFunDec fenv c v (Fix TypeF')) where
  ftv (FD _ params _ ret) = ftv ret <> foldMap (ftv . snd) params
  subst su (FD name params env ret) = FD name ((fmap . fmap) (subst su) params) env (subst su ret)

instance Substitutable (Fix (AnnStmtF (BigStmtF datadef (GFunDec fenv ConInfo VarInfo (Fix TypeF')) (StmtF ConInfo VarInfo (Fix (ExprType (Fix TypeF') (Fix (TypeF env TypeInfo)))))))) where
  ftv = cata $ \(AnnStmt _ bstmt) -> case bstmt of
    NormalStmt stmt -> bifoldMap ftv id stmt
    DataDefinition _ -> mempty
    FunctionDefinition fd stmts -> ftv fd <> fold stmts

  subst su = hoist $ \(AnnStmt anns bstmt) -> AnnStmt anns $ case bstmt of
    NormalStmt stmt -> NormalStmt $ first (subst su) stmt
    DataDefinition dd -> DataDefinition dd
    FunctionDefinition fd stmts -> FunctionDefinition (subst su fd) stmts


t2ty :: Type Typed -> Type TyVared
t2ty = hoist (TF' . Right . mapTypeEnv (TyFunEnv reserved))

rt2ty :: Type Resolved -> Type TyVared
rt2ty = hoist $ TF' . Right . mapTypeEnv (const $ TyFunEnv reserved noFunEnv)  -- noFunEnv -> probably bad design

rt2t :: Type Resolved -> Type Typed
rt2t = hoist $ mapTypeEnv $ const noFunEnv  -- noFunEnv -> probably bad design


mkFunEnv :: [(VarInfo, a)] -> FunEnv a
mkFunEnv xs = FunEnv [xs]

noFunEnv :: FunEnv a
noFunEnv = FunEnv []

bidmap :: Bifunctor p => (c -> d) -> p c c -> p d d
bidmap f = bimap f f

findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList


-----
-- DEBUG
----

dbgTypecheck :: Maybe Prelude -> Module Resolved -> ([TypeError], Module Typed)
dbgTypecheck mprelude rStmts =
    let env = topLevelEnv mprelude
        senv = makeSEnv mprelude
        -- Three phases
        (tyStmts', constraints) = generateConstraints env senv rStmts
        tyStmts =
          traceWith tyModule
          tyStmts'
        (errors, su@(Subst _ tysu)) = solveConstraints 
          $ (traceWith dbgPrintConstraints) 
          constraints
        ambiguousTyVars = ftv tyStmts \\ Map.keysSet tysu
    in if (not . null) ambiguousTyVars
          then
            let ambiguousTyvarsErrors = AmbiguousType <$> Set.toList ambiguousTyVars
                errs = errors ++ ambiguousTyvarsErrors

                addMissing :: Set TyVar -> Subst -> Subst
                addMissing tyvs su =
                  let tyvsu = Map.fromList $ (\tyv@(TyVar tyvName) -> (tyv, makeType (TVar (TV tyvName)))) <$> Set.toList tyvs
                      tyvarSubst = Subst Map.empty
                  in tyvarSubst tyvsu `compose` su

                su' = addMissing ambiguousTyVars su
                fsu = finalizeSubst su'
                tstmts = substituteTypes fsu tyStmts
            in (errs, tstmts)
          else
            let fsu = finalizeSubst su
                tstmts = substituteTypes fsu tyStmts
            in (errors, tstmts)



dbgPrintConstraints :: [Constraint] -> String
dbgPrintConstraints = unlines . fmap pc
  where
    pc (tl, tr) = dbgt tl <> " <=> " <> dbgt tr

dbgt :: Type TyVared -> String
dbgt = cata $ \(TF' t) -> case t of
  Left tyv -> "#" <> show tyv
  Right rt -> case rt of
    TCon ti apps -> "(" <> show ti <> unwords apps <> ")"
    TFun env args ret -> dbgenv env <> "(" <> intercalate ", " args <> ") -> " <> ret
    TVar tv -> show tv

dbgenv :: TyFunEnv' String -> String
dbgenv (TyFunEnv envid (FunEnv fe)) = "#" <> show envid <> "[" <> unwords (fmap (\env -> "[" <> intercalate ", " (fmap (\(v, t) -> show v <> " " <> t) env) <> "]") fe) <> "]"

