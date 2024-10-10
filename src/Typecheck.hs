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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE InstanceSigs #-}

module Typecheck (typecheck, TypeError(..), ftv, unSolve, Subst(..)) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.Trans.RWS (RWST, evalRWST)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (Base, cata, embed, hoist, project, transverse)
import Control.Monad (replicateM)
import Data.Bitraversable (bitraverse)
import Data.Foldable (for_, fold)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Set (Set, (\\), member)
import qualified Data.Set as Set
import Control.Monad.Trans.Writer (runWriter, Writer, runWriterT, WriterT)
import qualified Control.Monad.Trans.Writer as Writer
import Data.Tuple (swap)
import Data.Bifunctor (bimap, Bifunctor)
import Data.Maybe (mapMaybe, catMaybes)
import Data.List ( find )
import Data.Bifoldable (bifoldMap, bifold)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Traversable (for)


import qualified AST.Resolved as R
import qualified AST.TyVared as Ty
import qualified AST.Typed as T

import AST.Converged (Prelude(..), boolTypeName, tlReturnTypeName, intTypeName, PreludeFind (..), boolFind, tlReturnFind, intFind)
import AST.Common (Module, Type, TVar (TV), AnnStmt, Expr, LitType (LInt), UniqueVar, UniqueCon, UniqueType (typeName), EnvUnion, Env, Annotated (Annotated), Op (..), TCon (fromTC, TC), Locality (..), EnvID (..), UnionID (..), Result(..), fromResult)
import AST.Resolved (Resolved)
import AST.Typed (Typed)
import AST.TyVared (TyVared, TyVar, TypeF (..), tyModule)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique, Unique, hashUnique)
import Data.Functor ((<&>))
import Data.List (nub)
import Debug.Trace (traceShow, traceShowWith, traceShowId)


-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)


typecheck :: Maybe Prelude -> Module Resolved -> IO (Either (NonEmpty TypeError) (Module Typed))
typecheck mprelude rStmts = do
    let env = mkContext mprelude  -- extract from Prelude unchanging things about the environment, like predefined types, including the return value.
        senv = makeSEnv mprelude  -- we should generate senv here....

    (tyStmts, constraints) <- generateConstraints env senv rStmts

    -- liftIO $ putStrLn "UNSUBST"
    -- liftIO $ putStrLn $ tyModule tyStmts

    (errors, su) <- liftIO $ solveConstraints constraints
    let finalTyStmts = subst su tyStmts

    -- debug print
    -- liftIO $ putStrLn $ (\(Subst su1 su2) -> show su1) su

    -- liftIO $ putStrLn "\nSUBST"
    -- liftIO $ putStrLn $ tyModule finalTyStmts
    
    pure $ case finalize finalTyStmts of
        Left ambs ->
            let ambiguousTyVarsErrors = AmbiguousType <$> ambs
            in Left $ NonEmpty.prependList errors ambiguousTyVarsErrors
        Right tmod -> case errors of
            (e:es) -> Left (e :| es)
            [] ->
              Right tmod



-----------------------------
-- ENVIRONMENT PREPARATION --
-----------------------------

-- TODO: explain what makeSEnv is for (after coming back to this function after some time, I have no idea what it does)
-- TODO: I had to add IO, because I have to regenerate envIDs. The obvious solution is to not lose them - preserve the env IDs.
-- TODO: I should probably do it only once, when exporting the package (so that empty env IDs are the same).
-- 
makeSEnv :: Maybe Prelude -> Infer StatefulEnv
makeSEnv Nothing = pure emptySEnv
makeSEnv (Just prelude) = do
  -- gather top level variables that should be accessible from prelude
  let vars = Map.fromList $ Map.elems prelude.varNames <&> \case
        Left (T.FD env v params ret) -> -- TODO: very hacky - these env "transforms" shouldn't be here or happen at all for that matter.
          let
            utfun = UTFun (tenv2tyenv env) (fmap (t2ty . snd) params) (t2ty ret)
            scheme = Forall (tv ret <> foldMap (tv . snd) params) utfun
          in (v, scheme)

        Right (v, t) -> 
          (v, Forall Set.empty (UTExternalVariable t))

  cons <- fmap Map.fromList $ for (Map.elems prelude.conNames) $ \case
    (tid, tvars, T.DC ci ts) -> do
      env <- emptyEnv
      let tyts = fmap t2ty ts
          tyvars = fmap (Fix . Ty.TVar) tvars
          utype =
            case tyts of
              [] -> UTCon tid tyvars
              tys ->
                let td = Fix $ TCon tid tyvars
                in UTFun env tys td
      pure (ci, Forall (Set.fromList tvars) utype)

  let ts = Map.fromList $ Map.elems prelude.tyNames <&> \(T.DD tid tvars _) -> (tid, t2ty $ dataType tid tvars)

  pure StatefulEnv
    { variables = vars
    , tvargen = newTVarGen
    , constructors = cons
    , types = ts
    , env = []
    } where


    tv :: Type Typed -> Set TVar
    tv = cata $ \case
      T.TVar tvar -> Set.singleton tvar
      t -> fold t





---------------------------
-- CONSTRAINT GENERATION --
---------------------------

generateConstraints :: Context -> Infer StatefulEnv -> Module Resolved -> IO (Module TyVared, [Constraint])
generateConstraints env senv utModule = do
  (tvStmts, constraints) <- evalRWST ((RWS.put =<< senv)
    >> inferModule) env emptySEnv

  let tvModule = Ty.Mod tvStmts
  pure (tvModule, constraints)
  where
    inferModule = inferStmts $ R.fromMod utModule


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
    inferAnnStmt (R.AnnStmt anns rStmt) = case rStmt of
      -- Old let generalization
      -- NormalStmt (Assignment v rexpr) -> do
      --   texpr@(Fix (ExprType texprt _)) <- subSolve $ inferExpr rexpr
      --   -- substitution done in subSolve

      --   -- generalization
      --   envFtv <- foldMap (\(Forall _ e) -> ftv e) . Map.elems <$> RWS.gets variables  -- 
      --   let texprtFtv = ftv texprt
      --   let schemeTyVars = texprtFtv \\ envFtv
      --   -- Do amibguous check at the end. 

      --   let (scheme, schemeExpr) = closeOverExpr schemeTyVars texpr -- Replace Left -> Right

      --   newVar v scheme

      --   pure $ AnnStmt anns $ NormalStmt $ Assignment v schemeExpr


      R.FunctionDefinition (R.FD varenv name params ret) rbody -> do
        -- |||| start subSolve
        (fdec, fbody) <- subSolve $ do
          -- |||| start withEnv
          (fenv, (fdec, fbody)) <- withEnv varenv $ do

            -- RECURSION: Add the (monotype) function to the environment
            f <- freshUn
            newVar name (Forall Set.empty f)  -- Empty scheme will prevent instantiation.

            -- Define parameters
            tparams <- (lookupVar . fst) `traverse` params

            -- Unify parameters with their types.
            for_ (zip tparams (fmap snd params)) $ \(v, mt) -> do
              t <- maybe fresh rt2ty mt  -- get declared type if any
              uni v t

            -- Unify return type
            tret <- maybe fresh rt2ty ret

            -- Typecheck the actual function
            fbody <- withReturn tret $ sequenceA rbody
            let fdec tenv = Ty.FD tenv name (zip (fmap fst params) tparams) tret

            pure (fdec, fbody)

          -- |||| end withEnv

          let fd = fdec fenv
          pure (fd, fbody)

        -- |||| end subSolve

        -- generalization
        -- TODO: I should put generalization in one function. (Infer ...)
        envFtv <- foldMap (ftv . (\(Forall _ t) -> t)) . Map.elems <$> RWS.gets variables
        let fntFtv = ftv fdec
        let schemeTyVars = fntFtv \\ envFtv  -- Only variables that exist in the "front" type. (front = the type that we will use as a scheme and will be able to generalize)

        let (scheme, sfdec, sfbody) = closeOver schemeTyVars fdec fbody
        newVar name scheme

        pure $ Ty.AnnStmt anns $ Ty.FunctionDefinition sfdec sfbody

      R.DataDefinition (R.DD tid tvars cons) -> do
        newType tid tvars

        nucons <- for cons $ \(Annotated anns (R.DC c ts)) -> do
          tyts <- traverse rt2ty ts
          env <- emptyEnv
          let tyvars = fmap (Fix . Ty.TVar) tvars
          let utype =
                case tyts of
                  [] -> UTCon tid tyvars
                  tys ->
                    let td = Fix $ TCon tid tyvars
                    in UTFun env tys td

          let scheme = Forall (Set.fromList tvars) utype
          newCon c scheme

          pure $ Annotated anns $ Ty.DC c tyts

        let nudd = Ty.DD tid tvars nucons
        pure $ Ty.AnnStmt anns $ Ty.DataDefinition nudd -- DataDefinition dd

      R.NormalStmt rstmt -> do
        tstmt <- bitraverse inferExpr id rstmt

        -- Map expr -> type for unification
        let ttstmt = first (\(expr@(Fix (Ty.ExprType t _))) -> (expr, t)) tstmt
        Ty.AnnStmt anns <$> inferStmt ttstmt


    -- TODO: i think I should split it like so:
    -- R -> Infer (fresh) Ty  <- add fresh variables + convert
    -- then Ty -> Infer ()   <- set constraints
    inferStmt :: R.StmtF (Expr TyVared, Type TyVared) a -> Infer (Ty.StmtF (Expr TyVared) a)
    inferStmt stmt = case stmt of
      -- new, no let-generalization assignment
      R.Assignment v (rexpr, t) -> do
        let scheme = Forall Set.empty $ UTUnchanged t
        newVar v scheme

        pure $ Ty.Assignment v rexpr

      R.MutDefinition v met -> do
        f <- fresh
        newVar v $ Forall Set.empty $ UTUnchanged f

        case met of
          Nothing ->
            pure $ Ty.MutDefinition v (Left f)
          Just (expr, t) -> do
            f `uni` t
            pure $ Ty.MutDefinition v (Right expr)

      R.MutAssignment v (expr, t) -> do
        vt <- lookupVar v
        vt `uni` t
        pure $ Ty.MutAssignment v expr

      R.If (cond, t) ifTrue elseIfs ifFalse -> do
        boolt <- findBuiltinType boolFind

        t `uni` boolt

        for_ elseIfs $ \((_, t), _) ->
          t `uni` boolt

        pure $ Ty.If cond ifTrue ((fmap . first) fst elseIfs) ifFalse

      R.Return (ret, t) -> do
        emret <- RWS.asks returnType

        -- Nothing -> Void / ()
        let opty = maybe (findBuiltinType tlReturnFind) pure  -- When default return type is nothing, this means that we are parsing prelude. Return type from top level should be "Int".
        eret <- opty emret
        t `uni` eret
        pure $ Ty.Return ret

      R.Print (expr, _) ->
        pure $ Ty.Print expr

      R.Pass ->
        pure Ty.Pass

      R.ExprStmt (expr, _) ->
        pure $ Ty.ExprStmt expr



inferExpr :: Expr Resolved -> Infer (Expr TyVared)
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType :: Base (Expr Resolved) (Infer (Expr TyVared)) -> Infer (Base (Expr TyVared) (Expr TyVared))
    inferExprType e = do
      -- map env
      e' <- case e of
        (R.Lam env args body) -> do
          (fenv, (args', body')) <- withEnv env $ do
            -- add types to lambda parameters
            argts <- traverse lookupVar args
            let args' = zip args argts

            -- eval body
            body' <- body
            pure (args', body')

          pure $ Ty.Lam fenv args' body'

        R.As e t -> do
          e' <- e
          t' <- rt2ty t
          pure $ Ty.As e' t'

        R.Lit lt -> pure $ Ty.Lit lt
        R.Var l v -> pure $ Ty.Var l v
        R.Con c -> pure $ Ty.Con c
        R.Op l op r -> do
          l' <- l
          r' <- r
          pure $ Ty.Op l' op r'
        R.Call e args -> do
          liftA2 Ty.Call e (sequenceA args)


      t <- inferExprLayer $ fmap (\(Fix (Ty.ExprType t _)) -> t) e'
      pure $ Ty.ExprType t e'

    -- TODO: merge it with previous function - I don't think it's necessarily needed?
    inferExprLayer = \case
      Ty.Lit (LInt _ ) -> findBuiltinType intFind

      Ty.Var External v -> error "Don't use external variables... yet!"
      Ty.Var _ v -> lookupVar v
      Ty.Con c -> lookupCon c

      Ty.Op l op r | op == NotEquals || op == Equals -> do
        l `uni` r
        findBuiltinType boolFind

      -- arithmetic
      Ty.Op l _ r -> do
        intt <- findBuiltinType intFind
        l `uni` intt
        r `uni` intt

        pure intt

      Ty.As x t -> do
        x `uni` t
        pure t

      Ty.Call f args -> do
        ret <- fresh
        union <- emptyUnion
        let ft = Fix $ TFun union args ret

        f `uni` ft
        pure ret

      Ty.Lam env params ret -> do
        let vars = fmap snd params  -- creates variables. i have to change the name from lookupVar i guess...

        union <- env2union env
        let t = Fix $ TFun union vars ret
        pure t

env2union :: Env TyVared -> Infer (EnvUnion TyVared)
env2union env = do
  unionID <- newUnionID
  pure $ Ty.EnvUnion { Ty.unionID = unionID, Ty.union = [env] }


withReturn :: Type TyVared -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }

uni :: Type TyVared -> Type TyVared -> Infer ()
uni t1 t2 = RWS.tell [(t1, t2)]

lookupVar  :: UniqueVar -> Infer (Type TyVared)
lookupVar v = do
  vars <- RWS.gets variables
  case Map.lookup v vars of
    Just t -> do
      ty <- instantiate t
      addEnv v ty
      pure ty
    Nothing -> do
      -- Special case used for errors, but also not!
      -- Function parameters need not create a scheme, thus we define variables without the whole scheme thing.
      -- also, they are needed once referenced, so this simplifies it.
      --    I thing I should change the names of those functions.
      t' <- fresh
      let scheme = Forall Set.empty $ UTUnchanged t'
      RWS.modify $ \s -> s { variables = Map.insert v scheme s.variables }
      pure t'

lookupCon :: UniqueCon -> Infer (Type TyVared)
lookupCon c = do
  cons <- RWS.gets constructors
  case Map.lookup c cons of
    Just t ->
      instantiate t
    Nothing -> do
      -- This means that the constructor does not exist. This is always an error (caught by the resolver).
      t' <- fresh
      let scheme = Forall Set.empty $ UTUnchanged t'
      RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }
      pure t'


-- when using a type, adds the usage (the tyvared types) to the environment type.
-- this makes it possible to know how many and which types were applied to the polymorphic functions.
addEnv :: UniqueVar -> Type TyVared -> Infer ()
addEnv v ty = RWS.modify $ \s -> s { env = fmap mapFunEnv s.env }
  where
    mapFunEnv :: Env TyVared -> Env TyVared
    mapFunEnv (Ty.Env envid vts) = Ty.Env envid ((v, ty) : vts)

instantiate :: Scheme -> Infer (Type TyVared)
instantiate (Forall tvars ut) = do
  -- Instantiate variables for TVars
  let tvarsList = Set.toList tvars
  freshlyMade <- traverse (const freshTyvar) tvarsList  -- make new tyvars (unpacked, used later)
  let tvMapping = Map.fromList $ zip tvarsList freshlyMade  -- Make a TVar -> TyVar mapping


  let mapTvs :: Base (Type TyVared) a -> Base (Type TyVared) a
      mapTvs = \case
        t@(Ty.TVar tv) -> (maybe t Ty.TyVar (Map.lookup tv tvMapping))
        t -> t

  ty <- instantiateType ut
  pure $ hoist mapTvs ty

instantiateType :: Type Unstantiated -> Infer (Type TyVared)
instantiateType = \case
  UTCon ut ts -> pure $ Fix $ Ty.TCon ut ts
  UTFun env args ret -> do
    union <- singletonUnion env
    pure $ Fix $ Ty.TFun union args ret

  UTyVar tyv -> pure $ Fix $ Ty.TyVar tyv
  UTUnchanged t -> pure t

  UTExternalVariable (Fix (T.TFun tunion params ret)) -> do
    union <- reunion tunion
    pure $ Fix $ Ty.TFun union (fmap t2ty params) (t2ty ret)

  UTExternalVariable t -> pure $ t2ty t


-- Creates a new env union from an already typed module.
reunion :: EnvUnion Typed -> Infer (EnvUnion TyVared)
reunion union = pure $ t2ty <$> reunion' union -- Should I create a new ID?

reunion' :: T.EnvUnionF a -> Ty.EnvUnionF a
reunion' (T.EnvUnion uid envs) = Ty.EnvUnion uid $ fmap tenv2tyenv' envs

tenv2tyenv :: Env Typed -> Env TyVared
tenv2tyenv = fmap t2ty . tenv2tyenv'

tenv2tyenv' :: T.EnvF a -> Ty.EnvF a
tenv2tyenv' (T.Env eid vars) = Ty.Env eid vars


-- A scheme turns closed over TyVars into TVars. This requires it to traverse through the expression and replace appropriate vars.
-- We use Substitutable's subst function for this.
closeOver :: Substitutable a => Set TyVar -> Ty.FunDec -> NonEmpty a -> (Scheme, Ty.FunDec, NonEmpty a)
closeOver tyvars fd body  = (scheme, sfd, sbody)
  where
    scheme = Forall tvars (UTFun senv sparams sret)
    tvars 
      =  fdTVars fd 
      <> Set.map (\(Ty.TyV tname) -> TV tname) tyvars  -- change closed over tyvars into tvars
    sparams = fmap snd svparams
    sbody = subst newSubst body
    sfd@(Ty.FD senv _ svparams sret) = subst newSubst fd  -- substituted expression
    newSubst = Subst Map.empty $ Map.fromList $ map (\tv@(Ty.TyV tname) -> (tv, Fix $ TVar $ TV tname)) $ Set.toList tyvars  -- that substitution

    fdTVars :: Ty.FunDec -> Set TVar
    fdTVars (Ty.FD _ _ params ret) = mconcat $ fmap fdType $ ret : fmap snd params
      where
        fdType :: Type TyVared -> Set TVar
        fdType = cata $ \case
          Ty.TVar tv -> Set.singleton tv
          t -> fold t


-- maybe merge lookupVar and newVar,
--   because that's what the resolving step should... resolve.
newVar :: UniqueVar -> Scheme -> Infer ()
newVar v scheme = RWS.modify $ \s -> s { variables = Map.insert v scheme s.variables }

newCon :: UniqueCon -> Scheme -> Infer ()
newCon c scheme = RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }

newType :: UniqueType -> [TVar] -> Infer ()
newType ti tvars =
  let t = Fix $ Ty.TCon ti $ fmap (Fix . Ty.TVar) tvars

  in RWS.modify $ \s -> s { types = Map.insert ti t s.types }

newEnvID :: Infer EnvID
newEnvID = EnvID <$> liftIO newUnique

newUnionID :: MonadIO io => io UnionID
newUnionID = UnionID <$> liftIO newUnique


-- Returns a fresh new tyvare
fresh :: Infer (Type TyVared)
fresh = tyvar <$> freshTyvar

freshUn :: Infer (Type Unstantiated)
freshUn = UTyVar <$> freshTyvar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyvar :: Infer TyVar
freshTyvar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ Ty.TyV $ letters !! nextVar

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']


findBuiltinType :: PreludeFind -> Infer (Type TyVared)
findBuiltinType (PF tc pf) = do
  Ctx { prelude  = prelud } <- RWS.ask
  case prelud of
    Just p -> pure $ t2ty $ pf p
    Nothing -> do
      ts <- RWS.gets types
      case findMap tc typeName ts of
        Just t -> pure t
        Nothing -> error $ "[TYPE ERROR]: Could not find inbuilt type '" <> show tc <> "'."

-- todo: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer a = RWST Context [Constraint] StatefulEnv IO a

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe (Type TyVared)
  }

mkContext :: Maybe Prelude -> Context
mkContext Nothing = Ctx { prelude = Nothing, returnType = Nothing }
mkContext (Just prelud) = Ctx { prelude = Just prelud, returnType = Just (exprType prelud.toplevelReturn) }
  where
    exprType :: Expr Typed -> Type TyVared
    exprType (Fix (T.ExprType t _)) = t2ty t


type Constraint = (Type TyVared, Type TyVared)

data StatefulEnv = StatefulEnv
  { variables :: Map UniqueVar Scheme
  , constructors :: Map UniqueCon Scheme
  , types :: Map UniqueType (Type TyVared)
  , tvargen :: TVarGen
  , env :: [Env TyVared]
  }

emptySEnv :: StatefulEnv
emptySEnv = StatefulEnv
  { variables = mempty
  , constructors = mempty
  , tvargen = newTVarGen
  , types = mempty
  , env = mempty
  }


-- FUNNY!
-- Closes over tyvars - but this requires the env union to not be instantiated. So we can't put a normal type. How do we do it?
-- The thing is, for functions, we need to be able to modify definitions from imported files...
-- so, we might need to keep everything in tyvared state or to be able to update the EnvUnion
data Scheme = Forall (Set TVar) (Type Unstantiated)

-- THIS. A very funny type meants to be mapped to the normal TyVared variation after
data Unstantiated  -- name is retarded on purpose.
type instance Type Unstantiated = UnstantiatedType
data UnstantiatedType
  = UTCon UniqueType [Type TyVared]
  -- | UTVar TVar
  | UTFun (Env TyVared) [Type TyVared] (Type TyVared)  -- this might be incorrect tho...
  | UTyVar TyVar
  | UTUnchanged (Type TyVared)  -- assignment etc. where the type is already "complete". kind of redundant, because it implies empty TVars...
  | UTExternalVariable (Type Typed)  -- oh shid, we comin outta circus with this one. used for types outside of the module. why? imagine `x` in a base module with some environment. module A imports it and does this: `y = x if rand() else x: x + n` and module B does this: `z = x if rand() else x: x - m`. ------ two different environments. since we parse everything per-module, we have to keep track of the mapping.
  deriving Show


instance Show Scheme where
  show (Forall tvs ts) = show tvs <> ": " <> show ts


newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst = Subst (Map UnionID (EnvUnion TyVared)) (Map TyVar (Type TyVared))


-- base `finalize` on it - remove after.
-- Before, this function had a return type Either (NonEmpty TyVar) FullSubst
-- however, it's actually not needed.
-- during generalization, we substitute variables, but we don't add any constraints.
--   for example, in the function, if an argument is unused, two fresh vars are added unified.
--    this unification generates a constraint. substitutions are generated per generalization and during the last substitution. because this constraint exists, on the last substitution it generates a mapping 'a -> 'b, despite none of the tyvars being in the function... which generated the error.
-- finalizeSubst :: Subst -> FullSubst
-- finalizeSubst (Subst _ su) = flip Map.mapMaybe su $ transverse $ \case
--   _ -> Nothing
  -- Ty.TyVar _ -> Nothing
  -- Ty.TVar _ -> undefined

  -- TF' (Right t) -> mapTypeEnv (\(TyFunEnv envid fe) -> TyFunEnv undefined fe) <$> sequenceA t
  -- where
    -- sesu = traverse $ transverse $ \case
    --   TF' (Left tyv) -> undefined
    --   TF' (Right t) -> mapTypeEnv (\(TyFunEnv _ fe) -> fe) <$> sequenceA t


------------------------
-- CONSTRAINT SOLVING --
------------------------

-- this one solves constraints for one part of the program
--  - needed for generalization
subSolve :: Substitutable a => Infer a -> Infer a
subSolve ctx = do
  ogvars <- RWS.gets variables  -- variables outside of scope. we will remove them after they are solved. (types are not ambiguous if they "come from outside" of the part we are solving (function probably))

  (x, constraints) <-  RWS.mapRWST (fmap (\(x, s, constraints) -> ((x, constraints), s { variables = ogvars }, constraints))) ctx
  (_, sub) <- liftIO $ solveConstraints constraints  -- here, some ambigous variables might come out. we'll find them at the end, so ignore them right now, but we might save them later (in development) for performance.
  let substituted = sub `subst` x

  pure substituted


withEnv :: R.Env -> Infer a -> Infer (Env TyVared, a)
withEnv renv x = do
  env <- emptyEnv
  RWS.modify $ \s -> s { env = env : s.env }
  (e, x') <- RWS.mapRWST (fmap (\(x, s@StatefulEnv { env = (e:ogenvs) }, cs) -> ((e, x), s { env = ogenvs }, cs))) x  -- we're using tail, because we want an error if something happens.

  -- remove things that are part of the inner environment (right now, just an intersection, because renv is already done in Resolver)
  let renvVarSet = Set.fromList $ R.fromEnv renv
  let outerEnv = e { Ty.env = filter ((`member` renvVarSet) . fst) e.env }
  
  pure (outerEnv, x')

-- TODO: should probably change the name
-- renv2tyenv :: R.Env -> Infer (Env TyVared)
-- renv2tyenv (R.Env vars) = do
--   envID <- liftIO newUnique
--   envts <- traverse (\v -> (v,) <$> fresh) vars  -- TODO: i guess we don't need environemnts, since we have addEnv?
--   pure $ Ty.Env { Ty.envID = envID, Ty.env = envts }


newtype Solve a = Solve { unSolve :: WriterT [TypeError] IO a } deriving (Functor, Applicative, Monad, MonadIO)

data TypeError
  = InfiniteType TyVar (Type TyVared)
  | TypeMismatch (Type TyVared) (Type TyVared)
  | MismatchingNumberOfParameters [(Type TyVared)] [(Type TyVared)]
  | AmbiguousType TyVar
  deriving Show

-- Solve constraints and generate a substitution from those constraints.
-- TODO: Why do we return a substitution and an error list?
--    TEMP: IO is temporary for generating unique values
solveConstraints :: [Constraint] -> IO ([TypeError], Subst)
solveConstraints = fmap swap . runWriterT . unSolve . solve emptySubst
  where
    solve :: Subst -> [Constraint] -> Solve Subst
    solve su [] = pure su
    solve su ((tl, tr):cs) = do
      newsu <- unify tl tr
      solve (newsu `compose` su) (subst newsu cs)

    unify :: Type TyVared -> Type TyVared -> Solve Subst
    unify tl tr =
      case bidmap project (tl, tr) of
        (l, r) | l == r -> pure emptySubst
        (Ty.TyVar tyv, _) -> tyv `bind` tr
        (_, Ty.TyVar tyv) -> tyv `bind` tl
        (Ty.TFun lenv lps lr, Ty.TFun renv rps rr) -> do
          su1 <- unifyMany lps rps
          su2 <- unify (subst su1 lr) (subst su1 rr)
          su3 <- liftIO $ lenv `unifyFunEnv` renv

          pure $ compose su3 $ compose su2 su1

        (TCon t ta, TCon t' ta') | t == t' -> do
          unifyMany ta ta'

        (_, _) -> report $ TypeMismatch tl tr

    unifyMany :: [Type TyVared] -> [Type TyVared] -> Solve Subst
    unifyMany [] [] = pure emptySubst
    unifyMany (tl:ls) (tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
      su1 <- unify tl tr
      su2 <- unifyMany (subst su1 ls) (subst su1 rs)
      pure $ su2 `compose` su1
    unifyMany tl tr = report $ MismatchingNumberOfParameters tl tr
    

    bind :: TyVar -> Type TyVared -> Solve Subst
    bind tyv t | t == tyvar tyv = pure emptySubst
               | occursCheck tyv t =
                  report $ InfiniteType tyv t
               | otherwise = pure $ Subst Map.empty $ Map.singleton tyv t

    unifyFunEnv :: EnvUnion TyVared -> EnvUnion TyVared -> IO Subst
    unifyFunEnv lenv@(Ty.EnvUnion { Ty.unionID = lid }) renv@(Ty.EnvUnion { Ty.unionID = rid }) = do
      unionID <- newUnionID
      let env = Ty.EnvUnion { Ty.unionID = unionID, Ty.union = funEnv }

      pure $ Subst (Map.fromList [(lid, env), (rid, env)]) Map.empty -- i don't think we need an occurs check
      --       traceShow ("ENVUNI: " <> show lenv <> "|||||" <> show renv <> "8=====>" <> show env <> "\n") $ 
      where

        union2envset = Set.fromList . (\(Ty.EnvUnion { Ty.union = union }) -> union)
        envset2union = Set.toList
        funEnv = envset2union $ union2envset lenv <> union2envset renv

    occursCheck :: Substitutable a => TyVar -> a -> Bool
    occursCheck tyv t = tyv `Set.member` ftv t

    report :: TypeError -> Solve Subst
    report te = do
      Solve $ Writer.tell [te]
      pure emptySubst

    emptySubst = Subst Map.empty Map.empty :: Subst

compose :: Subst -> Subst -> Subst
compose sl@(Subst envsl tysl) (Subst envsr tysr) = Subst 
  (Map.map (subst sl) envsr `Map.union` envsl)
  (Map.map (subst sl) tysr `Map.union` tysl)


-- this is correct when it comes to typing, but requires me to use applicative shit everywhere. kinda cringe.
type Res = Result (NonEmpty TyVar)
finalize :: Module TyVared -> Either (NonEmpty TyVar) (Module Typed)
finalize (Ty.Mod tystmts) = fmap T.Mod $ fromResult $ traverse annStmt tystmts where
  annStmt :: AnnStmt TyVared -> Res (AnnStmt Typed)
  annStmt = transverse $ \(Ty.AnnStmt anns stmt) ->
    fmap (T.AnnStmt anns) $ case first fExpr stmt of
      Ty.Pass -> pure T.Pass
      Ty.Print expr -> T.Print <$> expr
      Ty.Assignment uv e -> T.Assignment uv <$> e
      Ty.MutDefinition uv e -> T.MutDefinition uv <$> bitraverse fType id e
      Ty.MutAssignment uv e -> T.MutAssignment uv <$> e

      Ty.If cond ifTrue elseIfs melse -> T.If <$> cond <*> sequenceA ifTrue <*> traverse (bitraverse id sequenceA) elseIfs <*> traverse sequenceA melse
      Ty.ExprStmt e -> T.ExprStmt <$> e
      Ty.Return me -> T.Return <$> me

      Ty.DataDefinition dd -> T.DataDefinition <$> fDataDef dd
      Ty.FunctionDefinition fd body -> T.FunctionDefinition <$> fFunDec fd <*> sequenceA body

  fExpr :: Expr TyVared -> Res (Expr Typed)
  fExpr = transverse $ \(Ty.ExprType t e) -> T.ExprType <$> fType t <*> case e of
    Ty.Lit l -> pure $ T.Lit l
    Ty.Var l uv -> pure $ T.Var l uv
    Ty.Con uc -> pure $ T.Con uc

    Ty.Op l op r -> T.Op <$> l <*> pure op <*> r
    Ty.Call c args -> T.Call <$> c <*> sequenceA args
    Ty.As e t -> T.As <$> e <*> fType t
    Ty.Lam env args ret -> T.Lam <$> fEnv env <*> traverse (\(uv, t) -> (uv,) <$> fType t) args <*> ret

  fDataDef :: Ty.DataDef -> Res T.DataDef
  fDataDef (Ty.DD ut tv cons) = T.DD ut tv <$> traverse fDataCon cons

  fDataCon :: Annotated Ty.DataCon -> Res (Annotated T.DataCon)
  fDataCon (Annotated anns (Ty.DC uc tyv)) = Annotated anns . T.DC uc <$> traverse fType tyv

  fFunDec :: Ty.FunDec -> Res T.FunDec
  fFunDec (Ty.FD env uv params ret) = T.FD <$> fEnv env <*> pure uv <*> traverse (\(uv, t) -> (uv,) <$> fType t) params <*> fType ret

  fType :: Type TyVared -> Res (Type Typed)
  fType = transverse $ \case
    Ty.TyVar tyv -> Failure $ NonEmpty.singleton tyv
    Ty.TCon ut ts -> T.TCon ut <$> sequenceA ts
    Ty.TVar tv -> pure $ T.TVar tv
    Ty.TFun union args ret -> T.TFun <$> fEnvUnion union <*> sequenceA args <*> ret where
      fEnvUnion (Ty.EnvUnion unionID envs) = case envs of
        -- Union is empty in this case for example:
        -- f (ff () -> a)  # only the specified type is present without any implied environment,
        --   pass
        [] -> pure $ T.EnvUnion unionID []
        (e:es) -> T.EnvUnion unionID <$> traverse fEnv' (e : es)
      fEnv'(Ty.Env envid ets) = T.Env envid <$> traverse sequenceA ets

  fEnv :: Env TyVared -> Res (Env Typed)
  fEnv (Ty.Env envid ets) = T.Env envid <$> (traverse . traverse) fType ets


tyvar :: TyVar -> Type TyVared
tyvar = Fix . Ty.TyVar

dataType :: UniqueType -> [TVar] -> Type Typed
dataType tid tvars = Fix $ T.TCon tid $ fmap (Fix . T.TVar) tvars



-------------------
-- Substitutable --
-------------------

class Substitutable a where
  ftv :: a -> Set TyVar
  subst :: Subst -> a -> a


instance Substitutable Ty.Mod where
  ftv (Ty.Mod stmts) = ftv stmts
  subst su (Ty.Mod stmts) = Ty.Mod $ fmap (subst su) stmts

instance Substitutable (Fix Ty.AnnotatedStmt) where
  ftv = cata $ \(Ty.AnnStmt _ stmt) -> case stmt of
    Ty.MutDefinition _ (Left t) -> ftv t
    Ty.FunctionDefinition fundec stmts -> ftv fundec <> fold stmts
    stmt -> bifold $ first ftv stmt

  subst su = cata $ embed . sub
    where 
      sub (Ty.AnnStmt ann stmt) = Ty.AnnStmt ann $ case stmt of
        Ty.MutDefinition v (Left t) -> Ty.MutDefinition v (Left (subst su t))
        Ty.FunctionDefinition fundec stmts -> Ty.FunctionDefinition (subst su fundec) stmts
        stmt -> first (subst su) stmt

instance Substitutable (Fix Ty.ExprType) where
  ftv = cata $ \(Ty.ExprType t e) -> ftv t <> case e of
    Ty.As e t -> e <> ftv t
    Ty.Lam env params body -> ftv env <> ftv params <> body
    e -> fold e
  subst su = hoist $ \(Ty.ExprType t e) -> Ty.ExprType (subst su t) (case e of
    Ty.As e t -> Ty.As e (subst su t)
    Ty.Lam env params body -> Ty.Lam (subst su env) (subst su params) body
    e -> e)


instance Substitutable UniqueVar where
  ftv _ = mempty
  subst _ = id


instance Substitutable Ty.FunDec where
  ftv (Ty.FD env _ params ret) = ftv env <> ftv params <> ftv ret
  subst su (Ty.FD env fid params ret) = Ty.FD (subst su env) fid (subst su params) (subst su ret)

-- here we treat the type as if it was a normal type
instance Substitutable UnstantiatedType where
  ftv = \case
    UTyVar tyv -> Set.singleton tyv
    
    UTCon _ apps -> ftv apps
    UTFun env params ret -> ftv env <> ftv params <> ftv ret  -- ???
    UTExternalVariable _ -> mempty
    UTUnchanged t -> ftv t
  subst = error "Should not be called."


instance Substitutable (Fix Ty.TypeF) where
  ftv = cata $ \case
    Ty.TyVar tyv -> Set.singleton tyv
    t -> fold t
  
  subst su@(Subst envm tyvm) = cata $ embed . \case
    Ty.TyVar tyv -> case tyvm !? tyv of
        Nothing -> Ty.TyVar tyv
        Just t -> project t

    -- we might need to substitute the union thing
    Ty.TFun ogUnion@(Ty.EnvUnion { Ty.unionID = uid }) ts t ->

      -- might need to replace the union
      let union = subst su $ case envm !? uid of
            Just eunion -> eunion
            Nothing -> ogUnion

      in Ty.TFun union ts t

    t -> t

instance Substitutable (Ty.EnvUnionF (Fix Ty.TypeF)) where
  ftv (Ty.EnvUnion _ envs) = ftv envs
  subst su@(Subst unions _) (Ty.EnvUnion uid envs) = do
    case unions !? uid of
      Just suUnion -> suUnion
      Nothing -> Ty.EnvUnion uid $ subst su envs

instance Substitutable (Ty.EnvF (Fix Ty.TypeF)) where
  ftv (Ty.Env _ vars) = ftv $ fmap snd vars
  subst su = fmap (subst su)


instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance Substitutable a => Substitutable (NonEmpty a) where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv
  subst su = bimap (subst su) (subst su)


rt2ty :: Type Resolved -> Infer (Type TyVared)
rt2ty = cata (fmap embed . f)
  where
    f = \case
      R.TCon t ts -> do
        ts' <- sequenceA ts
        pure $ Ty.TCon t ts'

      R.TVar tv -> pure $ Ty.TVar tv
      R.TFun params ret -> do
        params' <- sequenceA params
        ret' <- ret
        union <- emptyUnion
        pure $ Ty.TFun union params' ret'

t2ty :: Type Typed -> Type TyVared
t2ty = hoist $ \case
  T.TCon ut apps -> Ty.TCon ut apps
  T.TFun union args ret -> Ty.TFun (reunion' union) args ret
  T.TVar tv -> Ty.TVar tv

emptyUnion :: Infer (EnvUnion TyVared)
emptyUnion = do
  uid <- newUnionID
  pure $ Ty.EnvUnion uid []

singletonUnion :: Env TyVared -> Infer (EnvUnion TyVared)
singletonUnion env = do
  uid <- newUnionID
  pure $ Ty.EnvUnion uid [env]

emptyEnv :: Infer (Env TyVared)
emptyEnv = do
  uid <- newEnvID
  pure $ Ty.Env uid []


bidmap :: Bifunctor p => (c -> d) -> p c c -> p d d
bidmap f = bimap f f


findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList


-----
-- DEBUG
----

-- dbgTypecheck :: Maybe Prelude -> Module Resolved -> ([TypeError], Module Typed)
-- dbgTypecheck mprelude rStmts =
--     let env = topLevelEnv mprelude
--         senv = makeSEnv mprelude
--         -- Three phases
--         (tyStmts', constraints) = generateConstraints env senv rStmts
--         tyStmts =
--           traceWith tyModule
--           tyStmts'
--         (errors, su@(Subst _ tysu)) = solveConstraints
--           $ (traceWith dbgPrintConstraints)
--           constraints
--         ambiguousTyVars = ftv tyStmts \\ Map.keysSet tysu
--     in if (not . null) ambiguousTyVars
--           then
--             let ambiguousTyvarsErrors = AmbiguousType <$> Set.toList ambiguousTyVars
--                 errs = errors ++ ambiguousTyvarsErrors

--                 addMissing :: Set TyVar -> Subst -> Subst
--                 addMissing tyvs su =
--                   let tyvsu = Map.fromList $ (\tyv@(TyVar tyvName) -> (tyv, makeType (TVar (TV tyvName)))) <$> Set.toList tyvs
--                       tyvarSubst = Subst Map.empty
--                   in tyvarSubst tyvsu `compose` su

--                 su' = addMissing ambiguousTyVars su
--                 fsu = finalizeSubst su'
--                 tstmts = substituteTypes fsu tyStmts
--             in (errs, tstmts)
--           else
--             let fsu = finalizeSubst su
--                 tstmts = substituteTypes fsu tyStmts
--             in (errors, tstmts)



-- dbgPrintConstraints :: [Constraint] -> String
-- dbgPrintConstraints = unlines . fmap pc
--   where
--     pc (tl, tr) = dbgt tl <> " <=> " <> dbgt tr

-- dbgt :: Type TyVared -> String
-- dbgt = undefined
-- dbgt = cata $ \(TF' t) -> case t of
--   Left tyv -> "#" <> show tyv
--   Right rt -> case rt of
--     TCon ti apps -> "(" <> show ti <> unwords apps <> ")"
--     TFun env args ret -> dbgenv env <> "(" <> intercalate ", " args <> ") -> " <> ret
--     TVar tv -> show tv

-- dbgenv :: TyFunEnv' String -> String
-- dbgenv (TyFunEnv envid (FunEnv fe)) = "#" <> show envid <> "[" <> unwords (fmap (\env -> "[" <> intercalate ", " (fmap (\(v, t) -> show v <> " " <> ("[" <> unwords (fmap show fe) <> "]")) env) <> "]") fe) <> "]"
