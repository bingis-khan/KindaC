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
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}

module Typecheck (typecheck, TypeError(..)) where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Biapplicative (first)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.Trans.RWS (RWST (RWST), runRWST)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Fix (Fix (Fix))
import Data.Functor.Foldable (Base, cata, embed, hoist, project, transverse)
import Control.Monad (replicateM, zipWithM_, when, join)
import Data.Bitraversable (bitraverse)
import Data.Foldable (for_, fold)
import Data.Set (Set, (\\))
import qualified Data.Set as Set
import Data.Bifunctor (bimap)
import Data.List ( find )
import Data.Bifoldable (bifoldMap, bifold)
import Data.Traversable (for)


import qualified AST.Resolved as R
import qualified AST.Typed as T

import AST.Converged (Prelude(..), PreludeFind (..), boolFind, tlReturnFind, intFind)
import AST.Common (TVar (TV), LitType (LInt), UniqueVar, UniqueType (typeName), Annotated (Annotated), Op (..), EnvID (..), UnionID (..), ctx, type (:.) (..), ppCon, Locality (..), ppUnionID, phase, ctxPrint, ctxPrint')
import Control.Monad.IO.Class (liftIO, MonadIO)
import Data.Unique (newUnique)
import Data.Functor ((<&>))
import Data.Maybe (fromMaybe, mapMaybe)
import AST.Typed (TyVar)
import Text.Printf (printf)
import Control.Applicative (liftA3)
import Debug.Trace (traceShowWith)
import Data.List.NonEmpty (NonEmpty)
import Misc.Memo (memo, Memo(..))


-- I have some goals alongside rewriting typechecking:
--   - The previous typechecker was unreadable. Use appropriate variable names, avoid the functional composition hell.
--   - Use comments even if something is obvious. (but not too obvious?)


typecheck :: Maybe Prelude -> R.Module -> IO ([TypeError], T.Module)
typecheck mprelude rStmts = do
    -- let env = mkContext mprelude  -- extract from Prelude unchanging things about the environment, like predefined types, including the return value.
    --     senv = makeSEnv mprelude  -- we should generate senv here....

    let env = Ctx { prelude = mprelude, returnType = Nothing }
    let senv = pure emptySEnv
    (tStmts, su, errs) <- generateSubstitution env senv rStmts

    phase "Typechecking (Before substitution)"
    ctxPrint T.tModule tStmts

    let tStmts' = subst su tStmts
    -- liftIO $ putStrLn $ dbgSubst su
    let errs' = errs <> (AmbiguousType <$> Set.toList (ftv tStmts'))
    pure (errs', tStmts')

    -- -- liftIO $ putStrLn "UNSUBST"
    -- -- liftIO $ putStrLn $ Ty.tyModule tyStmts

    -- (errors, su) <- liftIO $ solveConstraints constraints
    -- let finalTyStmts = subst su tyStmts

    -- -- debug print
    -- -- liftIO $ putStrLn $ (\(Subst su1 su2) -> show su1 <> "\n" <> show su2) su

    -- -- liftIO $ putStrLn "\nSUBST"
    -- -- liftIO $ putStrLn $ Ty.tyModule finalTyStmts

    -- pure $ case finalize finalTyStmts of
    --     Left ambs ->
    --         let ambiguousTyVarsErrors = AmbiguousType <$> ambs
    --         in Left $ NonEmpty.prependList errors ambiguousTyVarsErrors
    --     Right tmod -> case errors of
    --         (e:es) -> Left (e :| es)
    --         [] ->
    --           Right tmod



-- -----------------------------
-- -- ENVIRONMENT PREPARATION --
-- -----------------------------

-- -- TODO: explain what makeSEnv is for (after coming back to this function after some time, I have no idea what it does)
-- -- TODO: I had to add IO, because I have to regenerate envIDs. The obvious solution is to not lose them - preserve the env IDs.
-- -- TODO: I should probably do it only once, when exporting the package (so that empty env IDs are the same).
-- -- 
-- makeSEnv :: Maybe Prelude -> Infer StatefulEnv
-- makeSEnv Nothing = pure emptySEnv
-- makeSEnv (Just prelude) = do
--   -- gather top level variables that should be accessible from prelude
--   let vars = Map.fromList $ Map.elems prelude.varNames <&> \case
--         Left (T.FD env v params ret) -> -- TODO: very hacky - these env "transforms" shouldn't be here or happen at all for that matter.
--           let
--             utfun = UTFun (tenv2tyenv env) (fmap (t2ty . snd) params) (t2ty ret)
--             scheme = Forall (tv ret <> foldMap (tv . snd) params) utfun
--           in (v, scheme)

--         Right (v, t) ->
--           (v, Forall Set.empty (UTExternalVariable t))

--   cons <- fmap Map.fromList $ for (Map.elems prelude.conNames) $ \case
--     (tid, tvars, unions, T.DC ci ts) -> do
--       env <- emptyEnv
--       let tyts = fmap t2ty ts
--           tyvars = fmap (Fix . Ty.TVar) tvars
--       utype <- do
--             unions' <- reunion `traverse` unions
--             pure $ UTCon tyts tid tyvars unions'
--       pure (ci, Forall (Set.fromList tvars) utype)

--   ts <- fmap Map.fromList $ for (Map.elems prelude.tyNames) $ \(T.DD tid tvars unions _) -> (tid,) . Ty.TypeCon tid (Fix . Ty.TVar <$> tvars) <$> traverse reunion unions

--   pure StatefulEnv
--     { variables = vars
--     , tvargen = newTVarGen
--     , constructors = cons
--     , types = ts
--     , env = []
--     } where


--     tv :: Type Typed -> Set TVar
--     tv = cata $ \case
--       T.TVar tvar -> Set.singleton tvar
--       t -> fold t





-- ---------------------------
-- -- CONSTRAINT GENERATION --
-- ---------------------------

generateSubstitution :: Context -> Infer StatefulEnv -> R.Module -> IO (T.Module, Subst, [TypeError])
generateSubstitution env senv rModule = do
  (tvModule, s, errors) <- runRWST infer env emptySEnv

  pure (tvModule, s.typeSubstitution, errors)
  where
    infer = do
      RWS.put =<< senv


      dds <- inferDatatypes rModule.datatypes
      fns <- inferFunctions rModule.functions
      tls <- inferTopLevel rModule.toplevel
      exs <- inferExports rModule.exports
      pure $ T.Mod
        { T.toplevelStatements = tls
        , T.exports = exs
        , T.functions = fns
        , T.datatypes = dds
        }

    inferFunctions fns = for fns inferFunction
    inferDatatypes dds = for dds inferDataDef
    inferTopLevel = inferStmts


-- Parses the top level part of the file.
--  Note: for top level, the return value will be set as U8 in order to "exit" the program.
inferStmts :: (Traversable t) => t R.AnnStmt -> Infer (t T.AnnStmt)
inferStmts = traverse conStmtScaffolding  -- go through the list (effectively)
  where
    -- go through each statement
    conStmtScaffolding :: R.AnnStmt -> Infer T.AnnStmt
    conStmtScaffolding = cata (fmap embed . inferAnnStmt)  -- i think it's possible to only map expressions and selectively typecheck this stuff. because you can control the order of evaluation, so, for a function, we can add the fujction name type, then evaluate the statement part.

    -- go through additional layers (in the future also position information)
    inferAnnStmt :: Base R.AnnStmt (Infer a) -> Infer (Base T.AnnStmt a)
    inferAnnStmt (O (Annotated anns rStmt)) = do
        tstmt <- bitraverse inferExpr id rStmt

        -- Map expr -> type for unification
        let ttstmt = first (\expr@(Fix (T.TypedExpr t _)) -> (expr, t)) tstmt
        O . Annotated anns <$> inferStmt ttstmt

--       R.FunctionDefinition (R.FD varenv name params ret) rbody -> do
--         -- |||| start subSolve
--         (fdec, fbody) <- subSolve $ do
--           -- |||| start withEnv
--           (fenv, (fdec, fbody)) <- withEnv varenv $ do

--             -- RECURSION: Add the (monotype) function to the environment
--             f <- freshUn
--             newVar name (Forall Set.empty f)  -- Empty scheme will prevent instantiation.

--             -- Define parameters
--             tparams <- (lookupVar . fst) `traverse` params

--             -- Unify parameters with their types.
--             for_ (zip tparams (fmap snd params)) $ \(v, mt) -> do
--               t <- maybe fresh rt2ty mt  -- get declared type if any
--               uni v t

--             -- Unify return type
--             tret <- maybe fresh rt2ty ret

--             -- Typecheck the actual function
--             fbody <- withReturn tret $ sequenceA rbody
--             let fdec tenv = Ty.FD tenv name (zip (fmap fst params) tparams) tret

--             pure (fdec, fbody)

--           -- |||| end withEnv

--           let fd = fdec fenv
--           pure (fd, fbody)

--         -- |||| end subSolve

--         -- generalization
--         -- TODO: I should put generalization in one function. (Infer ...)
--         envFtv <- foldMap (ftv . (\(Forall _ t) -> t)) . Map.elems <$> RWS.gets variables
--         let fntFtv = ftv fdec
--         let schemeTyVars = fntFtv \\ envFtv  -- Only variables that exist in the "front" type. (front = the type that we will use as a scheme and will be able to generalize)

--         let (scheme, sfdec, sfbody) = closeOver schemeTyVars fdec fbody
--         newVar name scheme

--         pure $ Ty.AnnStmt anns $ Ty.FunctionDefinition sfdec sfbody

--       R.DataDefinition (R.DD tid tvars cons) -> do
--         -- definition of type should go here.

--         -- Envs in Datatypes: gather all of the unions.
--         -- to do that:
--         --  1. get unions from function types
--         --  2. get unions from TCons (which previously got them from function types)
--         -- I need to have the same order for them. This is important!! (I don't have a better way for now.)
--         let exunzip = first concat . unzip
--         typez <- RWS.gets types
--         (unions, nucons) <- fmap exunzip $ for cons $ \(Annotated anns (R.DC c ts)) -> do
--           let
--             mapTypeAndExtractUnion :: Base (Type Resolved) (Infer ([EnvUnion TyVared], Type TyVared)) -> Infer ([EnvUnion TyVared], Ty.TypeF (Type TyVared))
--             mapTypeAndExtractUnion = \case
--               R.TCon t ts -> do
--                 case typez !? t of
--                   Nothing -> error $ "Could not find type " <> show t <> ". This is probably impossible?? Maybe???"
--                   Just (Ty.TypeCon ut _tyvars tconUnions) -> do
--                     (paramUnions, ts') <- exunzip <$> sequenceA ts
--                     let unions = tconUnions <> paramUnions
--                     pure (unions, Ty.TCon ut ts' unions)

--               R.TVar tv -> pure (mempty, Ty.TVar tv)

--               R.TFun params ret -> do
--                 (paramUnions, params') <- exunzip <$> sequenceA params
--                 (retUnions, ret') <- ret
--                 funEmpty <- emptyUnion  -- this union is for the function itself.
--                 let union = funEmpty : paramUnions <> retUnions
--                 pure (union, Ty.TFun funEmpty params' ret')

--           (unions, tyts) <- fmap (first concat . unzip) $ for ts $ cata $ (fmap . fmap) embed . mapTypeAndExtractUnion
--           pure (unions, (c, tyts, tvars, anns))


--         -- Now, let's construct the datatypes using the collected unions from all of the constructors.
--         cons' <- for nucons $ \(uc, tyts, tvars, anns) -> do
--           let tyvars = Fix . Ty.TVar <$> tvars
--           let utype = UTCon tyts tid tyvars unions

--           let scheme = Forall (Set.fromList tvars) utype
--           newCon uc scheme
--           pure $ Annotated anns $ Ty.DC uc tyts

--         let nudd = Ty.DD tid tvars unions cons'

--         newType tid tvars unions
--         pure $ Ty.AnnStmt anns $ Ty.DataDefinition nudd -- DataDefinition dd

--       R.NormalStmt rstmt -> do


    -- TODO: i think I should split it like so:
    -- R -> Infer (fresh) Ty  <- add fresh variables + convert
    -- then Ty -> Infer ()   <- set constraints
    inferStmt :: R.StmtF (T.Expr, T.Type) a -> Infer (T.StmtF T.Expr a)
    inferStmt stmt = case stmt of
      R.Assignment v (rexpr, t) -> do
        -- TODO: how do we distinguish function call with variable during typechecking.
        vt <- var v
        vt `uni` t

        pure $ T.Assignment v rexpr

      R.Mutation v loc (expr, t) -> do
        vt <- var v
        vt `uni` t
        addEnv (T.DefinedVariable v) vt
        pure $ T.Mutation v loc expr

      R.If (cond, condt) ifTrue elseIfs ifFalse -> do
        boolt <- findBuiltinType boolFind

        condt `uni` boolt

        for_ elseIfs $ \((_, t), _) ->
          t `uni` boolt

        pure $ T.If cond ifTrue ((fmap . first) fst elseIfs) ifFalse

      R.Switch (rswitch, switchType) cases -> do
        tdecons <- traverse inferCase cases
        for_ tdecons $ \(_, dec) ->
          switchType `uni` dec
        pure $ T.Switch rswitch (fst <$> tdecons)
        where
          inferCase R.Case { R.deconstruction = decon, R.caseCondition = caseCon, R.body = body } = do
            tdecon <- inferDecon decon
            let tCaseCon = fst <$> caseCon
            pure (T.Case tdecon tCaseCon body, decon2type tdecon)

          decon2type :: T.Decon -> T.Type
          decon2type (Fix dec) = case dec of
            T.CaseVariable t _ -> t
            T.CaseConstructor t _ _ -> t

          inferDecon :: R.Decon -> Infer T.Decon
          inferDecon = cata $ fmap embed . f where
            f = \case
              -- R.CaseVariable uv -> do
              --   t <- lookupVar uv

              --   pure (T.CaseVariable t uv)

              -- R.CaseConstructor uc args -> do

              --   -- HACK! Unify the case statement by creating a fake function type.
              --   ct <- lookupCon uc
              --   let conOnly = case ct of
              --         Fix (T.TCon {}) -> ct
              --         Fix (T.TFun _ _ c@(Fix (T.TCon {}))) -> c

              --         -- error in resolver: just return a fresh type. (lookupCon already does that)
              --         _ -> ct

              --   args' <- sequenceA args
              --   syntheticConType <- case args' of
              --         [] -> pure conOnly
              --         (_:_) -> do
              --           un <- emptyUnion
              --           pure $ Fix $ TFun un (decon2type <$> args') conOnly

              --   ct `uni` syntheticConType
              --   pure (T.CaseConstructor conOnly uc args')
              _ -> undefined

      R.Return (ret, t) -> do
        emret <- RWS.asks returnType

        -- Nothing -> Void / ()
        let opty = maybe (findBuiltinType tlReturnFind) pure  -- When default return type is nothing, this means that we are parsing prelude. Return type from top level should be "Int".
        eret <- opty emret
        t `uni` eret
        pure $ T.Return ret

      R.Print (expr, _) ->
        pure $ T.Print expr

      R.Pass ->
        pure T.Pass

      R.ExprStmt (expr, _) ->
        pure $ T.ExprStmt expr

      R.EnvDef rfn -> do
        fn <- inferFunction rfn
        -- liftIO $ putStrLn $ "This env... " <> ctx T.tEnv fn.functionDeclaration.functionEnv
        pure $ T.EnvDef fn.functionDeclaration.functionEnv



inferExpr :: R.Expr -> Infer T.Expr
inferExpr = cata (fmap embed . inferExprType)
  where
    inferExprType :: Base R.Expr (Infer T.Expr) -> Infer (Base T.Expr T.Expr)
    inferExprType e = do
      -- map env
      e' <- case e of
        (R.Lam _ env args body) -> do

          -- add types to lambda parameters
          argts <- traverse var args
          let args' = zip args argts

          -- eval body
          (fenv, body') <- withEnv env body

          pure $ T.Lam fenv args' body'

        R.As ae t -> do
          e' <- ae
          t' <- inferType t
          pure $ T.As e' t'

        R.Lit lt -> pure $ T.Lit lt
        R.Var l v -> do
          T.Var l <$> inferVariable v

        R.Con c -> T.Con <$> newEnvID <*> inferConstructor c  -- NOTE: for `newEnvID`, see note in AST.Typed near this constructor.
        R.Op l op r -> liftA2 (\l' r' -> T.Op l' op r') l r

        R.Call callee args -> do
          liftA2 T.Call callee (sequenceA args)


      t <- inferExprLayer $ fmap (\(Fix (T.TypedExpr t _)) -> t) e'
      pure $ T.TypedExpr t e'

    -- TODO: merge it with previous function - I don't think it's necessarily needed?
    inferExprLayer = \case
      T.Lit (LInt _ ) -> findBuiltinType intFind

      T.Var loc v -> do
        t <- instantiateVariable v

        when (loc == FromEnvironment) $ do
          addEnv v t

        pure t
      T.Con env c -> instantiateConstructor env c

      T.Op l op r | op == NotEquals || op == Equals -> do
        l `uni` r
        findBuiltinType boolFind

      -- arithmetic
      T.Op l _ r -> do
        intt <- findBuiltinType intFind
        l `uni` intt
        r `uni` intt

        pure intt

      T.As x t -> do
        x `uni` t
        pure t

      T.Call f args -> do
        ret <- fresh
        union <- emptyUnion
        let ft = Fix $ T.TFun union args ret

        f `uni` ft
        pure ret

      T.Lam env params ret -> do
        let vars = snd <$> params  -- creates variables. i have to change the name from lookupVar i guess...

        union <- mkUnion env
        let t = Fix $ T.TFun union vars ret
        pure t


inferVariable :: R.Variable -> Infer T.Variable
inferVariable = \case
  R.DefinedVariable v -> pure $ T.DefinedVariable v
  R.ExternalFunction fn -> pure $ T.DefinedFunction fn
  R.DefinedFunction fn -> T.DefinedFunction <$> inferFunction fn

inferConstructor :: R.Constructor -> Infer T.DataCon
inferConstructor = \case
  R.ExternalConstructor c -> pure c
  R.DefinedConstructor (R.DC rdd uc _ _) -> do
    (T.DD _ _ cons _) <- inferDataDef rdd

    -- HACK?: Find constructor through memoized DataDefinition.
    let dc =  fromMaybe (error $ printf "[Compiler Error] Could not find constructor %s." (ctx ppCon uc)) $ find (\(T.DC _ uc' _ _) -> uc == uc') cons

    pure dc


inferType :: R.Type -> Infer T.Type
inferType = cata $ (.) (fmap embed) $ \case
  R.TCon (R.DefinedDatatype rdd) rparams -> do
    dd <- inferDataDef rdd
    params <- sequenceA rparams
    let unions = extractUnionsFromDataType dd
    pure $ T.TCon dd params unions

  R.TCon (R.ExternalDatatype dd) rparams -> do
    params <- sequenceA rparams
    let unions = extractUnionsFromDataType dd
    pure $ T.TCon dd params unions

  R.TVar tv -> pure $ T.TVar tv

  R.TFun rargs rret -> liftA3 T.TFun emptyUnion (sequenceA rargs) rret



inferDataDef :: R.DataDef -> Infer T.DataDef
inferDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $
  \(R.DD ut tvars rdcs anns) addMemo -> do

    rec
      -- TVar correctness should be checked in Resolver!
      let dd = T.DD ut tvars dcs anns

      addMemo dd

      dcs <- for rdcs $ \(R.DC _ uc rts dcAnn)-> do
        ts <- traverse inferType rts
        let dc = T.DC dd uc ts dcAnn
        pure dc

    pure dd

-- TODO: clean up all the mapUnion shit. think about proper structure.
mapUnion :: UniqueType -> T.Type -> [T.EnvUnion]
mapUnion ut (Fix t) = case t of
  -- TODO: explain what I'm doing - somehow verify if it's correct (with the unions - should types like `Proxy (Int -> Int)` store its union in conUnions? or `Ptr (Int -> Int)`?).
  T.TCon (T.DD tut _ _ _) paramts conUnions
    -- breaks cycle with self referential datatypes.
    | tut == ut -> concatMap (mapUnion ut) paramts
    | otherwise -> conUnions <> concatMap (mapUnion ut) paramts

  T.TFun u args ret -> [u] <> concatMap (mapUnion ut) args <> mapUnion ut ret
  T.TVar _ -> []
  T.TyVar _ -> []


inferFunction :: R.Function -> Infer T.Function
inferFunction = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \rfn addMemo -> do

  -- must substitute the function
  -- TODO: should this maybe be in "instantiateVariable"? It will be more correct, but we will have to repeat the computation each time.
  fn <- generalize $ mdo

    -- Infer function declaration.
    let rfundec = rfn.functionDeclaration

    params <- for rfundec.functionParameters $ \(v, definedType) -> do
      vt <- var v
      case definedType of
        Just rt -> do
          t <- inferType rt

          vt `uni` t

        Nothing -> pure ()

      -- NOTE: because of the way we typecheck recursive functions,
      -- we should put `vt` here. This will not generalize and
      -- recursive functions will work correctly.
      -- `vt` will only be substituted and generalized after we
      -- finish typechecking this function - GOOD!
      pure (v, vt)

    ret <- maybe fresh inferType rfundec.functionReturnType

    envID <- newEnvID
    let recenv = T.RecursiveEnv envID (null $ R.fromEnv rfundec.functionEnv)
    let fundec = T.FD recenv rfundec.functionId params ret
    let fun = T.Function { T.functionDeclaration = fundec, T.functionBody = body }

    -- Add *ungeneralized* type.
    addMemo fun

    -- Infer body.
    (envc, body) <- withEnv' rfundec.functionEnv $ withReturn ret $ inferStmts rfn.functionBody

    -- now, replace it with a non-recursive environment.
    let env = T.Env envID envc
    let fundec' = fundec { T.functionEnv = env }
    let fun' = fun { T.functionDeclaration = fundec' }

    pure fun'

  -- Add *generalized* version.
  addMemo fn

  pure fn


inferExports :: R.Exports -> Infer T.Exports
inferExports e = do
  dts <- traverse inferDataDef e.datatypes
  fns <- traverse inferFunction e.functions
  pure $ T.Exports
    { variables = e.variables
    , functions = fns
    , datatypes = dts
    }


-- Like previous `subSolve`. 
-- Preemptively (tFunDec fn.functionDeclarationitutes the result of the computation.
generalize :: Infer T.Function -> Infer T.Function
generalize fx = do
  unsuFn <- fx
  -- liftIO $ putStrLn $ ctx T.tFunction unsuFn
  csu <- RWS.gets typeSubstitution

  -- First substitution will substitute types that are already defined.
  -- What's left will be TyVars that are in the definition.
  let fn = subst csu unsuFn

  let
    -- gather tvars defined ONLY in this function
    -- the theory is that any external variables have types from the function environment only.
    typesFromOutside = ftv fn.functionDeclaration.functionEnv
    typesFromDeclaration = ftv (snd <$> fn.functionDeclaration.functionParameters) <> ftv fn.functionDeclaration.functionReturnType
    scheme = typesFromDeclaration \\ typesFromOutside

    -- Then substitute it.
    asTVar (T.TyV tyname) = Fix $ T.TVar $ TV tyname

    su = Subst mempty $ Map.fromSet asTVar scheme

  -- This one is generalized.
  let generalizedFn = subst su fn

  -- Also, remember the substitution! (tvars might escape the environment)
  --  TODO: not sure if that's the best way. check it.
  substituting $ do
    for_ (Set.toList scheme) $ \tv ->
      bind tv (asTVar tv)

  -- liftIO $ putStrLn $ ctx T.tFunction generalizedFn
  -- liftIO $ printf "Just generalized: %s\n" (ctx T.tEnv generalizedFn.functionDeclaration.functionEnv)
  -- liftIO $ printf "Types from declaration: %s\n" (show $ fmap (ctx T.tTyVar) $ Set.toList typesFromDeclaration)

  pure generalizedFn


-- Substitute return type for function.
withReturn :: T.Type -> Infer a -> Infer a
withReturn ret = RWS.local $ \e -> e { returnType = Just ret }



------
-- Instantiation
------

instantiateVariable :: T.Variable -> Infer T.Type
instantiateVariable = \case
  T.DefinedVariable v -> var v
  T.DefinedFunction fn -> do
    let
      tvars :: T.Type -> Set TVar
      tvars = cata $ \case
        T.TVar tv -> Set.singleton tv
        t -> fold t

      decl = fn.functionDeclaration

      scheme = foldMap (tvars . snd) decl.functionParameters <> tvars decl.functionReturnType

    -- substitute with fresh ones
    -- fmap (traceShowWith (fmap (ctx T.tType)) . 
    tvmap <- fmap (Map.fromList) $ traverse (\tv -> (,) tv <$> fresh) $ Set.toList scheme
    let mapTVs = mapTVsWithMap tvmap

    -- Create type from function declaration
    let fundec = fn.functionDeclaration
    fnUnion <- mkUnion fundec.functionEnv
    let fnType = Fix $ T.TFun fnUnion (mapTVs . snd <$> fundec.functionParameters) (mapTVs fundec.functionReturnType)

    pure fnType

instantiateConstructor :: EnvID -> T.DataCon -> Infer T.Type
instantiateConstructor envID = \case
  T.DC dd@(T.DD _ tvs _ _) _ [] _ -> do
    itvs <- traverse (const fresh) tvs
    let unions = extractUnionsFromDataType dd
    unions' <- cloneUnions unions
    pure $ Fix $ T.TCon dd itvs unions'

  dc@(T.DC dd@(T.DD ut tvs cons _) _ usts@(_:_) _) -> do
    tvmap <- Map.fromList <$> traverse (\tv -> (tv,) <$> fresh) tvs

    -- let unions = extractUnionsFromDataType dd
    let cons2newUnions = cloneUnions . concatMap extractUnionsFromConstructor
    unionsBeforeConstructor <- cons2newUnions $ takeWhile (/=dc) cons
    unionsAfterConstructor <- cons2newUnions $ drop 1 $ dropWhile (/=dc) cons


    let
      mapTVs = mapTVsWithMap tvmap

      ts = mapTVs <$> usts

    tsWithClonedUnions <- traverse (cloneUnionInType ut) ts

    let
      unionsInConstructor = concatMap (mapUnion ut) tsWithClonedUnions
      allUnions = unionsBeforeConstructor <> unionsInConstructor <> unionsAfterConstructor

      ret = mapTVs $ Fix $ T.TCon dd (Fix . T.TVar <$> tvs) allUnions

    -- liftIO $ do
    --   putStrLn "Fuck you"
    --   putStrLn $ ctx T.tUnions unionsBeforeConstructor
    --   putStrLn $ ctx T.tUnions unionsAfterConstructor
    --   putStrLn $ ctx T.tUnions unionsInConstructor


    -- unify unions in the declaration.
    --   important: how are unions ordered wrt. constructors.
    -- TODO: this is very bad. depends on arbitrary order. at least create a function that would take care of it??? or simply remove unions from declarations or just turn them into normal generics.

    -- first, unify current constructor


    -- then recreate the unions, but subst
    let emptyEnv = T.Env envID []
    union <- mkUnion emptyEnv

    pure $ Fix $ T.TFun union tsWithClonedUnions ret

mapTVsWithMap :: Map TVar T.Type -> T.Type -> T.Type
mapTVsWithMap tvmap =
  let
    mapTVs :: T.Type -> T.Type
    mapTVs = cata $ (.) embed $ \case
      t@(T.TVar tv) -> maybe t project (tvmap !? tv)
      t -> t
  in mapTVs


mkUnion :: T.Env -> Infer T.EnvUnion
mkUnion env = do
  uid <- newUnionID
  pure T.EnvUnion { T.unionID = uid, T.union = [env] }

uni :: T.Type -> T.Type -> Infer ()
uni t1 t2 = do
  -- liftIO $ putStrLn $ printf "%s :: %s" (ctx T.tType t1) (ctx T.tType t2)

  substituting $ do
    su <- RWS.get
    let (t1', t2') = subst su (t1, t2)
    unify t1' t2'

  -- liftIO . putStrLn . dbgSubst =<< RWS.gets typeSubstitution

  -- HACK: Doing it this way simplifies the algorithm, but it's not very parallelizable tho.
  -- TODO: Lookup cool unification algorithms?
  -- (su', errs) <- liftIO $ runWriterT $ composeLeft csu (t1, t2)
  -- RWS.modify $ \s -> s {su = su'}
  -- RWS.tell errs


-- A one way compose function
-- aaaaaa :: Subst -> (T.Type, T.Type) -> Errable Subst
-- aaaaaa su (t1, t2) = do
--   let (t1', t2') = subst su (t1, t2)
--   su' <- unify t1' t2'

--   pure $ composeLeft su' su

-- composeLeft :: Subst -> Subst -> Subst
-- composeLeft sl@(Subst lenv ltypes) sr@(Subst renv rtypes) = Subst
--   (Map.map (subst sl) renv `Map.union` Map.map (subst sr) lenv)
--   (Map.map (subst sl) rtypes `Map.union` ltypes)

-- lookupVar  :: UniqueVar -> Infer (Type TyVared)
-- lookupVar v = do
--   vars <- RWS.gets variables
--   case Map.lookup v vars of
--     Just t -> do
--       ty <- instantiate t
--       addEnv v ty
--       pure ty
--     Nothing -> do
--       -- Special case used for errors, but also not!
--       -- Function parameters need not create a scheme, thus we define variables without the whole scheme thing.
--       -- also, they are needed once referenced, so this simplifies it.
--       --    I thing I should change the names of those functions.
--       fresh

-- lookupCon :: UniqueCon -> Infer (Type TyVared)
-- lookupCon c = do
--   cons <- RWS.gets constructors
--   case Map.lookup c cons of
--     Just t ->
--       instantiate t
--     Nothing -> do
--       -- This means that the constructor does not exist. This is always an error (caught by the resolver).
--       t' <- fresh
--       let scheme = Forall Set.empty $ UTUnchanged t'
--       RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }
--       pure t'


-- -- when using a type, adds the usage (the tyvared types) to the environment type.
-- -- this makes it possible to know how many and which types were applied to the polymorphic functions.
-- addEnv :: UniqueVar -> Type TyVared -> Infer ()
-- addEnv v ty = RWS.modify $ \s -> s { env = fmap mapFunEnv s.env }
--   where
--     mapFunEnv :: [(UniqueVar, Type TyVared)] -> [(UniqueVar, Type TyVared)]
--     mapFunEnv = ((v, ty) :)

-- instantiate :: Scheme -> Infer (Type TyVared)
-- instantiate (Forall tvars ut) = do
--   -- Instantiate variables for TVars
--   let tvarsList = Set.toList tvars
--   freshlyMade <- traverse (const freshTyvar) tvarsList  -- make new tyvars (unpacked, used later)
--   let tvMapping = Map.fromList $ zip tvarsList freshlyMade  -- Make a TVar -> TyVar mapping


--   let mapTvs :: Base (Type TyVared) a -> Base (Type TyVared) a
--       mapTvs = \case
--         t@(Ty.TVar tv) -> (maybe t Ty.TyVar (Map.lookup tv tvMapping))
--         t -> t

--   ty <- instantiateType ut
--   pure $ hoist mapTvs ty

-- instantiateType :: Type Unstantiated -> Infer (Type TyVared)
-- instantiateType = \case
--   UTCon params ut ts unions -> do
--     unions' <- cloneUnion `traverse` unions
--     let unionMapping = Map.fromList $ zip unions unions'

--     let
--       findUnion :: EnvUnion TyVared -> EnvUnion TyVared
--       findUnion union = Map.findWithDefault union union unionMapping

--       mapTypeUnions :: Type TyVared -> Type TyVared
--       mapTypeUnions = cata $ embed . \case
--         Ty.TCon ut types unions ->
--           let unions' = findUnion <$> unions
--           in Ty.TCon ut types unions'

--         Ty.TFun union params ret -> Ty.TFun (findUnion union) params ret
--         Ty.TVar tv -> Ty.TVar tv
--         Ty.TyVar tv -> Ty.TyVar tv

--     t <- case params of
--           [] -> pure $ Fix $ Ty.TCon ut ts unions'
--           (_:_) -> do
--             funUnion <- singletonUnion =<< emptyEnv
--             let td = Fix $ Ty.TCon ut ts unions'
--             pure $ Fix $ Ty.TFun funUnion params td

--     pure $ mapTypeUnions t
--   UTFun env args ret -> do
--     union <- singletonUnion env
--     pure $ Fix $ Ty.TFun union args ret

--   UTyVar tyv -> pure $ Fix $ Ty.TyVar tyv
--   UTUnchanged t -> pure t

--   UTExternalVariable (Fix (T.TFun tunion params ret)) -> do
--     union <- reunion tunion
--     pure $ Fix $ Ty.TFun union (fmap t2ty params) (t2ty ret)

--   UTExternalVariable t -> pure $ t2ty t


-- -- Creates a new env union from an already typed module.
-- reunion :: EnvUnion Typed -> Infer (EnvUnion TyVared)
-- reunion union = pure $ t2ty <$> reunion' union -- Should I create a new ID?

-- reunion' :: T.EnvUnionF a -> Ty.EnvUnionF a
-- reunion' (T.EnvUnion uid envs) = Ty.EnvUnion uid $ fmap tenv2tyenv' envs

-- tenv2tyenv :: Env Typed -> Env TyVared
-- tenv2tyenv = fmap t2ty . tenv2tyenv'

-- tenv2tyenv' :: T.EnvF a -> Ty.EnvF a
-- tenv2tyenv' (T.Env eid vars) = Ty.Env eid vars


-- A scheme turns closed over TyVars into TVars. This requires it to traverse through the expression and replace appropriate vars.
-- We use Substitutable's subst function for this.
-- closeOver :: Substitutable a => Set TyVar -> a -> a
-- closeOver tyvars x = undefined
--   where
--     su = Subst mempty undefined
--     tvMap = Map.fromList $ map (\tyv -> (tyv, Fix $ T.TVar (TV (T.fromTyV tyv)))) $ Set.toList tyvars


-- maybe merge lookupVar and newVar,
--   because that's what the resolving step should... resolve.
var :: UniqueVar -> Infer T.Type
var v = do
  vars <- RWS.gets variables
  case vars !? v of
    Just t -> pure t
    Nothing -> do
      t <- fresh
      RWS.modify $ \s -> s { variables = Map.insert v t s.variables }
      pure t

-- newCon :: UniqueCon -> Scheme -> Infer ()
-- newCon c scheme = RWS.modify $ \s -> s { constructors = Map.insert c scheme s.constructors }

-- newType :: UniqueType -> [TVar] -> [EnvUnion TyVared] -> Infer ()
-- newType ti tvars unions =
--   let t = Ty.TypeCon ti (Fix . Ty.TVar <$> tvars) unions
--   in RWS.modify $ \s -> s { types = Map.insert ti t s.types }


-- Make a new env ID.
newEnvID :: Infer EnvID
newEnvID = EnvID <$> liftIO newUnique

-- Make new union ID.
newUnionID :: MonadIO io => io UnionID
newUnionID = UnionID <$> liftIO newUnique


-- Returns a fresh new tyvare
fresh :: Infer T.Type
fresh = Fix . T.TyVar <$> freshTyvar

-- freshUn :: Infer (Type Unstantiated)
-- freshUn = UTyVar <$> freshTyvar

-- Supplies the underlying tyvar without the structure. (I had to do it, it's used in one place, where I need a deconstructed tyvar)
freshTyvar :: Infer TyVar
freshTyvar = do
  TVG nextVar <- RWS.gets tvargen
  RWS.modify $ \s -> s { tvargen = TVG (nextVar + 1) }
  pure $ T.TyV $ letters !! nextVar

letters :: [Text]
letters = map (Text.pack . ('\'':)) $ [1..] >>= flip replicateM ['a'..'z']


findBuiltinType :: PreludeFind -> Infer T.Type
findBuiltinType (PF tc pf) = do
  Ctx { prelude = prelud } <- RWS.ask
  case prelud of
    Just p -> pure $ pf p
    Nothing -> do
      ts <- RWS.gets $ memoToMap . memoDataDefinition
      case findMap tc (\(R.DD ut _ _ _) -> ut.typeName) ts of
        Just dd@(T.DD _ tvs _ _) -> do
          itvs <- traverse (const fresh) tvs
          let tunions = extractUnionsFromDataType dd
          -- nocheckin: we also do union instantiation here
          unions <- cloneUnions tunions
          pure $ Fix $ T.TCon dd itvs unions
        Nothing -> error $ "[COMPILER ERROR]: Could not find inbuilt type '" <> show tc <> "'."

-- -- todo: after I finish, or earlier, maybe make sections for main logic, then put stuff like datatypes or utility functions at the bottom.
type Infer = RWST Context [TypeError] StatefulEnv IO  -- normal inference
type SubstCtx = RWST () [TypeError] Subst IO     -- substitution

data Context = Ctx
  { prelude :: Maybe Prelude
  , returnType :: Maybe T.Type
  }


substituting :: SubstCtx a -> Infer a
substituting subctx = RWST $ \_ s -> do
  (x, su, errs) <- RWS.runRWST subctx () s.typeSubstitution
  pure (x, s { typeSubstitution = su }, errs)

-- mkContext :: Maybe Prelude -> Context
-- mkContext Nothing = Ctx { prelude = Nothing, returnType = Nothing }
-- mkContext (Just prelud) = Ctx { prelude = Just prelud, returnType = Just (exprType prelud.toplevelReturn) }
--   where
--     exprType :: Expr Typed -> Type TyVared
--     exprType (Fix (T.ExprType t _)) = t2ty t


-- type Constraint = (Type TyVared, Type TyVared)

data StatefulEnv = StatefulEnv
  { tvargen :: TVarGen

  -- HACK: It's kinda weird that it's here.
  -- I prefer the writer guarantees, however, we have to report errors during composition.
  -- It's simpler like this right now.
  , typeSubstitution :: Subst

  , memoFunction :: Memo R.Function T.Function
  , memoDataDefinition :: Memo R.DataDef T.DataDef

  , variables :: Map UniqueVar T.Type

  -- HACK: track instantiations from environments. czy jest sens?
  , instantiations :: Set (T.Variable, T.Type)
  }
  -- { variables :: Map UniqueVar Scheme
  -- , constructors :: Map UniqueCon Scheme
  -- , types :: Map UniqueType Ty.TypeConstructor
  -- , tvargen :: TVarGen
  -- , env :: [[(UniqueVar, Type TyVared)]]
  -- }

emptySEnv :: StatefulEnv
emptySEnv = StatefulEnv
  { tvargen = newTVarGen
  , typeSubstitution = emptySubst

  , memoFunction = Memo mempty
  , memoDataDefinition = Memo mempty

  , variables = mempty

  , instantiations = mempty
  }
--   { variables = mempty
--   , constructors = mempty
--   , tvargen = newTVarGen
--   , types = mempty
--   , env = mempty
--   }


-- -- FUNNY!
-- -- Closes over tyvars - but this requires the env union to not be instantiated. So we can't put a normal type. How do we do it?
-- -- The thing is, for functions, we need to be able to modify definitions from imported files...
-- -- so, we might need to keep everything in tyvared state or to be able to update the EnvUnion
-- data Scheme = Forall (Set TVar) (Type Unstantiated)

-- -- THIS. A very funny type meants to be mapped to the normal TyVared variation after
-- data Unstantiated  -- name is retarded on purpose.
-- type instance Type Unstantiated = UnstantiatedType
-- data UnstantiatedType
--   = UTCon [Type TyVared] UniqueType [Type TyVared] [EnvUnion TyVared]
--   -- | UTVar TVar
--   | UTFun (Env TyVared) [Type TyVared] (Type TyVared)  -- this might be incorrect tho...
--   | UTyVar TyVar
--   | UTUnchanged (Type TyVared)  -- assignment etc. where the type is already "complete". kind of redundant, because it implies empty TVars...
--   | UTExternalVariable (Type Typed)  -- oh shid, we comin outta circus with this one. used for types outside of the module. why? imagine `x` in a base module with some environment. module A imports it and does this: `y = x if rand() else x: x + n` and module B does this: `z = x if rand() else x: x - m`. ------ two different environments. since we parse everything per-module, we have to keep track of the mapping.
--   deriving Show


-- instance Show Scheme where
--   show (Forall tvs ts) = show tvs <> ": " <> show ts


newtype TVarGen = TVG Int

newTVarGen :: TVarGen
newTVarGen = TVG 0


data Subst = Subst (Map UnionID T.EnvUnion) (Map TyVar T.Type)

emptySubst :: Subst
emptySubst = Subst mempty mempty

  -- undefined where
  --   rs = subst lsu $ first (Fix . T.TyVar) <$> Map.toList tysr
  --   rsu' = solve rs
  --   lsu' = subst rsu' lsu
  --   final = lsu' `Map.union` rsu'

  --   solve :: [(T.Type, T.Type)] -> Subst
  --   solve = undefined
  -- let r@(Subst envr tyr) = Subst (Map.map (subst sl) envsr) (Map.map (subst sl) tysr)
  --     (Subst envl tyl) = Subst (Map.map (subst r) envsl) (Map.map (subst r) tysl)
  --     final = Subst (envl `Map.union` envr) (tyl `Map.union` tyr)
  -- in final
  -- (Map.map (subst sl) envsr `Map.union` Map.map (subst sr) envsl)
  -- (Map.map (subst sl) tysr `Map.union` Map.map (subst sr) tysl)


-- -- base `finalize` on it - remove after.
-- -- Before, this function had a return type Either (NonEmpty TyVar) FullSubst
-- -- however, it's actually not needed.
-- -- during generalization, we substitute variables, but we don't add any constraints.
-- --   for example, in the function, if an argument is unused, two fresh vars are added unified.
-- --    this unification generates a constraint. substitutions are generated per generalization and during the last substitution. because this constraint exists, on the last substitution it generates a mapping 'a -> 'b, despite none of the tyvars being in the function... which generated the error.
-- -- finalizeSubst :: Subst -> FullSubst
-- -- finalizeSubst (Subst _ su) = flip Map.mapMaybe su $ transverse $ \case
-- --   _ -> Nothing
--   -- Ty.TyVar _ -> Nothing
--   -- Ty.TVar _ -> undefined

--   -- TF' (Right t) -> mapTypeEnv (\(TyFunEnv envid fe) -> TyFunEnv undefined fe) <$> sequenceA t
--   -- where
--     -- sesu = traverse $ transverse $ \case
--     --   TF' (Left tyv) -> undefined
--     --   TF' (Right t) -> mapTypeEnv (\(TyFunEnv _ fe) -> fe) <$> sequenceA t


-- ------------------------
-- -- CONSTRAINT SOLVING --
-- ------------------------

-- -- this one solves constraints for one part of the program
-- --  - needed for generalization
-- subSolve :: Substitutable a => Infer a -> Infer a
-- subSolve ctx = do
--   ogvars <- RWS.gets variables  -- variables outside of scope. we will remove them after they are solved. (types are not ambiguous if they "come from outside" of the part we are solving (function probably))

--   (x, constraints) <-  RWS.mapRWST (fmap (\(x, s, constraints) -> ((x, constraints), s { variables = ogvars }, constraints))) ctx
--   (_, sub) <- liftIO $ solveConstraints constraints  -- here, some ambigous variables might come out. we'll find them at the end, so ignore them right now, but we might save them later (in development) for performance.
--   let substituted = sub `subst` x

--   pure substituted


-- Constructs an environment from all the instantiations.
--  We need the instantiations, because not all instantiations of a function can come up in the environment.
--  But, when there is a TVar in the type, it means all instantiated types of TVars must be there.
withEnv' :: R.Env -> Infer a -> Infer ([(T.Variable, Locality, T.Type)], a)
withEnv' renv x = do

  -- 1. clear environment - we only collect things from this scope.
  outOfEnvInstantiations <- RWS.gets instantiations

  -- 2. execute in scope.
  RWS.modify $ \s -> s { instantiations = Set.empty }
  x' <- x
  modifiedInstantiations <- RWS.gets instantiations

  -- 3. then filter the stuff that actually is from the environment
  --  TODO: this might not be needed, since we conditionally add an instantiation if it's FromEnvironment.
  renvQuery <- Map.fromList <$> traverse (\(v, t) -> (,t) <$> inferVariable v) (R.fromEnv renv)
  let newEnv = mapMaybe (\(v, t) -> Map.lookup v renvQuery <&> (v,,t)) $ Set.toList modifiedInstantiations


  -- 4. and put that filtered stuff back.
  let usedInstantiations = Set.fromList $ fmap (\(v, _, t) -> (v, t)) newEnv
  RWS.modify $ \s -> s { instantiations = outOfEnvInstantiations <> usedInstantiations }

  pure (newEnv, x')

withEnv :: R.Env -> Infer a -> Infer (T.Env, a)
withEnv renv x = do
  (tenv, x') <- withEnv' renv x
  envID <- newEnvID
  pure (T.Env envID tenv, x')

addEnv :: T.Variable -> T.Type -> Infer ()
addEnv v t = RWS.modify $ \s -> s { instantiations = Set.insert (v, t) s.instantiations }

  -- RWS.modify $ \s -> s { env = [] : s.env }
  -- (e, x') <- RWS.mapRWST (fmap (\(x, s@StatefulEnv { env = (e:ogenvs) }, cs) -> ((e, x), s { env = ogenvs }, cs))) x  -- we're using tail, because we want an error if something happens.

--   -- remove things that are part of the inner environment (right now, just an intersection, because renv is already done in Resolver)
--   env <- emptyEnv
--   let renvVarMap = Map.fromList $ R.fromEnv renv
--   env <- emptyEnv
--   let outerEnv = env { Ty.env = mapMaybe (\(uv, t) -> (\l -> (uv, l, t)) <$> (renvVarMap !? uv)) e }

--   pure (outerEnv, x')

-- -- TODO: should probably change the name
-- -- renv2tyenv :: R.Env -> Infer (Env TyVared)
-- -- renv2tyenv (R.Env vars) = do
-- --   envID <- liftIO newUnique
-- --   envts <- traverse (\v -> (v,) <$> fresh) vars  -- TODO: i guess we don't need environemnts, since we have addEnv?
-- --   pure $ Ty.Env { Ty.envID = envID, Ty.env = envts }


-- newtype Solve a = Solve { unSolve :: WriterT [TypeError] IO a } deriving (Functor, Applicative, Monad, MonadIO)

data TypeError
  = InfiniteType TyVar T.Type
  | TypeMismatch T.Type T.Type
  | MismatchingNumberOfParameters [T.Type] [T.Type]
  | AmbiguousType TyVar

-- not sure if we have to have a show instance
instance Show TypeError where
  show = \case
    InfiniteType tyv t -> unwords ["InfiniteType", ctx T.tTyVar tyv, ctx T.tType t]
    TypeMismatch t t' -> printf "Type Mismatch: %s %s" (ctx T.tType t) (ctx T.tType t')
    MismatchingNumberOfParameters ts ts' -> printf "Mismatching number of parameters: (%d) %s (%d) %s" (length ts) (show $ ctx T.tType <$> ts) (length ts') (show $ ctx T.tType <$> ts')
    AmbiguousType tyv -> printf "Ambiguous type: %s" (ctx T.tTyVar tyv)

-- -- Solve constraints and generate a substitution from those constraints.
-- -- TODO: Why do we return a substitution and an error list?
-- --    TEMP: IO is temporary for generating unique values
-- solveConstraints :: [Constraint] -> IO ([TypeError], Subst)
-- solveConstraints = fmap swap . runWriterT . unSolve . solve emptySubst
--   where
--     solve :: Subst -> [Constraint] -> Solve Subst
--     solve su [] = pure su
--     solve su ((tl, tr):cs) = do
--       newsu <- unify tl tr
--       solve (newsu `compose` su) (subst newsu cs)

unify :: T.Type -> T.Type -> SubstCtx ()
unify ttl ttr = do
  su <- RWS.get
  let (tl, tr) = subst su (ttl, ttr)
  case bimap project project $ subst su (tl, tr) of
    (l, r) | l == r -> pure ()
    (T.TyVar tyv, _) -> tyv `bind` tr
    (_, T.TyVar tyv) -> tyv `bind` tl
    (T.TFun lenv lps lr, T.TFun renv rps rr) -> do
      unifyMany lps rps
      unify lr rr
      lenv `unifyFunEnv` renv

    (T.TCon t ta unions, T.TCon t' ta' unions') | t == t' -> do
      unifyMany ta ta'
      zipWithM_ unifyFunEnv unions unions'

    (_, _) -> do
      err $ TypeMismatch tl tr

unifyMany :: [T.Type] -> [T.Type] -> SubstCtx ()
unifyMany [] [] = nun
unifyMany (tl:ls) (tr:rs) | length ls == length rs = do  -- quick fix - we don't need recursion here.
  unify tl tr
  unifyMany ls rs

unifyMany tl tr = err $ MismatchingNumberOfParameters tl tr

bind :: TyVar -> T.Type -> SubstCtx ()
bind tyv (Fix (T.TyVar tyv')) | tyv == tyv' = nun
bind tyv t | occursCheck tyv t =
              err $ InfiniteType tyv t
           | otherwise = do
  RWS.modify $ \su ->
    let singleSubst  = Subst mempty (Map.singleton tyv t)
        Subst unions types = subst singleSubst su
    in Subst unions (Map.insert tyv t types)

unifyFunEnv :: T.EnvUnion -> T.EnvUnion -> SubstCtx ()
unifyFunEnv lenv@(T.EnvUnion { T.unionID = lid }) renv@(T.EnvUnion { T.unionID = rid }) = do
  unionID <- newUnionID
  let env = T.EnvUnion { T.unionID = unionID, T.union = funEnv }

  RWS.modify $ \su ->
    let unionSubst = Subst (Map.fromList [(lid, env), (rid, env)]) Map.empty -- i don't think we need an occurs check. BUG: we actually do, nigga.
        Subst unions ts = subst unionSubst su  -- NOTE: technically, we don't even need to add this mapping to our global Subst, but then we would have to create a new fresh variable every time a new variable is created, or something similar (more error prone, so maybe not worth it.).
    in Subst (Map.insert rid env $ Map.insert lid env unions) ts
  --       traceShow ("ENVUNI: " <> show lenv <> "|||||" <> show renv <> "8=====>" <> show env <> "\n") $ 
  where
    union2envset = Set.fromList . (\(T.EnvUnion { T.union = union }) -> union)
    envset2union = Set.toList
    funEnv = envset2union $ union2envset lenv <> union2envset renv

occursCheck :: Substitutable a => TyVar -> a -> Bool
occursCheck tyv t = tyv `Set.member` ftv t

err :: TypeError -> SubstCtx ()
err te = RWS.tell [te]

-- Sikanokonokonokokośtantan
nun :: SubstCtx ()
nun = pure ()



-- -- this is correct when it comes to typing, but requires me to use applicative shit everywhere. kinda cringe.
-- type Res = Result (NonEmpty TyVar)
-- finalize :: Module TyVared -> Either (NonEmpty TyVar) (Module Typed)
-- finalize (Ty.Mod tystmts) = fmap T.Mod $ fromResult $ traverse annStmt tystmts where
--   annStmt :: AnnStmt TyVared -> Res (AnnStmt Typed)
--   annStmt = transverse $ \(Ty.AnnStmt anns stmt) ->
--     fmap (T.AnnStmt anns) $ case first fExpr stmt of
--       Ty.Pass -> pure T.Pass
--       Ty.Print expr -> T.Print <$> expr
--       Ty.Assignment uv e -> T.Assignment uv <$> e
--       Ty.MutDefinition uv e -> T.MutDefinition uv <$> bitraverse fType id e
--       Ty.MutAssignment uv e -> T.MutAssignment uv <$> e

--       Ty.If cond ifTrue elseIfs melse -> T.If <$> cond <*> sequenceA ifTrue <*> traverse (bitraverse id sequenceA) elseIfs <*> traverse sequenceA melse
--       Ty.Switch switch cases -> T.Switch <$> switch <*> traverse fCase cases
--       Ty.ExprStmt e -> T.ExprStmt <$> e
--       Ty.Return me -> T.Return <$> me

--       Ty.DataDefinition dd -> T.DataDefinition <$> fDataDef dd
--       Ty.FunctionDefinition fd body -> T.FunctionDefinition <$> fFunDec fd <*> sequenceA body

--   fCase :: Ty.Case (Res (Expr Typed)) (Res a) -> Res (T.Case (Expr Typed) a)
--   fCase Ty.Case { Ty.deconstruction = decon, Ty.caseCondition = caseCond, Ty.body = body } =
--     T.Case <$> fDecon decon <*> sequenceA caseCond <*> sequenceA body

--   fDecon :: Decon TyVared -> Res (Decon Typed)
--   fDecon = transverse $ \case
--     Ty.CaseVariable ty uv -> T.CaseVariable <$> fType ty <*> pure uv
--     Ty.CaseConstructor ty uc args -> T.CaseConstructor <$> fType ty <*> pure uc <*> sequenceA args

--   fExpr :: Expr TyVared -> Res (Expr Typed)
--   fExpr = transverse $ \(Ty.ExprType t e) -> T.ExprType <$> fType t <*> case e of
--     Ty.Lit l -> pure $ T.Lit l
--     Ty.Var l uv -> pure $ T.Var l uv
--     Ty.Con uc -> pure $ T.Con uc

--     Ty.Op l op r -> T.Op <$> l <*> pure op <*> r
--     Ty.Call c args -> T.Call <$> c <*> sequenceA args
--     Ty.As e t -> T.As <$> e <*> fType t
--     Ty.Lam env args ret -> T.Lam <$> fEnv env <*> traverse (\(uv, t) -> (uv,) <$> fType t) args <*> ret

--   fDataDef :: Ty.DataDef -> Res T.DataDef
--   fDataDef (Ty.DD ut tv unions cons) = T.DD ut tv <$> fEnvUnion `traverse` unions <*> traverse fDataCon cons

--   fDataCon :: Annotated Ty.DataCon -> Res (Annotated T.DataCon)
--   fDataCon (Annotated anns (Ty.DC uc tyv)) = Annotated anns . T.DC uc <$> traverse fType tyv

--   fFunDec :: Ty.FunDec -> Res T.FunDec
--   fFunDec (Ty.FD env uv params ret) = T.FD <$> fEnv env <*> pure uv <*> traverse (\(uv, t) -> (uv,) <$> fType t) params <*> fType ret

--   fType :: Type TyVared -> Res (Type Typed)
--   fType = transverse $ \case
--     Ty.TyVar tyv -> Failure $ NonEmpty.singleton tyv
--     Ty.TCon ut ts union -> T.TCon ut <$> sequenceA ts <*> fEnvUnion' `traverse` union
--     Ty.TVar tv -> pure $ T.TVar tv
--     Ty.TFun union args ret -> T.TFun <$> fEnvUnion' union <*> sequenceA args <*> ret where

--   fEnvUnion :: EnvUnion TyVared -> Res (EnvUnion Typed)
--   fEnvUnion = fEnvUnion' . fmap fType

--   fEnvUnion' (Ty.EnvUnion unionID envs) = case envs of
--     -- Union is empty in this case for example:
--     -- f (ff () -> a)  # only the specified type is present without any implied environment,
--     --   pass
--     [] -> pure $ T.EnvUnion unionID []
--     (e:es) -> T.EnvUnion unionID <$> traverse fEnv' (e : es)
--       where fEnv'(Ty.Env envid ets) = T.Env envid <$> traverse (\(v, loc, t) -> (,,) v loc <$> t) ets

--   fEnv :: Env TyVared -> Res (Env Typed)
--   fEnv (Ty.Env envid ets) = T.Env envid <$> (traverse . (\f (v, loc, t) -> (,,) v loc <$> f t)) fType ets


-- tyvar :: TyVar -> Type TyVared
-- tyvar = Fix . Ty.TyVar

-- tycon2type :: Ty.TypeConstructor -> Type TyVared
-- tycon2type (Ty.TypeCon uid tys unions) = Fix $ Ty.TCon uid tys unions


-------------------
-- Substitutable --
-------------------

class Substitutable a where
  ftv :: a -> Set TyVar
  subst :: Subst -> a -> a


instance Substitutable Subst where
  ftv (Subst unions types) = ftv (Map.elems unions) <> Map.keysSet types <> ftv (Map.elems types)
  subst su (Subst unions types) = Subst (Map.map (subst su) unions) (Map.map (subst su) types)

instance Substitutable T.Module  where
  -- TODO: We're not yet ftv-ing Datatypes, because it might lead to loops. Same with functions. I'll probably need another memoization system.
  ftv m = ftv m.toplevelStatements <> ftv m.functions -- <> ftv m.datatypes
  subst su m = T.Mod
    { T.toplevelStatements = subst su <$> m.toplevelStatements
    , T.exports = subst su m.exports

    , T.functions = subst su <$> m.functions
    , T.datatypes = m.datatypes -- subst su <$> m.datatypes
    }

instance Substitutable T.Exports where
  ftv e = ftv e.functions
  subst su e = e { T.functions = subst su e.functions }

instance Substitutable T.AnnStmt where
  ftv = cata $ \(O (Annotated _ stmt)) -> bifold $ first ftv stmt

  subst su = cata $ embed . sub
    where
      sub (O (Annotated ann stmt)) = O . Annotated ann $ case stmt of
        T.Switch cond cases ->
          let cond' = subst su cond
              cases' = subst su cases
          in T.Switch cond' cases'
        T.EnvDef env -> T.EnvDef $ subst su env
        s -> first (subst su) s

instance (Substitutable expr, Substitutable stmt) => Substitutable (T.Case expr stmt) where
  ftv kase = ftv kase.deconstruction <> ftv kase.caseCondition <> ftv kase.body
  subst su kase = T.Case (subst su kase.deconstruction) (subst su kase.caseCondition) (subst su kase.body)

instance Substitutable (Fix T.DeconF) where
  ftv = cata $ \case
    T.CaseVariable t _ -> ftv t
    T.CaseConstructor t _ ftvs -> ftv t <> mconcat ftvs
  subst su = hoist $ \case
    T.CaseVariable t v -> T.CaseVariable (subst su t) v
    T.CaseConstructor t uc ds -> T.CaseConstructor (subst su t) uc ds

instance Substitutable (Fix T.TypedExpr) where
  ftv = cata $ \(T.TypedExpr et ee) -> ftv et <> case ee of
    T.As e t -> e <> ftv t
    T.Lam env params body -> ftv env <> ftv params <> body
    e -> fold e
  subst su = hoist $ \(T.TypedExpr et ee) -> T.TypedExpr (subst su et) (case ee of
    T.As e t -> T.As e (subst su t)
    T.Lam env params body -> T.Lam (subst su env) (subst su params) body
    T.Var loc v -> T.Var loc $ subst su v
    e -> e)

instance Substitutable T.Variable where
  ftv _ = mempty
  subst su (T.DefinedFunction fn) = T.DefinedFunction $ subst su fn
  subst _ x = x


instance Substitutable UniqueVar where
  ftv _ = mempty
  subst _ = id



instance Substitutable T.Function where
  ftv fn = ftv fn.functionBody \\ ftv fn.functionDeclaration
  subst su fn = T.Function { T.functionDeclaration = subst su fn.functionDeclaration, T.functionBody = subst su fn.functionBody }

instance Substitutable T.FunDec where
  ftv (T.FD _ _ params ret) = ftv params <> ftv ret -- <> ftv env  -- TODO: env ignored here, because we expect these variables to be defined outside. If it's undefined, it'll come up in ftv from the function body. 
  subst su (T.FD env fid params ret) = T.FD (subst su env) fid (subst su params) (subst su ret)

-- -- here we treat the type as if it was a normal type
-- instance Substitutable UnstantiatedType where
--   ftv = \case
--     UTyVar tyv -> Set.singleton tyv

--     UTCon params _ apps unions -> ftv params <> ftv apps <> ftv unions
--     UTFun env params ret -> ftv env <> ftv params <> ftv ret  -- ???
--     UTExternalVariable _ -> mempty
--     UTUnchanged t -> ftv t
--   subst = error "Should not be called."


instance Substitutable (Fix T.TypeF) where
  ftv = cata $ \case
    T.TyVar tyv -> Set.singleton tyv
    t -> fold t

  subst su@(Subst _ tyvm) = cata $ embed . \case
    T.TyVar tyv -> case tyvm !? tyv of
        Nothing -> T.TyVar tyv
        Just t -> project t

    -- we might need to substitute the union thing
    T.TFun ogUnion ts t ->

      -- might need to replace the union
      let union = subst su ogUnion

      in T.TFun union ts t

    T.TCon ut cons unions -> T.TCon ut cons (subst su unions)

    t -> t

instance Substitutable (T.EnvUnionF (Fix T.TypeF)) where
  ftv (T.EnvUnion _ envs) = ftv envs
  subst su@(Subst unions _) (T.EnvUnion uid envs) = do
    case unions !? uid of
      Just suUnion -> suUnion
      Nothing -> T.EnvUnion uid $ subst su envs

instance Substitutable (T.EnvF (Fix T.TypeF)) where
  ftv (T.Env _ _) = mempty  -- TODO: why is this `mempty`?
  ftv (T.RecursiveEnv _ _) = mempty

  -- redundant work. memoize this shit also.
  subst su (T.Env eid env) = T.Env eid ((\(v, l, t) -> (subst su v, l, subst su t)) <$> env)
  subst su env = fmap (subst su) env


instance Substitutable a => Substitutable [a] where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance Substitutable a => Substitutable (NonEmpty a) where
  ftv = foldMap ftv
  subst su = fmap (subst su)

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  ftv = bifoldMap ftv ftv
  subst su = bimap (subst su) (subst su)

instance Substitutable a => Substitutable (Maybe a) where
  ftv = maybe mempty ftv
  subst su = fmap (subst su)

-- rt2ty :: Type Resolved -> Infer (Type TyVared)
-- rt2ty = cata (fmap embed . f)
--   where
--     f = \case
--       R.TCon t ts -> do
--         typez <- RWS.gets types
--         case typez !? t of
--           Nothing -> error $ "Could not find type " <> show t <> ". This is probably impossible?? Maybe???"
--           Just (Ty.TypeCon ut _tyvars unions) -> do
--             ts' <- sequenceA ts
--             pure $ Ty.TCon ut ts' unions


--       R.TVar tv -> pure $ Ty.TVar tv
--       R.TFun params ret -> do
--         params' <- sequenceA params
--         ret' <- ret
--         union <- emptyUnion
--         pure $ Ty.TFun union params' ret'

-- t2ty :: Type Typed -> Type TyVared
-- t2ty = hoist $ \case
--   T.TCon ut apps union -> Ty.TCon ut apps (reunion' <$> union)
--   T.TFun union args ret -> Ty.TFun (reunion' union) args ret
--   T.TVar tv -> Ty.TVar tv

extractUnionsFromDataType :: T.DataDef -> [T.EnvUnion]
extractUnionsFromDataType (T.DD _ _ dcs _) =
  concatMap extractUnionsFromConstructor dcs

extractUnionsFromConstructor :: T.DataCon -> [T.EnvUnion]
extractUnionsFromConstructor (T.DC (T.DD ut _ _ _) _ ts _) = concatMap (mapUnion ut) ts

-- Clones unions in a type.
--   Because we always use it in contexts where we know the type and we want to avoid infinite recursion,
--    `UniqueType` is provided to stop such recursion.
--  TODO: right now, we don't care if some union repeats. Is it even possible? Prove me wrong.
cloneUnionInType :: UniqueType -> T.Type -> Infer T.Type
cloneUnionInType baseUT = transverse $ \case
  T.TCon dd@(T.DD ut _ _ _) ts unions
    | ut == baseUT -> T.TCon dd <$> sequenceA ts <*> sequenceA2 unions
    | otherwise -> T.TCon dd <$> sequenceA ts <*> (cloneUnions =<< sequenceA2 unions)
  T.TFun union ts ret -> T.TFun <$> (cloneUnion =<< sequenceA union) <*> sequenceA ts <*> ret

  t -> sequenceA t

cloneUnions :: [T.EnvUnionF a] -> Infer [T.EnvUnionF a]
cloneUnions = traverse cloneUnion

cloneUnion :: T.EnvUnionF a -> Infer (T.EnvUnionF a)
cloneUnion union = do
  uid <- newUnionID
  pure $ union { T.unionID = uid }

-- Creates an empty union.
emptyUnion :: Infer T.EnvUnion
emptyUnion = do
  uid <- newUnionID
  pure $ T.EnvUnion uid []

newEmptyEnv :: Infer T.Env
newEmptyEnv = do
  envID <- newEnvID
  pure $ T.Env envID []

-- singletonUnion :: Env TyVared -> Infer (EnvUnion TyVared)
-- singletonUnion env = do
--   uid <- newUnionID
--   pure $ Ty.EnvUnion uid [env]

-- emptyEnv :: Infer (Env TyVared)
-- emptyEnv = do
--   uid <- newEnvID
--   pure $ Ty.Env uid []


-- bidmap :: Bifunctor p => (c -> d) -> p c c -> p d d
-- bidmap f = bimap f f


findMap :: Eq a => a -> (b -> a) -> Map b c -> Maybe c
findMap kk f = fmap snd . find (\(k, _) -> f k == kk). Map.toList


-- -----
-- -- DEBUG
-- ----

dbgSubst :: Subst -> String
dbgSubst (Subst unions ts) =
  let tvars = Map.toList ts <&> \(ty, t) -> printf "%s => %s" (ctx T.tTyVar ty) (ctx T.tType t)
      unionRels = Map.toList unions <&> \(uid, union) -> printf "%s => %s" (ctx ppUnionID uid) (ctx (T.tEnvUnion . fmap T.tType) union)
  in unlines $ tvars <> ["--"] <> unionRels

-- -- dbgTypecheck :: Maybe Prelude -> Module Resolved -> ([TypeError], Module Typed)
-- -- dbgTypecheck mprelude rStmts =
-- --     let env = topLevelEnv mprelude
-- --         senv = makeSEnv mprelude
-- --         -- Three phases
-- --         (tyStmts', constraints) = generateConstraints env senv rStmts
-- --         tyStmts =
-- --           traceWith tyModule
-- --           tyStmts'
-- --         (errors, su@(Subst _ tysu)) = solveConstraints
-- --           $ (traceWith dbgPrintConstraints)
-- --           constraints
-- --         ambiguousTyVars = ftv tyStmts \\ Map.keysSet tysu
-- --     in if (not . null) ambiguousTyVars
-- --           then
-- --             let ambiguousTyvarsErrors = AmbiguousType <$> Set.toList ambiguousTyVars
-- --                 errs = errors ++ ambiguousTyvarsErrors

-- --                 addMissing :: Set TyVar -> Subst -> Subst
-- --                 addMissing tyvs su =
-- --                   let tyvsu = Map.fromList $ (\tyv@(TyVar tyvName) -> (tyv, makeType (TVar (TV tyvName)))) <$> Set.toList tyvs
-- --                       tyvarSubst = Subst Map.empty
-- --                   in tyvarSubst tyvsu `compose` su

-- --                 su' = addMissing ambiguousTyVars su
-- --                 fsu = finalizeSubst su'
-- --                 tstmts = substituteTypes fsu tyStmts
-- --             in (errs, tstmts)
-- --           else
-- --             let fsu = finalizeSubst su
-- --                 tstmts = substituteTypes fsu tyStmts
-- --             in (errors, tstmts)



-- -- dbgPrintConstraints :: [Constraint] -> String
-- -- dbgPrintConstraints = unlines . fmap pc
-- --   where
-- --     pc (tl, tr) = dbgt tl <> " <=> " <> dbgt tr

-- -- dbgt :: Type TyVared -> String
-- -- dbgt = undefined
-- -- dbgt = cata $ \(TF' t) -> case t of
-- --   Left tyv -> "#" <> show tyv
-- --   Right rt -> cloneUnionInTypee rt of
-- --     TCon ti cloneUnionInType-> "(" <> show ti <> unwords apps <> ")"
-- --     TFun env args ret -> dbgenv env <> "(" <> intercalate ", " args <> ") -> " <> ret
-- --     TVar tv -> show tv

-- -- dbgenv :: TyFunEnv' String -> String
-- -- dbgenv (TyFunEnv envid (FunEnv fe)) = "#" <> show envid <> "[" <> unwords (fmap (\env -> "[" <> intercalate ", " (fmap (\(v, t) -> show v <> " " <> ("[" <> unwords sequenceA2 unions <> "]")) env) <> "]") fe) <> 


sequenceA2 = traverse sequenceA
