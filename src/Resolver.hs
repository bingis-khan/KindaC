{-# LANGUAGE LambdaCase, OverloadedRecordDot, DuplicateRecordFields, RecursiveDo #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-ambiguous-fields #-}
{-# HLINT ignore "Use concatMap" #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
module Resolver (resolve, ResolveError) where

import Data.Unique (newUnique)
import Control.Monad.IO.Class (liftIO)
import Data.Functor.Foldable (transverse, cata, embed, project)
import Data.Foldable (fold, for_)
import Control.Monad.Trans.RWS (RWST)
import Data.Map (Map, (!?))
import qualified Control.Monad.Trans.RWS as RWST
import qualified Data.Map as Map

import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Control.Applicative ((<|>))
import Data.Set (Set, (\\))
import Data.Bifoldable (bifold)
import qualified Data.Set as Set

import AST.Common
-- import AST.Converged (Prelude(..))
import qualified AST.Prelude as Prelude
import AST.Untyped (U, Qualified (..))
import qualified AST.Untyped as U
import AST.Resolved
import qualified AST.Resolved as R
import qualified AST.Typed (Mod(..))
import Data.Fix (Fix(..))
import Data.Functor ((<&>))
import Data.Biapplicative (first)
import qualified Data.Text as Text
import Data.Maybe (mapMaybe)
import Data.Semigroup (sconcat)
import Data.Traversable (for)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Either (rights, lefts)
import Data.List (find)
import AST.Def (type (:.)(O), Annotated (..), Binding (..), Located (..), pp)
import qualified AST.Def as Def
import qualified AST.Common as Common
import AST.Prelude (Prelude (..))
import Control.Monad ( when, foldM, void )
import AST.Typed (TC, functionAnnotations)
import CompilerContext (CompilerContext)
import qualified CompilerContext as Compiler
import Control.Monad.Trans.Class (lift)
import Error (Error (..), renderError)
import Text.Printf (printf)
import Data.String (fromString)
import Data.Text (Text)



-- Resolves variables, constructors and types and replaces them with unique IDs.
resolve :: Maybe Prelude -> Compiler.ModuleLoader -> Module U -> CompilerContext ([ResolveError], Module R)
resolve mPrelude moduleLoader (U.Mod ustmts) = do
  let newState = maybe emptyState (mkState moduleLoader) mPrelude
  (rstmts, state, errs) <- RWST.runRWST (rStmts ustmts) mPrelude newState

  let topLevelScope = NonEmpty.head state.scopes
  let moduleExports = scopeToExports topLevelScope

  let rmod = R.Mod { toplevel = rstmts, exports = moduleExports, allFunctions = state.functions, allDatatypes = state.datatypes, allClasses = state.classes, allInstances = state.instances }

  return (errs, rmod)


rStmts :: [AnnStmt U] -> Ctx [AnnStmt R]
rStmts = traverse -- traverse through the list with Ctx
  rStmt' -- go through Stmt recursively with Ctx. cata (fmap embed . ...) is transverse without the forall type.
  where
    rStmt' = cata (fmap embed . (\(O (O utStmt)) -> O . O <$> rStmt utStmt))
    -- actual logic
    -- maybe try to generalize it if possible using traverse n shit
    rStmt (Annotated anns (Located location uStmt)) =
      let stmt = pure . Annotated anns . Located location
          pass = pure $ Annotated [] $ Located location Pass
      in case uStmt of
      Print e -> do
        re <- rExpr e
        stmt $ Print re
      Assignment name location e -> do
        re <- rExpr e
        vid <- newVar name
        stmt $ Assignment vid location re
      Pass -> stmt Pass
      Mutation name varLocation () accesses e -> do
        re <- rExpr e
        let raccesses = flip map accesses $ \case  -- noop to map "phase"
              MutRef location -> MutRef location
              MutField location mem -> MutField location mem
        (loc, vf) <- resolveVar varLocation (U.unqualified name)

        case vf of
          -- LOCAL VAR
          R.DefinedVariable vid | loc == Def.Local ->
            stmt $ Mutation vid varLocation loc raccesses re

          -- when we're using a ref, we're actually mutating outside shit, so it's good.
          R.DefinedVariable vid | any (\case { MutRef {} -> True; _ -> False }) raccesses -> do
            stmt $ Mutation vid varLocation loc raccesses re

          R.DefinedVariable vid -> do
            err $ CannotMutateNonLocalVariable location name
            stmt $ Mutation vid varLocation loc raccesses re


          -- IMPORTED VAR (basically a copy!)
          -- NOTE TODO: RIGHT NOW I WON'T ALLOW MUTATING EXTERNAL VARIABLES DUE TO THE ARCHITECTURE AND MY OWN OPINION. THIS MIGHT (WILL PROBABLY) CHANGE IN THE FUTURE.
          R.ExternalVariable vid _ -> do
            err $ CannotMutateImportedVariable location vid
            stmt Pass


          R.DefinedFunction fun _ -> do
            err $ CannotMutateFunctionDeclaration location fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ Mutation vid varLocation loc [] re

          R.ExternalFunction fun _ -> do
            err $ CannotMutateFunctionDeclaration location fun.functionDeclaration.functionId.varName

            vid <- generateVar name
            stmt $ Mutation vid varLocation loc [] re

          R.DefinedClassFunction (CFD _ cfdUV _ _ _ _) _ -> do
            err $ CannotMutateFunctionDeclaration location cfdUV.varName

            vid <- generateVar name
            stmt $ Mutation vid varLocation loc [] re

          R.ExternalClassFunction (CFD _ cfdUV _ _ _ _) _ -> do
            err $ CannotMutateFunctionDeclaration location cfdUV.varName

            vid <- generateVar name
            stmt $ Mutation vid varLocation loc [] re


      If (IfStmt { condition, ifTrue, ifElifs, ifElse }) -> do
        rcond <- rExpr condition
        rIfTrue <- scope $ sequenceA ifTrue
        rElseIfs <- traverse (\(c, b) -> do
          rc <- rExpr c
          tb <- rBody b
          pure (rc, tb)) ifElifs
        rElseBody <- traverse rBody ifElse
        stmt $ If $ IfStmt rcond rIfTrue rElseIfs rElseBody
      Switch switch cases -> do
        rswitch <- rExpr switch
        rcases <- traverse rCase cases
        stmt $ Switch rswitch rcases
      ExprStmt e -> do
        re <- rExpr e
        stmt $ ExprStmt re
      Return _ | Def.AUndefinedReturn `elem` anns -> do  -- RETARDED HACK
        let vn = Def.VN "cock cock cock cock cock"
        uv <- newVar vn
        stmt $ Return $ Fix $ N location $ Var (R.DefinedVariable uv) Def.Local
      Return e -> do
        mre <- traverse rExpr e
        re <- case mre of
          Just re -> pure re
          Nothing -> do
            uc <- unit
            eid <- newEnvID
            pure $ Fix $ N location (Con uc eid)

        stmt $ Return re

      While cond bod -> do
        rcond <- rExpr cond
        rbod <- scope $ sequenceA bod
        stmt $ While rcond rbod

      Other (U.UseStmt use) -> do
        mtmod <- tryLoadModule use.moduleQualifier
        case mtmod of
          Just tmod -> do
            useModule use.moduleQualifier tmod  -- import module itself.
            quietlyAddInstancesFromImportedModule tmod

            let
              findExport :: (Exports TC -> [a]) -> (a -> Bool) -> Maybe a
              findExport selectorFn filterFn = find filterFn $ selectorFn tmod.exports

            for_ use.items $ \case
              U.UseVarOrFun vn -> do
                let mv = findExport variables ((==vn) . Def.varName . fst)
                v <- case mv of
                      Just (uv, t) -> pure $ PExternalVariable uv t
                      Nothing -> do
                        let mfn = findExport Common.functions ((==vn) . Def.varName . functionId . functionDeclaration)
                        case mfn of
                          Just fn -> pure $ PExternalFunction fn
                          Nothing -> do
                            err $ ModuleDoesNotExportVariable location vn use.moduleQualifier
                            PDefinedVariable <$> generateVar vn

                modifyThisScope $ \sc -> sc { varScope = Map.insert vn v sc.varScope }

              U.UseType tc usedCons -> do
                (dd, cons) <- case findExport Common.datatypes ((==tc) . Def.typeName . ddName) of
                  Just dd@(DD ut _ (Right tcons) _) -> do
                    let
                      importedCons = Set.fromList $ NonEmpty.toList usedCons  -- set of used cons
                      cons = Map.fromList $ (\dc -> (dc.conID.conName, R.ExternalConstructor dc)) <$> filter ((`Set.member` importedCons) . Def.conName . conID) tcons  -- filter used cons and construct a con Map.

                    -- check if any of the cons were not imported (and error 'em)
                    for_ (importedCons \\ Map.keysSet cons) $ \importedButNonExistingCon ->
                      err $ TryingToImportNonExistingConstructorOfType location importedButNonExistingCon ut use.moduleQualifier

                    pure (ExternalDatatype dd, cons)

                  -- error paths
                  Just dd@(DD ut _ (Left _) _) -> do
                    err $ TryingToImportConstructorsFromARecordType location ut use.moduleQualifier

                    -- placeholders
                    cons <- fmap (Map.fromList . NonEmpty.toList) $ for usedCons $ \cn -> (cn,) <$> placeholderCon cn
                    pure (ExternalDatatype dd, cons)

                  Nothing -> do
                    err $ ModuleDoesNotExportType location tc use.moduleQualifier

                    -- placeholders
                    dd <- placeholderType tc
                    cons <- fmap (Map.fromList . NonEmpty.toList) $ for usedCons $ \cn -> (cn,) <$> placeholderCon cn
                    pure (dd, cons)

                modifyThisScope $ \sc -> sc
                  { tyScope = Map.insert tc (Right dd) sc.tyScope
                  , conScope = cons <> sc.conScope
                  }

              U.UseClass cn usedClassFuns -> do
                let mclass = findExport Common.classes ((==cn) . Def.className . classID)
                (klass, cfns) <- case mclass of
                  Just klass -> do
                    let
                      importedClassFuns = Set.fromList $ NonEmpty.toList usedClassFuns
                      cfns = Map.fromList $ (\cfn@(CFD _ cfnId _ _ _ _) -> (cfnId.varName, R.PExternalClassFunction cfn)) <$> filter (\(CFD _ funId _ _ _ _) -> funId.varName `Set.member` importedClassFuns) klass.classFunctions  -- filter used cons and construct a con Map.

                    -- check if any of the cons were not imported (and error 'em)
                    for_ (importedClassFuns \\ Map.keysSet cfns) $ \importedButNonExistingCFN ->
                      err $ TryingToImportNonExistingFunctionOfClass location importedButNonExistingCFN klass.classID use.moduleQualifier

                    pure (ExternalClass klass, cfns)

                  Nothing -> do
                    klass <- placeholderClass cn
                    err $ ModuleDoesNotExportClass location ((Def.className . R.asUniqueClass) klass) use.moduleQualifier

                    cfns <- fmap (Map.fromList . NonEmpty.toList) $ for usedClassFuns $ \cvn -> do
                      uv <- placeholderVar cvn
                      pure (cvn, PDefinedVariable uv)
                    pure (klass, cfns)

                modifyThisScope $ \sc -> sc
                  { tyScope = Map.insert ((Def.uniqueClassAsTypeName . R.asUniqueClass) klass) (Left klass) sc.tyScope
                  , varScope = cfns <> sc.varScope
                  }

              U.UseTypeOrClass tncn -> do
                -- try find datatype
                typeOrClass <- case findExport Common.datatypes ((==tncn) . Def.typeName . ddName) of
                  Just dd ->
                    pure $ Right $ ExternalDatatype dd

                  -- if not, try find class
                  Nothing -> case findExport Common.classes ((==tncn) . Def.uniqueClassAsTypeName . classID) of
                    Just klass ->
                      pure $ Left $ ExternalClass klass

                    Nothing -> do
                      err $ ModuleDoesNotExportTypeOrClass location tncn use.moduleQualifier
                      Right <$> placeholderType tncn

                modifyThisScope $ \sc -> sc
                  { tyScope = Map.insert tncn typeOrClass sc.tyScope
                  }


          Nothing ->
            for_ use.items $ \case
              -- This is probably bad... (the errors will be funny)
              U.UseVarOrFun varName ->
                void $ newVar varName
              U.UseType tc cons -> do  -- TODO: complete later
                undefined
              U.UseClass cn cfns -> undefined
              U.UseTypeOrClass cn -> do
                DefinedDatatype dd <- placeholderType cn
                registerDatatype dd

        stmt Pass

      Other (U.DataDefinition dd) -> mdo
        tid <- generateType dd.ddName
        -- tying the knot for the datatype definition

        let dataDef = DD tid tvars rCons anns
        registerDatatype dataDef


        let tvars = mkTVars (Def.BindByType tid) dd.ddScheme
        rCons <- bindTVars ((location,) <$> tvars) $ case dd.ddCons of
          Right cons ->
            fmap Right $ for cons $ \(DC () cname ctys conAnns) -> do
              cid <- generateCon cname

              -- TODO: throw an error if there is more than one constructor with the same name in the same datatype.
              -- TODO: also, can we redeclare constructors (in another datatype in the same scope?)
              rConTys <- traverse rType ctys
              let rCon = DC dataDef cid rConTys conAnns
              newCon rCon

              pure rCon

          Left recs ->
            fmap Left $ for recs $ \(Annotated recAnns (mem, t)) -> do
              t' <- rType t
              pure $ Annotated recAnns (mem, t')

        pass

      -- TODO: THIS IS ALL TEMPORARY - I SHOULD PROBABLY MAKE DIFFERENT DATA STRUCTURES FOR THIS!
      --  CURRENTLY, YOU MAY NOT USE EXTERNAL FUNCTIONS ALONGSIDE OTHER FUNCTIONS. SHIT WILL BREAK. THIS IS A QUICK HACK.
      Other (U.ExternalFunctionDeclaration (FD () name params ret (uconstraints, headerLocation))) -> do
        vid <- generateVar name
        constraints <- rConstraints uconstraints
        -- get all unbound tvars
        let allTypes = catNotDeclared $ ret : (snd <$> params)
        tvars <- fmap mconcat $ for allTypes $ cata $ \case
              TO utv -> tryResolveTVar utv <&> \case
                Just _ ->  Set.empty  -- don't rebind existing tvars. (scoped tvars. but maybe a function declaration should rebind them.)
                Nothing -> Set.singleton $ bindTVar (defaultEmpty utv constraints) (BindByVar vid) utv
              t -> fold <$> sequenceA t

        eid <- newEnvID
        (rparams, rret) <- bindTVars ((headerLocation,) <$> Set.toList tvars) $ closure eid $ do
          rparams' <- traverse (\(n, t) -> do
            rn <- rDecon n
            rt <- rDeclaredType t
            return (rn, rt)) params
          rret' <- rDeclaredType ret
          pure (rparams', rret')

        -- set the environment
        --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
        -- TODO: maybe just make it a part of 'closure'?
        env <- mkEnv eid mempty

        newFunction $ Function (FD env vid rparams rret (Def.AExternal : anns, headerLocation)) $ NonEmpty.singleton $ Fix $ O $ O $ Annotated [] $ Located location Pass
        stmt Pass

      Fun (U.FunDef (FD () name params ret (uconstraints, headerLocation)) body) -> do
        vid <- generateVar name  -- NOTE: this is added to scope in `newFunction` (for some reason.) TODO: change it later (after I finish implementing records.) TODO: to what?????

        constraints <- rConstraints uconstraints

        -- get all unbound tvars
        let allTypes = catNotDeclared $ ret : (snd <$> params)
        tvars <- fmap mconcat $ for allTypes $ cata $ \case
              TO utv -> tryResolveTVar utv <&> \case
                Just _ ->  Set.empty  -- don't rebind existing tvars. (scoped tvars. but maybe a function declaration should rebind them.)
                Nothing -> Set.singleton $ bindTVar (defaultEmpty utv constraints) (BindByVar vid) utv
              t -> fold <$> sequenceA t

        rec
          let function = Function (FD env vid rparams rret (anns, headerLocation)) rbody
          newFunction function

          eid <- newEnvID
          (rparams, rret, rbody) <- bindTVars ((headerLocation,) <$> Set.toList tvars) $ closure eid $ do
            rparams' <- traverse (\(n, t) -> do
              rn <- rDecon n
              rt <- rDeclaredType t
              return (rn, rt)) params
            rret' <- rDeclaredType ret
            rbody' <- rBody $ rStmt' <$> body
            pure (rparams', rret', rbody')

          -- set the environment
          --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
          -- TODO: maybe just make it a part of 'closure'?
          let innerEnv = Map.delete (R.PDefinedVariable vid) $ sconcat $ gatherVariables <$> rbody
          env <- mkEnv eid innerEnv

        stmt $ Fun function

      -- REF: How are instances selected in Haskell: https://www.youtube.com/watch?v=XfIlhJFmw3c
      -- REF: https://wiki.haskell.org/index.php?title=Orphan_instance
      --  > Type class instances are special in that they don't have a name and cannot be imported explicitly. This also means that they cannot be excluded explicitly. All instances defined in a module A are imported automatically when importing A, or importing any module that imports A, directly or indirectly. 
      Other (U.ClassDefinition cd) -> do
        uc <- generateClass cd.classID

        -- scoped dependent types.
        rec
          let rcd = ClassDef
                { classID = uc
                -- , classDependentTypes = deps   -- TEMP remove
                , classFunctions = fundecs
                , classDeclarationLocation = cd.classDeclarationLocation
                }

          -- TODO: define dependent types... at least, later
          -- let _ = cd.classDependentTypes
          -- let deps = []

          fundecs <- for cd.classFunctions $ \(CFD () name params ret uconstraints classFunctionHeaderLocation) -> do
            funid <- generateVar name

            constraints <- rConstraints uconstraints

            -- get all unbound tvars (HACK: copied from DefinedFunction)
            let allTypes = ret : (snd <$> params)
            tvars <- fmap mconcat $ for allTypes $ cata $ \case
                  NormalType (TO utv) -> tryResolveTVar utv <&> \case
                    Just _ ->  Set.empty  -- don't rebind existing tvars.
                    Nothing -> Set.singleton $ R.bindTVar (defaultEmpty utv constraints) (BindByVar funid) utv
                  t -> fold <$> sequenceA t

            -- HACK: ALSO COPIED FROM DefinedFunction!!
            (rparams, rret) <- bindTVars ((cd.classDeclarationLocation,) <$> Set.toList tvars) $ do
              rparams' <- traverse (\(n, t) -> do
                rn <- rDecon n
                rt <- rClassType t
                return (rn, rt)) params
              rret' <- rClassType ret
              pure (rparams', rret')

            pure $ CFD rcd funid rparams rret () classFunctionHeaderLocation

          registerClass rcd
        pass


      Inst rinst -> mdo
        klass <- resolveClass location rinst.instClass

        klassType <- resolveType (error "location in types!") $ fst rinst.instType
        constraints <- rConstraints rinst.instConstraints

        let instTVars = map (\utv -> R.bindTVar (Def.defaultEmpty utv constraints) (BindByInst (R.asUniqueClass klass)) utv) $ snd rinst.instType

        -- constraints <- rConstraints klass (zip (snd rinst.instType) instTVars) rinst.instConstraints

        let inst = InstDef
              { instClass = klass
              , instType = (klassType, instTVars)
              , instConstraints = ()
              -- , R.instDependentTypes = []  -- TODO: temporary!
              , instFuns = fns
              }

        -- TEMP: should `registerInst` here, but I have a problem with recursive definitions.
        -- It also fixed the problem


        fns <- for rinst.instFuns $ \ifn -> do
          cfd <- findFunctionInClass (error "todo") ifn.instFunDec.functionId klass
          vid <- generateVar ifn.instFunDec.functionId

          constraints <- rConstraints $ fst ifn.instFunDec.functionOther

          -- get all unbound tvars
          let allTypes = catNotDeclared $ ifn.instFunDec.functionReturnType : (snd <$> ifn.instFunDec.functionParameters)
          tvars <- fmap mconcat $ for allTypes $ cata $ \case
                TO utv -> tryResolveTVar utv <&> \case
                  Just _ ->  Set.empty  -- don't rebind existing tvars.
                  Nothing -> Set.singleton $ R.bindTVar (Def.defaultEmpty utv constraints) (BindByVar vid) utv
                t -> fold <$> sequenceA t

          eid <- newEnvID
          (rparams, rret, rbody) <- bindTVars ((snd ifn.instFunDec.functionOther,) <$> Set.toList tvars) $ closure eid $ do
            rparams' <- traverse (\(n, t) -> do
              rn <- rDecon n
              rt <- rDeclaredType t
              return (rn, rt)) ifn.instFunDec.functionParameters
            rret' <- rDeclaredType ifn.instFunDec.functionReturnType
            rbody' <- rBody $ rStmt' <$> ifn.instFunBody
            pure (rparams', rret', rbody')

          -- set the environment
          --   NOTE: don't forget to remove self reference - it does not need to be in the environment.
          -- TODO: maybe just make it a part of 'closure'?
          let innerEnv = Map.delete (R.PDefinedVariable vid) $ sconcat $ gatherVariables <$> rbody
          env <- mkEnv eid innerEnv
          let fundec = FD env vid rparams rret (anns, snd ifn.instFunDec.functionOther)

          pure InstFun
            { instFunDec = fundec
            , instFunBody = rbody
            , instDef = inst
            -- , classFunctionPrototypeUniqueVar = protovid  -- TEMP remove
            , instClassFunDec = cfd
            }


        registerInst inst

        stmt $ Inst inst

    rCase :: CaseF U (Expr U) (Ctx (AnnStmt R)) -> Ctx (CaseF R (Expr R) (AnnStmt R))
    rCase kase = do
      rdecon <- rDecon kase.deconstruction
      mrCond <- traverse rExpr kase.caseCondition
      rbody <- rBody kase.caseBody
      pure $ Case rdecon mrCond rbody

    rBody :: Traversable t => t (Ctx a) -> Ctx (t a)
    rBody = scope . sequenceA

currentLevel :: Ctx Int
currentLevel = subtract 1 . length <$> RWS.gets scopes


-- must be called BEFORE binding tvars. It checks and errors out if there is a bound tvar that's being constrained.
rConstraints :: XClassConstraints U -> Ctx (Map Def.UnboundTVar (Set Class))
rConstraints constraints = do
  let f m (U.CC location klass utv) = do
        rklass <- resolveClass location klass
        tryResolveTVar utv >>= \case
          Just spanAndTV -> do
            err $ FurtherConstrainingExistingTVar spanAndTV (location, R.asUniqueClass rklass)
            pure m
          Nothing -> do
            pure $ Map.insertWith (<>) utv (Set.singleton rklass) m

  foldM f Map.empty constraints

rDecon :: Decon U -> Ctx (Decon R)
rDecon = transverse $ \(N location d) -> fmap (N location) $ case d of
  CaseVariable var -> do
    rvar <- newVar var
    pure $ CaseVariable rvar
  CaseConstructor conname decons -> do
    con <- resolveCon location conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor location conname
        placeholderCon conname.qualify

    CaseConstructor con <$> sequenceA decons
  CaseRecord tyName members -> do
    ty <- resolveType (error "location in types!") tyName
    mems <- traverse sequenceA members

    -- NOTE: we can check here if members exist in datatype.
    -- however it won't be so simple if we add anonymous structs.
    -- basically, it'll be checked during typechecking..?
    -- TODO: what's better?
    case tryGetMembersFromDatatype ty of
      Nothing -> pure ()
      Just recs -> do
        let tyMems = Set.fromList $ NonEmpty.toList recs
        let currentMems = Set.fromList $ NonEmpty.toList $ fst <$> mems
        let extraneousMems = currentMems \\ tyMems

        for_ extraneousMems $ \mem ->
          err $ MemberNotInDataDef (error "todo", mem) (R.asUniqueType ty, NonEmpty.toList recs)

        let memDefinitions = Map.unionsWith (+) $ flip Map.singleton (1 :: Int) . fst <$> mems
        let redefinedMems = fmap fst $ filter ((>1) . snd) $ Map.toList memDefinitions  -- find member variables that were defined more than once.
        for_ redefinedMems $ \mem ->
          err $ RedefinedMember (error "todo") mem

    pure $ CaseRecord ty mems

rExpr :: Expr U -> Ctx (Expr R)
rExpr = cata $ \(N location expr) -> embed . N location <$> case expr of  -- transverse, but unshittified
  Lit cx -> case cx of
    LInt i -> pure $ Lit $ LInt i
    LFloat f -> pure $ Lit $ LFloat f
    LString si -> mkStringInterpolation location si
    --   rsi <- for2 si $ \vn -> do
    --       (loc, v) <- resolveVar vn

    --       -- we only allow defined variables in string interpolation
    --       case v of
    --         DefinedVariable {} -> pure ()
    --         ExternalVariable {} -> pure ()
    --         _ -> err $ OnlyVariablesAreAllowedInStringInterpolation vn

    --       pure (v, loc)


  Var v () -> do
    (l, vid) <- resolveVar location v
    pure $ Var vid l
  Con conname () -> do
    con <- resolveCon location conname >>= \case
      Just con -> pure con
      Nothing -> do
        err $ UndefinedConstructor location conname
        placeholderCon conname.qualify

    -- you may not use the constructor of a pointer!
    --  only when deconstructing!
    when (isPointer con) $ err $ UsingPointerConstructor location

    eid <- newEnvID
    pure $ Con con eid
  MemAccess e memname -> do
    rexpr <- e
    pure $ MemAccess rexpr memname
  RecCon tyname mems -> do
    ty <- resolveType (error "location in types!") tyname
    mems' <- Def.sequenceA2 mems

    case R.tryGetMembersFromDatatype ty of
      Nothing -> pure ()
      Just recs -> do
        let tyMems = Set.fromList $ NonEmpty.toList recs
        let currentMems = Set.fromList $ NonEmpty.toList $ fst <$> mems

        -- TODO: I don't have a Show instance for DataDef because lazy, so this should suffice for now.
        let dd = (R.asUniqueType ty, NonEmpty.toList recs)

        -- report members not in the current datatype.
        let extraneousMems = currentMems \\ tyMems
        for_ extraneousMems $ \mem ->
          err $ MemberNotInDataDef (error "todo", mem) dd

        -- report members that were not defined, but should have been.
        let undefinedMems = tyMems \\ currentMems
        for_ undefinedMems $ \mem ->
          err $ DidNotDefineMember (error "todo", mem) dd

        -- report redefinitions.
        let memDefinitions = Map.unionsWith (+) $ flip Map.singleton (1 :: Int) . fst <$> mems
        let redefinedMems = fmap fst $ filter ((>1) . snd) $ Map.toList memDefinitions  -- find member variables that were defined more than once.
        for_ redefinedMems $ \mem ->
          err $ RedefinedMember (error "todo") mem

    pure $ RecCon ty mems'

  RecUpdate e mems -> do
    e' <- e
    mems' <- Def.sequenceA2 mems
    pure $ RecUpdate e' mems'

  BinOp l op r -> BinOp <$> l <*> pure op <*> r
  UnOp op x -> UnOp op <$> x
  Call c args -> Call <$> c <*> sequenceA args
  As e t -> As <$> e <*> rType t
  Lam () params body -> do
    lamId <- lambdaVar
    eid <- newEnvID
    (rParams, rBody) <- closure eid $ do
      rParams <- traverse newVar params
      rBody <- scope body
      pure (rParams, rBody)

    let innerEnv = gatherVariablesFromExpr rBody -- TODO: environment making in 'closure' function.
    env <- mkEnv eid innerEnv
    pure $ Lam (R.LamDec lamId env) rParams rBody

rType :: Type U -> Ctx (Type R)
rType = transverse rType'

rDeclaredType :: DeclaredType U -> Ctx (DeclaredType R)
rDeclaredType = \case
  TypeNotDeclared -> pure TypeNotDeclared
  DeclaredType t -> DeclaredType <$> rType t

rClassType :: ClassType U -> Ctx (ClassType R)
rClassType = transverse $ \case
  Self -> pure Self
  NormalType t -> NormalType <$> rType' t

rType' :: TypeF U (Ctx a) -> Ctx (TypeF R a)
rType' = \case
  TCon t tapps () -> do
    rt <- resolveTypeOrClass (error "location in types!") t
    rtApps <- sequenceA tapps
    case (rt, rtApps) of
      (Left klass, []) ->
        pure $ TO $ TClass klass
      (Right dt, _) -> do
        pure $ TCon dt rtApps ()

      (Left klass, _:_) -> do
        err $ AppliedTypesToClassInType (error "todo") (R.asUniqueClass klass)

        -- what's better for error reporting here? returning a type or a class? what would produce better error messages?
        pure $ TO $ TClass klass

  TO v -> do
    tv <- resolveTVar (error "location in types!") v
    pure $ TO $ TVar tv
  TFun () args ret -> do
    rArgs <- sequence args
    rret <- ret
    pure $ TFun () rArgs rret


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
closure :: Def.EnvID -> Ctx a -> Ctx a
closure eid x = do
  oldScope <- RWST.get          -- enter scope

  RWST.modify $ \state@(CtxState { scopes = scopes', envStack = envStack' }) -> state { scopes = emptyScope <| scopes', envStack = eid : envStack' }
  x' <- x                       -- evaluate body
  RWST.put oldScope             -- exit scope

  return x'


-- cheap and bad string interpolation. (it would be more readable if we generated types on the fly. the errors would be slightly better!)
mkStringInterpolation :: Def.Location ->  XStringInterpolation U -> Ctx (ExprF R (Expr R))
mkStringInterpolation fullInterpolationLocation si = do
  let
    e loc = Fix . N loc
    digOutVar :: Expr R -> R.Variable
    digOutVar (Fix (N location expr)) = case expr of
      UnOp Def.Deref x -> digOutVar x
      MemAccess x _ -> digOutVar x
      Var v _ -> v

      _ -> error "[COMPILER ERROR]: incorrect expression in interpolated string"

    mkStackedConcat loc = fmap (e loc) . \case
      [] -> pure $ Lit $ LString ""
      [Left s] -> pure $ Lit $ LString s
      [Right ee] -> do
        re@(Fix (N varLocation re')) <- rExpr ee
        -- (loc, v) <- resolveVar vn

        -- we only allow defined variables in string interpolation
        case digOutVar re of
          DefinedVariable {} -> pure ()
          ExternalVariable {} -> pure ()
          v -> err $ OnlyVariablesAreAllowedInStringInterpolation fullInterpolationLocation varLocation $ Def.varName $ R.asPUniqueVar $ R.asProto v

        pure re'

      xs@(_:_:_) -> do
        concatCon <- findBuiltinStrConcat  -- NOTE: resolve it here, not outside, because we might still want to use strings before StrConcat is defined?
        let half = length xs `div` 2
        l@(Fix (N lloc _)) <- mkStackedConcat loc (take half xs)
        r@(Fix (N rloc _)) <- mkStackedConcat loc (drop half xs)

        emptyEnv <- newEnvID
        pure $ Call (e (lloc <> rloc) (Con concatCon emptyEnv)) [l, r]

  (\(N _ v) -> v) . project <$> mkStackedConcat fullInterpolationLocation si

-- NOTE: FORMER (and probably future) string interpolation.
--   LEFT HERE FOR FUTURE REFERENCE.
-- mkStringInterpolation :: XStringInterpolation U -> Ctx (ExprF R (Expr R))
-- mkStringInterpolation si = do
--   strClass <- findBuiltinStrClass
--   ut <- undefined
--   uc <- undefined
--   let
--     tvars = [ TV ("si" <> fromString (show idx)) (BindByType ut) (Set.singleton strClass) | idx <- [1..length si] ] :: [TVar R]
--     dc = DC { conDataDef = dd, conID = uc, conTypes = Fix . TO . TVar <$> tvars, conAnns = [] }
--     dd = DD { ddName = ut, ddScheme = tvars, ddCons = Right [dc], ddAnns = [] } :: DataDef R
--   undefined

-- findBuiltinStrClass :: Ctx R.Class
-- findBuiltinStrClass = undefined


type Ctx = RWST (Maybe Prelude) [ResolveError] CtxState CompilerContext  -- I might add additional context later.

data CtxState = CtxState
  { scopes :: NonEmpty Scope
  , envStack :: [Def.EnvID]
  , inLambda :: Bool  -- hack to check if we're in a lambda currently. when the lambda is not in another lambda, we put "Local" locality.
  , tvarBindings :: Map Def.UnboundTVar (Def.Location, TVar R)

  , loaderFn :: Compiler.ModuleLoader
  , modules :: Map U.ModuleQualifier (Module TC)  -- list imported modules. automatically gets scoped, so dunt wurry.

  -- we need to keep track of each defined function to actually typecheck it.
  -- NOTE: we don't need it anymore, since we infer the functions in Typecheck at definition site anyway.
  , functions :: [Function R]
  , datatypes :: [DataDef R]
  , classes   :: [ClassDef R]
  , instances :: [InstDef R]
  }

data Scope = Scope
  { varScope :: Map Def.VarName R.VariableProto
  , conScope :: Map Def.ConName R.Constructor
  , tyScope :: Map Def.TCon (Either Class R.DataType)

  , instScope :: Map Class (Map R.DataType R.Inst)
  }

emptyState :: CtxState
emptyState =
  CtxState { scopes = NonEmpty.singleton emptyScope, envStack = mempty, tvarBindings = mempty, loaderFn = error "should not import anything in Prelude!", modules = mempty, inLambda = False, functions = mempty, datatypes = mempty, classes = mempty, instances = mempty }

emptyScope :: Scope
emptyScope = Scope { varScope = mempty, conScope = mempty, tyScope = mempty, instScope = mempty }

getScopes :: Ctx (NonEmpty Scope)
getScopes = RWST.gets scopes

-- Add later after I do typechecking.
mkState :: Compiler.ModuleLoader -> Prelude -> CtxState
mkState moduleLoader prel = CtxState
  { scopes = NonEmpty.singleton initialScope
  , envStack = mempty
  , tvarBindings = mempty
  , loaderFn = moduleLoader
  , modules = mempty
  , inLambda = False
  , functions = mempty
  , datatypes = mempty
  , classes = mempty
  , instances = mempty
  } where

    -- convert prelude to a scope
    initialScope = Scope
      { varScope = exportedVariables <> exportedFunctions

      , conScope = Map.fromList $ concat $ preludeExports.datatypes <&> \dd -> foldMap (fmap (\dc -> (dc.conID.conName, R.ExternalConstructor dc))) dd.ddCons
      , tyScope  = Map.fromList $ preludeExports.datatypes <&> \dd -> (dd.ddName.typeName, Right $ R.ExternalDatatype dd)

      , instScope = Map.fromListWith (<>) $ preludeExports.instances <&> \inst -> (ExternalClass inst.instClass, Map.singleton (R.ExternalDatatype $ fst inst.instType) (ExternalInst inst))
      }

    exportedVariables = Map.fromList $ preludeExports.variables <&> \(uv, t) ->
      (uv.varName, PExternalVariable uv t)
    exportedFunctions = Map.fromList $ preludeExports.functions <&> \fn ->
      (fn.functionDeclaration.functionId.varName, PExternalFunction fn)

    preludeExports = prel.tpModule.exports

generateVar :: Def.VarName -> Ctx Def.UniqueVar
generateVar name = do
  vid <- liftIO newUnique
  let var = Def.VI { varID = vid, varName = name }
  pure var

newFunction :: Function R -> Ctx ()
newFunction fun = do
  let uv = fun.functionDeclaration.functionId
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.PDefinedFunction fun) sc.varScope }
  RWST.modify $ \s -> s { functions = fun : s.functions }

newVar :: Def.VarName -> Ctx Def.UniqueVar
newVar name = do
  uv <- generateVar name
  modifyThisScope $ \sc -> sc { varScope = Map.insert uv.varName (R.PDefinedVariable uv) sc.varScope }
  pure uv

lambdaVar :: Ctx Def.UniqueVar
lambdaVar = do
  vid <- liftIO newUnique
  let var = Def.VI { varID = vid, varName = Def.VN (Text.pack "lambda") }
  return var

resolveVar :: Def.Location -> Qualified Def.VarName -> Ctx (Def.Locality, R.Variable)
resolveVar loc qname@(Qualified Nothing name) = do
  curlev <- currentLevel
  allScopes <- getScopes
  case lookupScope curlev name (fmap varScope allScopes) of
    Just (l, v) -> (l,) <$> protoVariableToVariable v
    Nothing -> do
      err $ UndefinedVariable loc qname
      (Def.Local,) . R.DefinedVariable <$> placeholderVar name

resolveVar loc (Qualified (Just mq) name) = do
  curlev <- currentLevel
  let locality = if curlev == 0 then Def.Local else Def.FromEnvironment 0
  tryFindExternalModule loc mq >>= \case
    Just tmod -> do
      -- This is very similar to 'Use' checking and importing! TODO: FEEEEECS
      snapshot <- getScopeSnapshot  -- hope it's not eagerly evaluated!

      let
        findVar = findInExternalModule tmod Common.variables $ \(v, t) ->
          if v.varName == name
            then Just $ R.ExternalVariable v t
            else Nothing

        findFun = findInExternalModule tmod Common.functions $ \fn ->
          if fn.functionDeclaration.functionId.varName == name
            then Just $ R.ExternalFunction fn snapshot
            else Nothing

        findClassFun = findInExternalModule tmod Common.classes $ \cd ->
          case find (\(CFD _ funId _ _ _ _) -> funId.varName == name) cd.classFunctions of
            Just cfd -> Just $ R.ExternalClassFunction cfd snapshot
            Nothing -> Nothing


      case findVar <|> findFun <|> findClassFun of
        Just x ->
          pure (locality, x)
        Nothing -> do
          err $ ModuleDoesNotExportVariable loc name mq
          (locality,) . DefinedVariable <$> generateVar name

    Nothing -> (locality,) . DefinedVariable <$> generateVar name

      -- case find undefined tmod.exports.variables of
      --   Nothing ->
      --     case find undefined tmod.exports.functions of
      --       Nothing ->
      --         case find undefined tmod.exports.classes of
      --           Nothing -> undefined

      --           Just _ -> undefined

      --       Just _ -> undefined

      --   Just _ -> undefined

protoVariableToVariable :: R.VariableProto -> Ctx R.Variable
protoVariableToVariable = \case
  R.PDefinedVariable uv -> pure $ R.DefinedVariable uv
  R.PExternalVariable uv t -> pure $ R.ExternalVariable uv t
  R.PDefinedFunction fn -> do
    snapshot <- getScopeSnapshot
    pure $ R.DefinedFunction fn snapshot
  R.PExternalFunction fn -> do
    snapshot <- getScopeSnapshot
    pure $ R.ExternalFunction fn snapshot
  R.PDefinedClassFunction cfd -> do
    snapshot <- getScopeSnapshot
    pure $ R.DefinedClassFunction cfd snapshot
  R.PExternalClassFunction cfd -> do
    snapshot <- getScopeSnapshot
    pure $ R.ExternalClassFunction cfd snapshot

placeholderVar :: Def.VarName -> Ctx Def.UniqueVar
placeholderVar = generateVar


generateCon :: Def.ConName -> Ctx Def.UniqueCon
generateCon name = do
  cid <- liftIO newUnique
  let con = Def.CI { conID = cid, conName = name }
  pure con

newCon :: DataCon R -> Ctx ()
newCon dc = do
  modifyThisScope $ \sc -> sc { conScope = Map.insert dc.conID.conName (R.DefinedConstructor dc) sc.conScope }

resolveCon :: Def.Location -> Qualified Def.ConName -> Ctx (Maybe R.Constructor)
resolveCon _ (Qualified Nothing name) = do
  allScopes <- getScopes
  curlev <- currentLevel
  -- This has been generalized to return Maybe instead of throwing an error.
  --   WHY? I needed this function somewhere else AND I the usage should be the same.
  --    This is more in line with the spiritual usage of Haskell - bubble up errors and handle them there. this makes it obvious what is happening with the value - no need to check inside the function. (remember this :3)
  let maybeCon = snd <$> lookupScope curlev name (fmap conScope allScopes)
  pure maybeCon

resolveCon location (Qualified (Just mq) name) = tryFindExternalModule location mq >>= \case -- we place a placeholder value here, because otherwise the error about the constructor not being found will be reported ALONGSIDE the error about the module not being found.
  Just tmod ->
    sequenceA $ findInExternalModule tmod Common.datatypes $ \case
      (DD { ddCons = Right cons }) -> find ((==name) . Def.conName . conID) cons <&> pure . R.ExternalConstructor

      _ -> Nothing

  Nothing -> do
    Just <$> placeholderCon name

placeholderCon :: Def.ConName -> Ctx R.Constructor
placeholderCon name = do
  uc <- generateCon name

  ti <- generateType $ Def.TC $ "PlaceholderTypeForCon" <> name.fromCN

  -- fill in later with a placeholder type.
  let dc = DC dd uc [] []
      dd = DD ti [] (Right [dc]) []
  pure $ DefinedConstructor dc


generateClass :: Def.ClassName -> Ctx Def.UniqueClass
generateClass cn = do
  cid <- liftIO newUnique
  let uc = Def.TCI { classID = cid, className = cn }
  pure uc

-- memo stuff
registerClass :: ClassDef R -> Ctx ()
registerClass cd = do
  modifyThisScope $ \sc -> sc
    -- class itself
    { tyScope = Map.insert (Def.uniqueClassAsTypeName cd.classID) (Left (R.DefinedClass cd)) sc.tyScope

    -- inner functions
    , varScope = foldr (\cfd@(CFD _ uv _ _ _ _) -> Map.insert uv.varName (R.PDefinedClassFunction cfd)) sc.varScope cd.classFunctions
    }

  RWST.modify $ \ctx -> ctx { classes = cd : ctx.classes }

resolveClass :: Def.Location -> Qualified Def.ClassName -> Ctx R.Class
resolveClass location qcn@(Qualified Nothing cn) = do
  allScopes <- getScopes
  curlev <- currentLevel
  let cnAsTCon = Def.TC cn.fromTN :: Def.TCon
  case lookupScope curlev cnAsTCon (fmap tyScope allScopes) of
    Just (_, Left c) -> pure c
    Just (_, Right dd) -> do
      err $ ExpectedClassNotDatatype location qcn (R.asUniqueType dd)
      placeholderClass cn
    Nothing -> do
      err $ UndefinedClass location qcn
      placeholderClass cn

resolveClass location (Qualified (Just mq) cn) = do
  tryFindExternalModule location mq >>= \case
    Just tmod -> case findInExternalModule tmod Common.classes (\k -> if k.classID.className == cn then Just k else Nothing) of
      Just cd -> pure $ R.ExternalClass cd
      Nothing -> do
        err $ ModuleDoesNotExportClass location cn mq
        placeholderClass cn
    Nothing -> undefined

placeholderClass :: Def.ClassName -> Ctx R.Class
placeholderClass = error . Def.printf "todo: placeholder class '%s'" . Def.pp

findFunctionInClass :: Def.Location -> Def.VarName -> R.Class -> Ctx (XClassFunDec R)
findFunctionInClass searchLocation vn ecd =
  let
    mcfd = case ecd of
      R.DefinedClass cd -> R.DefinedClassFunDec <$> find (\(CFD _ uv _ _ _ _) -> uv.varName == vn) cd.classFunctions
      R.ExternalClass cd -> R.ExternalClassFunDec <$> find (\(CFD _ uv _ _ _ _) -> uv.varName == vn) cd.classFunctions
    cid = R.asUniqueClass ecd
  in case mcfd of
    Just cfd -> pure cfd
    Nothing -> do
      err $ UndefinedFunctionOfThisClass searchLocation cid vn
      uv <- generateVar vn
      pure $ case ecd of
        R.DefinedClass cd -> R.DefinedClassFunDec $ CFD cd uv [] (Fix Self) () searchLocation
        R.ExternalClass cd -> R.ExternalClassFunDec $ CFD cd uv [] (Fix Self) () searchLocation


getScopeSnapshot :: Ctx R.ScopeSnapshot
getScopeSnapshot = do
  allScopes <- getScopes

  -- Merge scopes into a flattened projection. Choose left keys, as they are from inner scopes.
  pure $ foldr (Map.unionWith (<>) . instScope) Map.empty allScopes


registerInst :: InstDef R -> Ctx ()
registerInst inst = do
  modifyThisScope $ \sc -> sc
    { instScope = Map.insertWith (<>) inst.instClass (Map.singleton (fst inst.instType) (R.DefinedInst inst)) sc.instScope
    }

  RWST.modify $ \ctx -> ctx { instances = inst : ctx.instances }


-------------
-- Modules --
-------------

tryLoadModule :: U.ModuleQualifier -> Ctx (Maybe (Module TC))
tryLoadModule modq = do
  moduleLoader <- RWST.gets loaderFn
  lift $ moduleLoader modq

useModule :: U.ModuleQualifier -> Module TC -> Ctx ()
useModule mq tmod = do
  -- NOTE: if I decide to make it illegal to reimport modules, put error here.
  RWST.modify $ \s -> s { modules = Map.insert mq tmod s.modules }

quietlyAddInstancesFromImportedModule :: Module TC -> Ctx ()
quietlyAddInstancesFromImportedModule tmod = do
  let insts = tmod.exports.instances
  let instMap = Map.fromListWith (<>) $ insts <&> \inst -> (R.ExternalClass inst.instClass, Map.singleton (R.ExternalDatatype (fst inst.instType)) (R.ExternalInst  inst))
  modifyThisScope $ \sc -> sc
    { instScope = Map.unionWith (<>) instMap sc.instScope
    }

tryFindExternalModule :: Def.Location -> U.ModuleQualifier -> Ctx (Maybe (Module TC))
tryFindExternalModule location mq = do
  mods <- RWST.gets modules
  case mods !? mq of
    Just tmod -> pure $ Just tmod
    Nothing -> do
      err $ ModuleNotImported location mq
      pure Nothing


findInExternalModule :: Module TC -> (Exports TC -> [k]) -> (k -> Maybe a) -> Maybe a
findInExternalModule tmod selectorFn findFn = Def.firstJust findFn $ selectorFn tmod.exports



-- Generate a new unique type.
generateType :: Def.TCon -> Ctx Def.UniqueType
generateType name = do
  tid <- liftIO newUnique
  let ty = Def.TI { typeID = tid, typeName = name }
  pure ty

registerDatatype :: DataDef R -> Ctx ()
registerDatatype dd = do
  -- Check for duplication first
  -- if it exists, we still replace it, but an error is signaled.
  -- TODO: All of this is iffy. I don't really know what it's doing.
  let name = dd.ddName.typeName
  currentScope <- NonEmpty.head <$> getScopes
  case currentScope.tyScope !? name of
    Just (Right (R.DefinedDatatype _)) -> pure ()
    Just (Right (R.ExternalDatatype _)) -> pure ()  -- err $ TypeRedeclaration (error "bruh. i think we want to redeclare types.") name  -- maybe we should shadow still?????
    _ -> pure ()

  modifyThisScope $ \sc -> sc { tyScope = Map.insert name (Right $ R.DefinedDatatype dd) sc.tyScope }
  RWST.modify $ \s -> s { datatypes = dd : s.datatypes }
  pure ()

-- NOTE: used only in DataDefs... remove?
mkTVars :: Def.Binding -> [Def.UnboundTVar] -> [TVar R]
mkTVars b = fmap $ R.bindTVar mempty b

bindTVars :: [(Def.Location, TVar R)] -> Ctx a -> Ctx a
bindTVars tvs cx = do
    oldBindings <- RWS.gets tvarBindings

    -- make bindings and merge them with previous bindings
    let bindings = Map.fromList $ fmap (\(location, tv) -> (Def.UTV tv.fromTV, (location, tv))) tvs
    RWS.modify $ \ctx -> ctx { tvarBindings = bindings <> ctx.tvarBindings }

    x <- cx

    RWS.modify $ \ctx -> ctx { tvarBindings = oldBindings }

    pure x

tryResolveTVar :: Def.UnboundTVar -> Ctx (Maybe (Def.Location, TVar R))
tryResolveTVar utv = do
  tvs <- RWS.gets tvarBindings
  pure $ tvs !? utv

resolveTVar :: Def.Location -> Def.UnboundTVar -> Ctx (TVar R)
resolveTVar location utv = do
  mtv <- tryResolveTVar utv
  case mtv of
    Just (_, tv) -> pure tv
    Nothing -> do
      err $ UnboundTypeVariable location utv
      placeholderTVar utv

placeholderTVar :: Def.UnboundTVar -> Ctx (TVar R)
placeholderTVar utv = do
  var <- generateVar $ Def.VN $ "placeholderVarForTVar" <> utv.fromUTV
  pure (R.bindTVar mempty (BindByVar var) utv)

resolveType :: Def.Location -> U.Qualified Def.TCon -> Ctx R.DataType
resolveType location name = do
  tOrC <- resolveTypeOrClass (error "locaiton in types!") name
  case tOrC of
    Right t -> pure t
    Left c -> do
      let cid = R.asUniqueClass c
      err $ UsingClassNameInPlaceOfType location cid
      placeholderType name.qualify

resolveTypeOrClass :: Def.Location -> Qualified Def.TCon -> Ctx (Either R.Class R.DataType)
resolveTypeOrClass location (Qualified Nothing name) = do
  allScopes <- getScopes
  curlev <- currentLevel
  case lookupScope curlev name (fmap tyScope allScopes) of
    Just (_, typeOrClass) -> pure typeOrClass

    Nothing -> do
      err $ UndefinedType location name
      Right <$> placeholderType name
resolveTypeOrClass location (Qualified (Just _) name) = do
  error "todo"


placeholderType :: Def.TCon -> Ctx R.DataType
placeholderType name = do
  -- generate a placeholder type.
  ti <- generateType $ Def.TC $ "PlaceholderType" <> name.fromTC

  let dd = DD ti [] (Right []) []
  pure $ DefinedDatatype dd

modifyThisScope :: (Scope -> Scope) -> Ctx ()
modifyThisScope f =
  let modifyFirstScope (sc :| scs) = f sc :| scs
  in RWST.modify $ \sctx -> sctx { scopes = modifyFirstScope sctx.scopes }

lookupScope :: (Ord b) => Int -> b -> NonEmpty (Map b c) -> Maybe (Def.Locality, c)
lookupScope curlev k = foldr (\(locality, l) r -> (locality,) <$> Map.lookup k l <|> r) Nothing . (\(cur :| envs) -> (Def.Local, cur) :| fmap (\(l, sc) -> (Def.FromEnvironment l, sc)) (zip [curlev-1, curlev-2 .. 0] envs))


unit, findBuiltinStrConcat :: Ctx R.Constructor
unit = do
  prelude <- RWST.ask
  case prelude of
    -- When prelude was already typechecked, it should always be available.
    Just prelud -> pure $ R.ExternalConstructor prelud.unitValue

    -- When we're resolving prelude, find it from the environment.
    Nothing ->
      resolveCon (error "location in types!") (U.unqualified Prelude.unitName) <&> \case
        Just uc -> uc
        Nothing -> error $ "[COMPILER ERROR]: Could not find Unit type with the name: '" <> show Prelude.unitName <> "'. This must not happen."

-- COPY!
findBuiltinStrConcat = do
  prelude <- RWST.ask
  case prelude of
    -- When prelude was already typechecked, it should always be available.
    Just prelud -> pure $ R.ExternalConstructor prelud.strConcatValue

    -- When we're resolving prelude, find it from the environment.
    Nothing ->
      resolveCon (error "location in types!") (U.unqualified Prelude.strConcatName) <&> \case
        Just uc -> uc
        Nothing -> error $ "[COMPILER ERROR]: Could not find StrConcat type with the name: '" <> show Prelude.strConcatName <> "'. This must not happen."


err :: ResolveError -> Ctx ()
err = RWST.tell .  (:[])

data ResolveError
  = UndefinedVariable Def.Location (Qualified Def.VarName)
  | UndefinedConstructor Def.Location (Qualified Def.ConName)
  | UndefinedType Def.Location Def.TCon
  | UnboundTypeVariable Def.Location Def.UnboundTVar
  | FurtherConstrainingExistingTVar (Def.Location, TVar R) (Def.Location, Def.UniqueClass)
  -- | TypeRedeclaration Def.Location Def.TCon
  | CannotMutateFunctionDeclaration Def.Location Def.VarName
  | CannotMutateNonLocalVariable Def.Location Def.VarName
  | CannotMutateImportedVariable Def.Location Def.UniqueVar

  | DidNotDefineMember (Def.Location, Def.MemName) (Def.UniqueType, [Def.MemName])
  | MemberNotInDataDef (Def.Location, Def.MemName) (Def.UniqueType, [Def.MemName])
  | RedefinedMember    Def.Location Def.MemName

  | NotARecordType Def.Location Def.UniqueType

  | UndefinedClass Def.Location (Qualified Def.ClassName)
  | ExpectedClassNotDatatype Def.Location (Qualified Def.ClassName) Def.UniqueType
  | UsingClassNameInPlaceOfType Def.Location Def.UniqueClass  -- IDs are only, because I'm currently too lazy to make a Show instance.
  | UndefinedFunctionOfThisClass Def.Location Def.UniqueClass Def.VarName

  | AppliedTypesToClassInType Def.Location Def.UniqueClass

  | UsingPointerConstructor Def.Location

  | ModuleDoesNotExist Def.Location U.ModuleQualifier
  | ModuleDoesNotExportVariable Def.Location Def.VarName U.ModuleQualifier
  | ModuleDoesNotExportType Def.Location Def.TCon U.ModuleQualifier
  | ModuleDoesNotExportClass Def.Location Def.ClassName U.ModuleQualifier
  | ModuleDoesNotExportTypeOrClass Def.Location Def.TCon U.ModuleQualifier
  | ModuleNotImported Def.Location U.ModuleQualifier
  | TryingToImportConstructorsFromARecordType Def.Location Def.UniqueType U.ModuleQualifier
  | TryingToImportNonExistingConstructorOfType Def.Location Def.ConName Def.UniqueType U.ModuleQualifier
  | TryingToImportNonExistingFunctionOfClass Def.Location Def.VarName Def.UniqueClass U.ModuleQualifier

  | OnlyVariablesAreAllowedInStringInterpolation Def.Location Def.Location Def.VarName  -- badtype, only to appease Show.


instance Error ResolveError where
  toError source = \case
    UndefinedVariable location vn -> renderError source (fs $ printf "Undefined variable %s" (pp vn)) $ ln (location, Just "this guy")
    UndefinedConstructor location cn -> renderError source (fs $ printf "Undefined constructor %s" (pp cn)) $ ln (location, Just "dis")
    UndefinedType location tn -> renderError source (fs $ printf "Undefined type %s" (pp tn)) $ ln (location, Just "diz")
    UnboundTypeVariable location utv -> renderError source (fs $ printf "Unbound type variable %s" (pp utv)) $ ln (location, Just "miau")
    FurtherConstrainingExistingTVar (location, tv) (location', uc) -> renderError source (fs $ printf "Further constraining existing tvar %s with class %s" (pp tv) (pp uc)) $ lns [(location, Just "this is where the tvar was defined"), (location', Just "that's the constraint")]
    -- TypeRedeclaration location ty -> renderError source (fs $ printf "") $ ln (location, Just "")
    CannotMutateFunctionDeclaration location vn -> renderError source (fs $ printf "Cannot mutate a function.") $ ln (location, Just (fs $ printf "%s is a function, ya dingus" (pp vn)))
    CannotMutateNonLocalVariable location vn -> renderError source (fs $ printf "Currently, we cannot mutate non local variables.") $ ln (location, Just "might change, i dunno")
    CannotMutateImportedVariable location vn -> renderError source (fs $ printf "Currently, we cannot mutate imported variables.") $ ln (location, Just "might change, might not i dunno")

    DidNotDefineMember (location, undefinedMem) (recordType, mems) -> renderError source (fs $ printf "You forgot to define %s when constructing an instance of %s." (pp undefinedMem) (pp recordType)) $ ln (location, Nothing)
    MemberNotInDataDef (location, mem) (ty, possibleMems) -> renderError source (fs $ printf "Field %s not in type %s." (pp ty) (pp mem)) $ ln (location, Just (Def.tsctx possibleMems))
    RedefinedMember location mem -> renderError source (fs $ printf "Redefined member %s" (pp mem)) $ ln (location, Nothing)

    NotARecordType location ty -> renderError source (fs $ printf "Type %s is not a record type!" (pp ty)) $ ln (location, Nothing)

    UndefinedClass location className -> renderError source (fs $ printf "Undefined class %s" (pp className)) $ ln (location, Nothing)
    ExpectedClassNotDatatype location className ty -> renderError source (fs $ printf "Expected class, but %s is a datatype." (pp ty)) $ ln (location, Nothing)
    UsingClassNameInPlaceOfType location klass -> renderError source (fs $ printf "Expected type but %s is actually a type yo." (pp klass)) $ ln (location, Just "this should be a type yo")  -- IDs are only, because I'm currently too lazy to make a Show instance.

    UndefinedFunctionOfThisClass location klass vn -> renderError source (fs $ printf "Class %s don't have function %s, yo." (pp klass) (pp vn)) $ ln (location, Nothing)

    AppliedTypesToClassInType location klass -> renderError source (fs $ printf "%s is a class and you just applied types to it. Bruh." (pp klass)) $ ln (location, Nothing)

    UsingPointerConstructor location -> renderError source (fs $ printf "Cannot use Ptr constructor in normal code.") $ ln (location, Just "you just... can't, ok???")

    ModuleDoesNotExist location modul -> renderError source (fs $ printf "Could not find module %s." (pp modul)) $ ln (location, Nothing)
    ModuleDoesNotExportVariable location vn modul -> renderError source (fs $ printf "Module %s does not export %s." (pp modul) (pp vn)) $ ln (location, Nothing)
    ModuleDoesNotExportType location ty modul -> renderError source (fs $ printf "Module %s does not export type %s." (pp modul) (pp ty)) $ ln (location, Nothing)
    ModuleDoesNotExportClass location klass modul -> renderError source (fs $ printf "Module %s does not export class %s." (pp modul) (pp klass)) $ ln (location, Nothing)
    ModuleDoesNotExportTypeOrClass location ty modul -> renderError source (fs $ printf "Module %s does not export this class or type %s." (pp modul) (pp ty)) $ ln (location, Nothing)
    ModuleNotImported location modul -> renderError source (fs $ printf "Could not import module %s." (pp modul)) $ ln (location, Nothing)
    TryingToImportConstructorsFromARecordType location ty modul -> renderError source undefined undefined
    TryingToImportNonExistingConstructorOfType location cn ty modul -> renderError source undefined undefined
    TryingToImportNonExistingFunctionOfClass location vn uc modul -> renderError source undefined undefined

    OnlyVariablesAreAllowedInStringInterpolation fullLocation location vn -> renderError source (fs $ printf "Only variables are allowed in string interpolation.") $ lns [(fullLocation, Nothing), (location, Just "it's a function, you dingus")]

ln :: a -> NonEmpty a
ln = NonEmpty.singleton

lns :: [a] -> NonEmpty a
lns = NonEmpty.fromList

fs :: String -> Text
fs = fromString


-- environment stuff
mkEnv :: Def.EnvID -> Map VariableProto Def.Locality -> Ctx (XEnv R)
mkEnv eid innerEnv = do
  currentEnvStack <- RWS.gets envStack
  curlev <- currentLevel
  -- locality <- localityOfVariablesAtCurrentScope
  -- pure $ Env eid currentEnvStack (mapMaybe (\v -> (locality !? R.asPUniqueVar v) <&> \(_, loc) -> (v, loc)) $ Set.toList innerEnv)  -- filters variables to ones that are in the environment.
  let remapLocality = \case
        (_, Def.Local) -> Nothing
        (_, Def.FromEnvironment lev) | lev > curlev -> Nothing
        (PExternalFunction fn, _) | Def.AExternal `elem` fn.functionDeclaration.functionOther.functionAnnotations -> Nothing  -- controversial! we must exclude external functions. what is controversial is if we should do it here or during codegen?
        (PDefinedFunction fn, _) | Def.AExternal `elem` fst fn.functionDeclaration.functionOther -> Nothing  -- controversial! we must exclude external functions. what is controversial is if we should do it here or during codegen?

        (v, Def.FromEnvironment lev) | lev == curlev -> Just (v, Def.Local)
        (v, Def.FromEnvironment lev) -> Just (v, Def.FromEnvironment lev)
  let varsWithNewLocalities = mapMaybe remapLocality $ Map.toList innerEnv
  pure $ Env eid currentEnvStack varsWithNewLocalities

-- Make a new env ID.
newEnvID :: Ctx Def.EnvID
newEnvID = Def.EnvID <$> liftIO newUnique

-- used for function definitions
gatherVariables :: AnnStmt R -> Map R.VariableProto Def.Locality
gatherVariables = cata $ \(O (O (Annotated _ (Located _ bstmt)))) -> case first gatherVariablesFromExpr bstmt of
  Mutation v _ loc _ expr -> Map.insert (R.PDefinedVariable v) loc expr
  Return expr -> gatherVariablesFromExpr expr
  Fun fn ->
    let dec = fn.functionDeclaration
        envVars = Map.fromList dec.functionEnv.fromEnv
    in envVars
  Inst idef -> foldMap (\fn -> Map.fromList fn.instFunDec.functionEnv.fromEnv) idef.instFuns
  stmt -> bifold stmt

-- used for lambdas
gatherVariablesFromExpr :: Expr R -> Map VariableProto Def.Locality
gatherVariablesFromExpr = cata $ \(N _ e) -> case e of
  Var v loc -> Map.singleton (R.asProto v) loc  -- TODO: Is this... correct? It's used for making the environment, but now we can just use this variable to know. This is todo for rewrite.
                                --   Update: I don't understand the comment above.
  expr -> fold expr


scopeToExports :: Scope -> Exports R
scopeToExports sc = Exports
  { variables = vars
  , functions = funs
  , datatypes = dts
  , classes   = cls
  , instances = insts
  } where
    vars = mapMaybe (\case { PDefinedVariable var -> Just (var, ()); _ -> Nothing }) $ Map.elems sc.varScope

    funs = mapMaybe (\case { PDefinedFunction fun -> Just fun; _ -> Nothing }) $ Map.elems sc.varScope

    dts = mapMaybe (\case { DefinedDatatype dt -> Just dt; _ -> Nothing }) $ rights $ Map.elems sc.tyScope

    cls = mapMaybe (\case { R.DefinedClass cd -> Just cd; _ -> Nothing }) $ lefts $ Map.elems sc.tyScope

    insts = concat $ Map.elems $ Map.elems <$> sc.instScope


isPointer :: Constructor -> Bool
isPointer con =
  let anns = case con of
        DefinedConstructor dc -> dc.conDataDef.ddAnns
        ExternalConstructor dc -> dc.conDataDef.ddAnns
  in Def.AActualPointerType `elem` anns
