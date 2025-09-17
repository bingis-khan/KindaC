{-# LANGUAGE OverloadedRecordDot, ApplicativeDo, OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Pipeline (startFromModule, codegen, loadPrelude, loadModule) where

import qualified Data.Text.IO as TextIO
import Parser (parse)
import Resolver (resolve)
import Typecheck (typecheck)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty

import qualified AST.Typed as T
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Fix (Fix(..))
import Data.Maybe (mapMaybe, listToMaybe)
import System.Exit (exitFailure)
import Data.Foldable (find)
import Text.Printf (printf)
import AST.Prelude (Prelude (..))
import qualified AST.Prelude as Prelude
import AST.Common (Module, DataDef (..), Type, DataCon, Expr, TypeF (..), ExprF (..), ExprNode (..), datatypes, LitType (..))
import qualified AST.Def as Def
import AST.Typed (TC, Mod (topLevelStatements), T)
import AST.Def (Result(..), phase, pc, LogType (P, R, T_AST, M, F))
import Mono (mono)
import CPrinter (cModule)
import qualified InterModular
import Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.Trans.RWS.Strict as RWST
import Data.Map.Strict ((!?))
import qualified System.Directory as Directory
import Error (Error (..))
import qualified System.FilePath as FilePath
import Control.Monad.Trans.Class (lift)
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import InterModular (InterModular, moduleCtx)
import qualified InterModular as InterModule
import qualified Control.Monad.Trans.RST as RST
import TypeFix (typefix)
import TypingContext (globalTypeUni, globalEnvAddition)
import qualified AST.Untyped as U
import Lens.Micro ((^.))
import BaseCtx (BaseCtx)


-- temporary redef
force :: a -> a
force = id


preludePath, stdPath :: FilePath
preludePath = "/home/bob/prj/KindaC/kcsrc/prelude.kc"
stdPath = "/home/bob/prj/KindaC/kcsrc/std/"


startFromModule :: FilePath -> BaseCtx (Either (NonEmpty Text) (Module T))
startFromModule path = do
  emod <- moduleCtx path $ do
    prelude <- loadPrelude
    loadModule (Just prelude) path

  case emod of
    Left errs -> pure $ Left errs
    Right (mods, tc) -> do
      tfmod <- typefix tc.globalTypeUni tc.globalEnvAddition mods

      phase F "Typechecking (fix)"
      pc F $ Def.ppLines tfmod

      pure $ Right tfmod


-- Loads and typechecks a module.
--   TODO: WRT errors: I should probably make a type aggregating all the different types of errors and put it in AST.hs.
--   However, right now, I can just turn them into strings. THIS IS TEMPORARY.
loadModule :: Maybe Prelude -> FilePath -> InterModular (Maybe (Module TC))
loadModule mPrelude filename = do
  let moduleName = Text.pack $ FilePath.takeFileName filename
  source <- liftIO $ TextIO.readFile filename
  -- prelude <- RWST.asks Compiler.prelude

  phase P "Parsing"
  case parse filename source of
    Left err -> do
      InterModular.addErrors moduleName [err]
      pure Nothing

    Right ast -> do
      pc P ast

      phase R "Resolving"
      (rerrs, rmod) <- force <$> resolve mPrelude (moduleLoader mPrelude moduleName) ast
      pc R rmod

      
      phase T_AST "Typechecking"
      (terrs, tmod) <- force <$> typecheck mPrelude rmod

      InterModular.addErrors moduleName $ map (" " <>) $ s2t source rerrs ++ s2t source terrs
      pure $ Just tmod


moduleLoader :: Maybe Prelude -> Text -> InterModule.Loader
moduleLoader mprel = InterModular.moduleLoader stdPath (loadModule mprel)

codegen :: Module T -> BaseCtx Text
codegen joinedModules = do
  phase M "Monomorphizing"
  mmod <- mono joinedModules

  phase M "Monomorphized statements"
  pc M mmod

  -- TODO: stats shouldn't really be here, but whatever.
  -- Def.unsilenceablePrintInContext (Def.pf "M exprs: %\nM stmt: %\nMF expr: %\nMF stmt: %\n" stats.exprVisited stats.stmtVisited stats.mfExprVisited stats.mfStmtVisited) :: BaseCtx ()
  -- Def.unsilenceablePrintInContext (Def.pf "M type nodes: %\nM unions: %\nMF type nodes: %\nMF unions %\n" stats.typeNodesVisited stats.unionsVisited stats.mfTypeNodesVisited stats.mfUnionsVisited) :: BaseCtx ()

  -- phase "C-ing"
  let cmod = force $ cModule mmod
  pure cmod



loadPrelude :: InterModular Prelude
loadPrelude = do
  epmod <- do
    source <- liftIO $ TextIO.readFile preludePath

    phase P "Parsing"
    case parse preludePath source of
      Left err -> do
        pure $ Left err

      Right ast -> do
        pc P ast

        phase R "Resolving"
        (rerrs, rmod) <- resolve Nothing (error "no module loader for prelude") ast
        pc R rmod

      
        phase T_AST "Typechecking"
        (terrs, tmod) <- typecheck Nothing rmod

        pure $ case s2t source rerrs <> s2t source terrs of
          [] -> Right tmod
          errs@(_:_) -> Left $ Text.unlines errs

  InterModular.storeModule (U.ModuleQualifier $ NonEmpty.singleton $ Def.ModName "prelude") $ Def.eitherToMaybe epmod

  case epmod of
    Left errs -> liftIO $ do
      putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
      TextIO.putStrLn errs

      exitFailure

    Right pmod -> do

      let 
        ne :: String -> NonEmpty Text
        ne = NonEmpty.singleton . Text.pack

        findBasicType :: Def.TCon -> InterModular (PreludeErr (Type TC))
        findBasicType typename = 
            let isCorrectType :: DataDef TC -> Bool
                isCorrectType (DD ut (T.Scheme [] []) _ _) = ut.typeName == typename
                isCorrectType _ = False

                mdd  = find isCorrectType pmod.exports.datatypes
                name = Def.pf "%" typename :: Def.Context
            in case mdd of
              Just dd -> do
                let bt = TCon dd [] []
                basicTypeID <- InterModular.nextTypeID
                InterModular.modifyTypeUni $ IntMap.insert basicTypeID.fromTypeID $ Right bt
                pure $ Success $ basicTypeID

              Nothing -> pure $ Failure $ ne $ Def.pf "[Prelude: %s] Could not find suitable %s type (%s type name + no tvars)" name name name

      let findUnit :: PreludeErr (DataCon TC)
          findUnit = 
            let
                mdd :: DataDef TC -> Maybe (DataCon TC)
                mdd (DD ut (T.Scheme [] []) (Right [con]) _) | ut.typeName == Prelude.unitTypeName = Just con
                mdd _ = Nothing

                mdc   = listToMaybe $ mapMaybe mdd pmod.exports.datatypes
            in case mdc of
              Just dc -> pure dc
              Nothing -> Failure $ ne "[Prelude: Unit] Could not find suitable Unit type (Unit type name + Unit constructor, no tvars, single constructor)"

      let findStrConcat :: PreludeErr (DataCon TC)
          findStrConcat = 
            let
                mdd :: DataDef TC -> Maybe (DataCon TC)
                mdd (DD ut (T.Scheme [_, _] []) (Right [con]) _) | ut.typeName == Prelude.strConcatTypeName = Just con
                mdd _ = Nothing

                mdc   = listToMaybe $ mapMaybe mdd pmod.exports.datatypes
            in case mdc of
              Just dc -> pure dc
              Nothing -> Failure $ ne "[Prelude: StrConcat] Could not find suitable StrConcat type (StrConcat type name + StrConcat constructor, two tvars, single constructor)"

          mkTopLevelReturn :: Type TC -> Def.Location -> Expr TC
          mkTopLevelReturn t loc =
            let lit = Lit (LInt 0)
            in Fix $ N (T.ExprNode t loc) lit

      let
        findPtrType :: PreludeErr (Type TC -> TypeF TC (Type TC))
        findPtrType =
            let
              fitsPtrType :: DataDef TC -> Bool
              fitsPtrType = \case
                DD ut (T.Scheme [_] []) _ _ -> ut.typeName == Prelude.ptrTypeName
                _ -> False
              mdd = find fitsPtrType pmod.exports.datatypes
            in case mdd of
              Just dd -> Success $ \t -> TCon dd [t] []
              Nothing -> Failure $ ne $ printf "[Prelude: Ptr] Could not find suitable Ptr type (Ptr type name + one tvar)" 

      ebool <- findBasicType Prelude.boolTypeName
      eint  <- findBasicType Prelude.intTypeName
      efloat <- findBasicType Prelude.floatTypeName
      econstStr <- findBasicType Prelude.constStrTypeName
      let eprelude = do  -- should compile to applicative do! TODO: test it somehow.
            bool <- ebool
            int <- eint
            float <- efloat
            constStr <- econstStr
            unit <- findUnit
            strConcat <- findStrConcat
            ptr <- findPtrType
            pure $ Prelude { tpModule = pmod, unitValue = unit, boolType = bool, intType = int, floatType = float, toplevelReturn = mkTopLevelReturn int, mkPtr = ptr, constStrType = constStr, strConcatValue = strConcat }

      case eprelude of
        Failure errs -> liftIO $ do
          putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
          TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs

          exitFailure
          
        Success p -> pure p

type PreludeErr = Result (NonEmpty Text)



s2t :: (Functor f, Error a) => Text -> f a -> f Text
s2t source = fmap (toError source)
