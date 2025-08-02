{-# LANGUAGE OverloadedRecordDot, ApplicativeDo, OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
module Pipeline (loadModule, loadPrelude, finalizeModule) where

import qualified Data.Text.IO as TextIO
import Parser (parse)
import Resolver (resolve)
import Typecheck (typecheck)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty

import qualified AST.Typed as T
import Data.List.NonEmpty (NonEmpty)
import Data.Fix (Fix(..))
import Data.Maybe (mapMaybe, listToMaybe)
import System.Exit (exitFailure)
import Data.Foldable (find)
import Text.Printf (printf)
import AST.Prelude (Prelude (..))
import qualified AST.Prelude as Prelude
import AST.Common (Module, DataDef (..), Type, DataCon, Expr, TypeF (..), ExprF (..), ExprNode (..), datatypes, LitType (..))
import qualified AST.Def as Def
import AST.Typed (TC, Mod (topLevelStatements))
import AST.Def (Result(..), phase, PP (..))
import Mono (mono)
import CPrinter (cModule)
import CompilerContext (CompilerContext)
import qualified CompilerContext as Compiler
import Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.Trans.RWS as RWST
import Data.Map ((!?))
import qualified System.Directory as Directory
import Error (Error (..))
import qualified System.FilePath as FilePath



preludePath, stdPath :: FilePath
preludePath = "kcsrc/prelude.kc"
stdPath = "kcsrc/std/"


-- Loads and typechecks a module.
--   TODO: WRT errors: I should probably make a type aggregating all the different types of errors and put it in AST.hs.
--   However, right now, I can just turn them into strings. THIS IS TEMPORARY.
loadModule :: FilePath -> CompilerContext (Maybe (Module TC))
loadModule filename = do
  let moduleName = Text.pack $ FilePath.takeFileName filename
  source <- liftIO $ TextIO.readFile filename
  prelude <- RWST.asks snd

  phase "Parsing"
  case parse filename source of
    Left err -> do
      Compiler.addErrors moduleName [err]
      pure Nothing

    Right ast -> do
      Def.ctxPrint ast

      phase "Resolving"
      (rerrs, rmod) <- resolve (Just prelude) (moduleLoader moduleName) ast
      Def.ctxPrint rmod

      
      phase "Typechecking"
      (terrs, tmod) <- liftIO $ typecheck (Just prelude) rmod

      Compiler.addErrors moduleName $ map (" " <>) $ s2t source rerrs ++ s2t source terrs
      pure $ Just tmod


moduleLoader :: Text -> Compiler.ModuleLoader
moduleLoader compilingModule mq = do
  mtmod <- RWST.gets Compiler.loadedModules
  case mtmod !? mq of
    Nothing -> do
      filepath <- Compiler.mkModulePath mq

      -- first, check if a file with that name exists in current project
      projectModuleExists <- liftIO $ Directory.doesFileExist filepath
      if projectModuleExists
        then do
          lmtmod <- Compiler.relativeTo filepath $ loadModule filepath
          Compiler.storeModule mq lmtmod
          pure lmtmod

        else do
          stdpath <- Compiler.relativeTo stdPath $ Compiler.mkModulePath mq  -- TODO: xddddddd very roundabout way to do it
          stdModuleExists <- liftIO $ Directory.doesFileExist stdpath
          if stdModuleExists
            then do
              lmtmod <- Compiler.relativeTo stdpath $ loadModule stdpath
              Compiler.storeModule mq lmtmod
              pure lmtmod
            else do
              Compiler.addErrors compilingModule [Text.pack $ Def.printf "Could not find module %s. (Searched both for '%s' and std '%s')" (show mq) filepath stdpath]
              pure Nothing

    Just lmtmod -> pure lmtmod


finalizeModule :: NonEmpty (Module TC) -> IO Text
finalizeModule modules = do
  -- join both modules
  let joinedStatements = concatMap topLevelStatements modules

  phase "Monomorphizing"
  mmod <- mono joinedStatements

  phase "Monomorphized statements"
  Def.ctxPrint mmod

  -- phase "C-ing"
  let cmod = cModule mmod
  pure cmod



loadPrelude :: IO Prelude
loadPrelude = do
  epmod <- do
    source <- liftIO $ TextIO.readFile preludePath

    phase "Parsing"
    case parse preludePath source of
      Left err -> do
        pure $ Left err

      Right ast -> do
        Def.ctxPrint ast

        phase "Resolving"
        (rerrs, rmod) <- Compiler.preludeHackContext $ resolve Nothing (error "no module loader for prelude") ast
        Def.ctxPrint rmod

      
        phase "Typechecking"
        (terrs, tmod) <- liftIO $ typecheck Nothing rmod

        pure $ case s2t source rerrs <> s2t source terrs of
          [] -> Right tmod
          errs@(_:_) -> Left $ Text.unlines errs

  case epmod of
    Left errs -> liftIO $ do
      putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
      TextIO.putStrLn errs

      exitFailure

    Right pmod -> do
      let 
        ne :: String -> NonEmpty Text
        ne = NonEmpty.singleton . Text.pack

        findBasicType :: Def.TCon -> PreludeErr (Type TC)
        findBasicType typename = 
            let isCorrectType :: DataDef TC -> Bool
                isCorrectType (DD ut (T.Scheme [] []) _ _) = ut.typeName == typename
                isCorrectType _ = False

                mdd  = find isCorrectType pmod.exports.datatypes
                name = Def.ctx' Def.showContext pp typename
            in case mdd of
              Just dd -> 
                let bt = Fix $ TCon dd [] []
                in pure bt
              Nothing -> Failure $ ne $ printf "[Prelude: %s] Could not find suitable %s type (%s type name + no tvars)" name name name

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
        findPtrType :: PreludeErr (Type TC -> Type TC)
        findPtrType =
            let
              fitsPtrType :: DataDef TC -> Bool
              fitsPtrType = \case
                DD ut (T.Scheme [_] []) _ _ -> ut.typeName == Prelude.ptrTypeName
                _ -> False
              mdd = find fitsPtrType pmod.exports.datatypes
            in case mdd of
              Just dd -> Success $ \t -> Fix $ TCon dd [t] []
              Nothing -> Failure $ ne $ printf "[Prelude: Ptr] Could not find suitable Ptr type (Ptr type name + one tvar)" 

      let eprelude = do  -- should compile to applicative do! TODO: test it somehow.
            unit <- findUnit
            strConcat <- findStrConcat
            bool <- findBasicType Prelude.boolTypeName
            int  <- findBasicType Prelude.intTypeName
            float <- findBasicType Prelude.floatTypeName
            ptr <- findPtrType
            constStr <- findBasicType Prelude.constStrTypeName
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
