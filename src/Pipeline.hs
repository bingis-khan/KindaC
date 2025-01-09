{-# LANGUAGE OverloadedRecordDot, ApplicativeDo #-}
module Pipeline (loadModule, loadPrelude, finalizeModule) where

import qualified Data.Text.IO as TextIO
import Parser (parse)
import Resolver (resolve)
import Typecheck (typecheck)
import RemoveUnused (removeUnused)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty

import AST.Converged (Prelude (..), unitTypeName, boolTypeName, intTypeName, floatTypeName)
import qualified AST.Resolved as R
import qualified AST.Typed as T
import qualified AST.Mono as M
import Mono (mono)
import CPrinter (cModule)
import AST.Common (TCon, Result (..), typeName, LitType (..), ctxPrint, phase, ppTCon, ctx', showContext)
import Data.List.NonEmpty (NonEmpty)
import Data.Fix (Fix(..))
import Data.Maybe (mapMaybe, listToMaybe)
import System.Exit (exitFailure)
import Data.Foldable (find)
import Text.Printf (printf)



-- Loads and typechecks a module.
--   TODO: WRT errors: I should probably make a type aggregating all the different types of errors and put it in AST.hs.
--   However, right now, I can just turn them into strings. THIS IS TEMPORARY.
loadModule :: Maybe Prelude -> FilePath -> IO (Either Text T.Module)
loadModule mPrelude filename = do
  source <- TextIO.readFile filename

  phase "Parsing"
  case parse filename source of
    Left err -> pure $ Left err
    Right ast -> do
      phase "Resolving"
      (rerrs, rmod) <- resolve mPrelude ast
      ctxPrint R.pModule rmod

      
      phase "Typechecking"
      (terrs, tmod) <- typecheck mPrelude rmod

      phase "Typechecking (After Substitution)"
      ctxPrint T.tModule tmod

      let errors = s2t rerrs ++ s2t terrs
      pure $ case errors of
        [] -> Right tmod

        (_:_) ->
          Left $ Text.unlines errors


finalizeModule :: Prelude -> T.Module -> IO Text
finalizeModule prel modul = do
  -- join both modules
  let joinedStatements = prel.tpModule.toplevelStatements ++ modul.toplevelStatements

  phase "Removing Unused"
  let removedUnused = removeUnused joinedStatements
  ctxPrint T.tStmts removedUnused

  phase "Monomorphizing"
  mmod <- mono removedUnused
  ctxPrint M.mModule mmod

  phase "C-ing"
  let cmod = cModule mmod
  pure cmod



loadPrelude :: IO Prelude
loadPrelude = do
  epmod <- loadModule Nothing "kcsrc/prelude.kc"
  case epmod of
    Left errs -> do
      putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
      TextIO.putStrLn errs

      exitFailure

    Right pmod -> do
      let 
        ne :: String -> NonEmpty Text
        ne = NonEmpty.singleton . Text.pack

        findBasicType :: TCon -> PreludeErr T.Type
        findBasicType typename = 
            let isCorrectType (T.DD ut (T.Scheme [] []) _ _) = ut.typeName == typename
                isCorrectType _ = False

                mdd   = find isCorrectType pmod.exports.datatypes
                name = ctx' showContext ppTCon typename
            in case mdd of
              Just dd -> 
                let bt = Fix $ T.TCon dd [] []
                in pure bt
              Nothing -> Failure $ ne $ printf "[Prelude: %s] Could not find suitable %s type (%s type name + no tvars)" name name name

      let findUnit :: PreludeErr T.DataCon
          findUnit = 
            let mdd (T.DD ut (T.Scheme [] []) [con] _) | ut.typeName == unitTypeName = Just con
                mdd _ = Nothing

                mdc   = listToMaybe $ mapMaybe mdd pmod.exports.datatypes
            in case mdc of
              Just dc -> pure dc
              Nothing -> Failure $ ne "[Prelude: Unit] Could not find suitable Unit type (Unit type name + Unit constructor, no tvars, single constructor)"

          mkTopLevelReturn :: T.Type -> T.Expr
          mkTopLevelReturn t =
            let lit = T.Lit (LInt 0)
            in Fix $ T.TypedExpr t lit

      let eprelude = do  -- should compile to applicative do! TODO: test it somehow.
            unit <- findUnit
            bool <- findBasicType boolTypeName
            int  <- findBasicType intTypeName
            float <- findBasicType floatTypeName
            pure $ Prelude { tpModule = pmod, unitValue = unit, boolType = bool, intType = int, floatType = float, toplevelReturn = mkTopLevelReturn int }

      case eprelude of
        Failure errs -> do
          putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
          TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs

          exitFailure
          
        Success p -> pure p

type PreludeErr = Result (NonEmpty Text)



s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)
