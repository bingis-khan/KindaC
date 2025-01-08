{-# LANGUAGE OverloadedRecordDot #-}
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
import Data.Char (toUpper)
import Mono (mono)
import CPrinter (cModule)
import AST.Common (TCon, Result (..), fromResult, typeName, LitType (..), ctx, ctxPrint', ctxPrint, phase)
import Data.List.NonEmpty (NonEmpty)
import Data.Fix (Fix(..))
import qualified Data.Map as Map
import Data.Maybe (mapMaybe, listToMaybe)
import System.Exit (exitFailure)
import Data.Foldable (find)
import Data.Functor ((<&>))


compile :: Prelude -> T.Module -> IO Text
compile prelude mod = do
  undefined

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

type PreludeErr = Result (NonEmpty Text)

loadPrelude :: IO Prelude
loadPrelude = do
  epmod <- loadModule Nothing "kcsrc/prelude.kc"
  case epmod of
    Left errs -> do
      putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
      TextIO.putStrLn errs

      exitFailure

    Right pmod -> do
      let mkPrelude uv bt it ft tlr = Prelude
            { tpModule = pmod
            , unitValue = uv
            , boolType = bt
            , intType = it
            , floatType = ft
            , toplevelReturn = tlr
            }

      let 
        ne :: String -> NonEmpty Text
        ne = NonEmpty.singleton . Text.pack

      -- TODO: think about how to generalize it.
      --       don't fear duplication, but i want it to be readable.
      let findUnit :: PreludeErr T.DataCon
          findUnit = 
            let mdd (T.DD ut (T.Scheme [] []) [con] _) | ut.typeName == unitTypeName = Just con
                mdd _ = Nothing

                mdc   = listToMaybe $ mapMaybe mdd pmod.exports.datatypes
            in case mdc of
              Just dc -> pure dc
              Nothing -> Failure $ ne "[Prelude: Unit] Could not find suitable Unit type (Unit type name + Unit constructor, no tvars, single constructor)"

          findBoolType :: PreludeErr T.Type
          findBoolType =
            let isCorrectBool (T.DD ut (T.Scheme [] []) _ _) = ut.typeName == boolTypeName
                isCorrectBool _ = False

                mdd   = find isCorrectBool pmod.exports.datatypes
            in case mdd of
              Just dd -> 
                let bt = Fix $ T.TCon dd [] []
                in pure bt
              Nothing -> Failure $ ne "[Prelude: Bool] Could not find suitable Bool type (Bool type name + no tvars)"

          findIntType :: PreludeErr T.Type
          findIntType =
            let isCorrectInt (T.DD ut (T.Scheme [] []) _ _) = ut.typeName == intTypeName
                isCorrectInt _ = False

                mdd   = find isCorrectInt pmod.exports.datatypes
            in case mdd of
              Just dd -> 
                let bt = Fix $ T.TCon dd [] []
                in pure bt
              Nothing -> Failure $ ne "[Prelude: Int] Could not find suitable Int type (Int type name + no tvars)"

          findFloatType :: PreludeErr T.Type
          findFloatType =
            let isCorrectFloat (T.DD ut (T.Scheme [] []) _ _) = ut.typeName == floatTypeName
                isCorrectFloat _ = False

                mdd   = find isCorrectFloat pmod.exports.datatypes
            in case mdd of
              Just dd -> 
                let bt = Fix $ T.TCon dd [] []
                in pure bt
              Nothing -> Failure $ ne "[Prelude: Float] Could not find suitable Int type (Int type name + no tvars)"

          findTopLevelReturn :: PreludeErr T.Expr
          findTopLevelReturn = findIntType <&> \t ->
            let lit = T.Lit (LInt 0)
            in Fix $ T.TypedExpr t lit

      let eprelude = mkPrelude <$> findUnit <*> findBoolType <*> findIntType <*> findFloatType <*> findTopLevelReturn
      case eprelude of
        Failure errs -> do
          putStrLn "[PRELUDE ERROR]: There were errors while compiling prelude."
          TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs

          exitFailure
          
        Success p -> pure p

finalizeModule :: Prelude -> T.Module -> IO Text
finalizeModule prel mod = do
  -- join both modules
  let joinedStatements = prel.tpModule.toplevelStatements ++ mod.toplevelStatements

  phase "Removing Unused"
  let removedUnused = removeUnused joinedStatements
  ctxPrint T.tStmts removedUnused

  phase "Monomorphizing"
  mmod <- mono removedUnused
  ctxPrint M.mModule mmod

  phase "C-ing"
  let cmod = cModule mmod
  pure cmod


-- dbgLoadModule :: Maybe Prelude -> FilePath -> IO Text
-- dbgLoadModule mPrelude filename = do
--   source <- TextIO.readFile filename
--   case parse filename source of
--     Left err -> pure err
--     Right ast -> do
--       (rerrs, rmod) <- resolve mPrelude ast
--       print rerrs
--       putStrLn $ rModule rmod

--       let (terrs, tmod) = dbgTypecheck mPrelude rmod
--       let errors = s2t rerrs ++ s2t terrs

--       case errors of
--         [] -> do
--           putStrLn $ tModule tmod

--           case mPrelude of
--             Just prelude -> do
--               mmod <- monoModule prelude tmod
--               pure $ Text.pack $ mModule mmod

--             Nothing -> pure mempty

--         _ -> pure $ Text.unlines
--           [ Text.unlines errors
--           , Text.empty
--           , Text.pack $ tModule tmod
--           ]


s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)
