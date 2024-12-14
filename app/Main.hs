{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
-- import ASTPrettyPrinter (tModule)
-- import Std (preparePrelude)
-- import Pipeline (loadModule, parseModule)
import AST.Typed (tModule)
import AST.Common (ctx)
import qualified AST.Untyped as U
import qualified AST.Resolved as R
import qualified AST.Typed as T
import Parser (parse)
import Resolver (resolve)
import Data.Text (Text)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Typecheck (typecheck)
import Mono (mono)
import Control.Monad (when)
import qualified AST.Mono as M
-- import AST.Mono (mModule)
-- import Mono (mono)
import CPrinter (cModule)
import RemoveUnused (removeUnused)
import Data.Char (toUpper)
-- import AST.Converged (Prelude(..))


main :: IO ()
main = do
  -- prelude <- preparePrelude
  -- putStrLn $ tModule prelude.tpModule

  -- (filename, outputc) <- parseArgs
  -- t <- loadModule (Just prelude) filename
  -- case t of
  --   Left err -> TextIO.putStrLn err
  --   Right mod -> do
  --     putStrLn $ tModule mod
  --     monoModule <- mono prelude mod

  --     putStrLn "MONO MODULE AYO"
  --     putStrLn $ mModule monoModule

  --     let cout = cModule monoModule
  --     if outputc
  --       then do
  --         let newFilename = takeBaseName filename <> ".c"
  --         TextIO.writeFile newFilename cout
  --       else do
  --         TextIO.putStrLn cout

  let filename = "testprelude.kc"
  emod <- parseModule filename
  case emod of
    Left err -> TextIO.putStrLn err
    Right mod -> do
      phase "resolving"
      (rerrs, mod') <- resolve Nothing mod
      putStrLn $ R.pModule mod'

      phase "typechecking"
      (terrs, tmod) <- typecheck Nothing mod'
      putStrLn $ T.tModule tmod
      let errors = s2t rerrs ++ s2t terrs
      TextIO.putStrLn $ Text.unlines errors

      when (null errors) $ do
        phase "removing unused"
        let removedUnused = removeUnused tmod.toplevelStatements
        putStrLn $ T.tStmtsOnly removedUnused

        phase "monomorphizing"
        mmod <- mono removedUnused
        putStrLn $ M.mModule mmod

        phase "c-ing"
        let cmod = cModule mmod
        TextIO.putStrLn cmod

        TextIO.writeFile "test.c" cmod

      -- case mtmod of
        -- Left tes -> 
          -- let errors = (s2t errs ++) $ NonEmpty.toList $ s2t tes
          -- in TextIO.putStrLn $ Text.unlines errors

        -- Right _ | (not . null) errs -> TextIO.putStrLn $ Text.unlines $ s2t errs
        -- Right tmod -> putStrLn $ T.tModule tmod

s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)

phase :: String -> IO ()
phase text = 
  let n = 10
  in putStrLn $ replicate n '=' <> " " <> map toUpper text <> " " <> replicate n '='

-- Misc for testing
parseModule :: FilePath -> IO (Either Text U.Module)
parseModule filename = do
  source <- TextIO.readFile filename
  pure $ parse filename source

type Filename = String
type OutputC = Bool
parseArgs :: IO (Filename, OutputC)
parseArgs = do
  args <- getArgs
  let (mFilename, outputC) = foldr (\case { "--output-c" -> \(fn, _) -> (fn, True); fn -> \(_, oc) -> (Just fn, oc) }) (Nothing, False) args
  pure $ case mFilename of
    Just name -> (name, outputC)
    Nothing -> error "No filename provided."

takeBaseName :: FilePath -> String
takeBaseName = reverse . drop 1 . dropWhile (/= '.') . reverse
