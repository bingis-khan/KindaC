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
import Pipeline (loadPrelude, loadModule, finalizeModule)
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

  (filename, outputC) <- parseArgs

  -- first, get dat prelude
  prelude <- loadPrelude
  emod <- loadModule (Just prelude) filename
  case emod of
    Left errs -> TextIO.putStrLn errs
    Right mod -> do
      cmod <- finalizeModule prelude mod

      if outputC 
        then TextIO.writeFile "test.c" cmod
        else do
          TextIO.putStrLn cmod

      -- case mtmod of
        -- Left tes -> 
          -- let errors = (s2t errs ++) $ NonEmpty.toList $ s2t tes
          -- in TextIO.putStrLn $ Text.unlines errors

        -- Right _ | (not . null) errs -> TextIO.putStrLn $ Text.unlines $ s2t errs
        -- Right tmod -> putStrLn $ T.tModule tmod

s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)

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
