{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
-- import ASTPrettyPrinter (tModule)
import Std (preparePrelude)
import Pipeline (loadModule, parseModule)
import AST.Typed (tModule)
import AST.Mono (mModule)
import Mono (mono)
import CPrinter (cModule)
import AST.Converged (Prelude(..))


main :: IO ()
main = do
  prelude <- preparePrelude
  putStrLn $ tModule prelude.tpModule

  (filename, outputc) <- parseArgs
  t <- loadModule (Just prelude) filename
  case t of
    Left err -> TextIO.putStrLn err
    Right mod -> do
      putStrLn $ tModule mod
      monoModule <- mono prelude mod

      putStrLn "MONO MODULE AYO"
      putStrLn $ mModule monoModule

      let cout = cModule monoModule
      if outputc
        then do
          let newFilename = takeBaseName filename <> ".c"
          TextIO.writeFile newFilename cout
        else do
          TextIO.putStrLn cout

  -- emod <- parseModule filename
  -- case emod of
  --   Left err -> TextIO.putStrLn err
  --   Right mod -> print mod

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
