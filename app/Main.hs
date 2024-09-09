module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
-- import ASTPrettyPrinter (tModule)
import Std (preparePrelude)
import Pipeline (loadModule)
import AST.Typed (tModule)
import AST.Mono (mModule)
import Mono (mono)


main :: IO ()
main = do
  prelude <- preparePrelude
  putStrLn $ tModule prelude

  [filename] <- getArgs
  t <- loadModule (Just prelude) filename
  case t of
    Left err -> TextIO.putStrLn err
    Right mod -> do
      putStrLn $ tModule mod
      monoModule <- mono prelude mod
      putStrLn $ mModule monoModule
