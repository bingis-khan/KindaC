module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import ASTPrettyPrinter (tModule)
import Std (preparePrelude)
import Pipeline (loadModule, dbgLoadModule)


main :: IO ()
main = do
  prelude <- preparePrelude
  putStrLn $ tModule prelude

  [filename] <- getArgs
  t <- dbgLoadModule (Just prelude) filename
  TextIO.putStrLn t
