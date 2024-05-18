module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Parser (parse)
import ASTPrettyPrinter (rModule)
import Resolver (resolve)
import Std (preparePrelude)


main :: IO ()
main = do
  prelude <- preparePrelude

  [filename] <- getArgs
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> TextIO.putStrLn err
    Right ast -> do
      print ast
      (errs, rmod) <- resolve ast
      print errs
      putStrLn $ rModule rmod
