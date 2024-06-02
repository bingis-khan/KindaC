module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Parser (parse)
import ASTPrettyPrinter (tModule)
import Resolver (resolve)
import Std (preparePrelude)
import Typecheck (typecheck)


main :: IO ()
main = do
  prelude <- preparePrelude

  [filename] <- getArgs
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> TextIO.putStrLn err
    Right ast -> do
      (errs, rmod) <- resolve ast
      putStrLn "Resolving errors:"
      print errs

      let mtmod = typecheck Nothing rmod
      case mtmod of
        Left tes -> do
          putStrLn "Type errors:"
          print tes
        Right tmod ->
          putStrLn $ tModule tmod
