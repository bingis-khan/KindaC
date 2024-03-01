module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Parser (parse)


main :: IO ()
main = do
  [filename] <- getArgs
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> print err
    Right ast -> print ast