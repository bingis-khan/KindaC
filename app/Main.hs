module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Parser (parse)
import ASTPrettyPrinter (utModule)


main :: IO ()
main = do
  [filename] <- getArgs
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> TextIO.putStrLn err
    Right ast -> putStrLn $ utModule ast
