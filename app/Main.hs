{-# LANGUAGE LambdaCase #-}
module Main (main) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Pipeline (loadPrelude, loadModule, finalizeModule)


main :: IO ()
main = do
  (filename, outputC) <- parseArgs

  -- first, get dat prelude
  prelude <- loadPrelude

  -- try compile module
  emod <- loadModule (Just prelude) filename
  case emod of
    Left errs -> TextIO.putStrLn errs
    Right modul -> do

      -- all good, finalize.
      cmod <- finalizeModule prelude modul

      if outputC 
        then TextIO.writeFile "test.c" cmod
        else TextIO.putStrLn cmod



parseArgs :: IO (Filename, ShouldOutputC)
parseArgs = do
  args <- getArgs
  let (mFilename, outputC) = foldr (\case { "--output-c" -> \(fn, _) -> (fn, True); fn -> \(_, oc) -> (Just fn, oc) }) (Nothing, False) args
  pure $ case mFilename of
    Just name -> (name, outputC)
    Nothing -> error "No filename provided."


type Filename = String
type ShouldOutputC = Bool
