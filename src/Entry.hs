-- This was created, because the Haskell LSP does not seem to work for app/Main.hs
{-# LANGUAGE LambdaCase #-}
module Entry (compilerMain) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import qualified AST.Def as Def
import AST.Def (PP(..))
import Pipeline (loadPrelude, loadModule, finalizeModule)
import CompilerContext (compilerContext)
import Control.Monad.IO.Class (liftIO)
import qualified System.FilePath as FilePath
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty


compilerMain :: IO ()
compilerMain = do
  (filename, outputC) <- parseArgs

  let basePath = FilePath.takeDirectory filename

  prelude <- loadPrelude

  -- first, get dat prelude
  errOrModules <- compilerContext basePath prelude $ loadModule filename

  case errOrModules of
    Left errs -> TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs
    Right modules -> do
      -- TEMP: i wanna check the typechecked module.
      cmod <- liftIO $ finalizeModule modules

      if outputC 
        then liftIO $ TextIO.writeFile "test.c" cmod
        else liftIO $ TextIO.putStrLn cmod


parseArgs :: IO (Filename, ShouldOutputC)
parseArgs = do
  args <- getArgs
  let (mFilename, outputC) = foldr (\case { "--output-c" -> \(fn, _) -> (fn, True); fn -> \(_, oc) -> (Just fn, oc) }) (Nothing, False) args
  pure $ case mFilename of
    Just name -> (name, outputC)
    Nothing -> error "No filename provided."


type Filename = String
type ShouldOutputC = Bool
