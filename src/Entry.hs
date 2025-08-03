-- This was created, because the Haskell LSP does not seem to work for app/Main.hs
{-# LANGUAGE LambdaCase #-}
module Entry (compilerMain) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Pipeline (loadPrelude, loadModule, finalizeModule)
import CompilerContext (compilerContext)
import Control.Monad.IO.Class (liftIO)
import qualified System.FilePath as FilePath
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty
import System.Exit (exitFailure)
import qualified AST.Def as Def


compilerMain :: IO ()
compilerMain = do
  (filename, outputC, dbg) <- parseArgs

  let basePath = FilePath.takeDirectory filename
  let ctx = if dbg then Def.debugContext else Def.runtimeContext

  Def.inPrintContext ctx $ do  -- debug printing 
    prelude <- loadPrelude

    -- first, get dat prelude
    errOrModules <- compilerContext basePath prelude $ loadModule filename

    case errOrModules of
      Left errs -> liftIO $ do
        TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs
        exitFailure

      Right modules -> do
        -- TEMP: i wanna check the typechecked module.
        cmod <- finalizeModule modules

        if outputC 
          then
            liftIO $ TextIO.writeFile "test.c" cmod
          else
            liftIO $ TextIO.putStrLn cmod


parseArgs :: IO (Filename, ShouldOutputC, DebugPrinting)
parseArgs = do
  args <- getArgs
  let (mFilename, outputC, debugPrinting) = foldr (\case { "--output-c" -> \(fn, _, dbgp) -> (fn, True, dbgp); "--debug" -> \(fn, oc, _) -> (fn, oc, True); fn -> \(_, oc, dbgp) -> (Just fn, oc, dbgp) }) (Nothing, False, False) args
  pure $ case mFilename of
    Just name -> (name, outputC, debugPrinting)
    Nothing -> error "No filename provided."


type Filename = String
type ShouldOutputC = Bool
type DebugPrinting = Bool
