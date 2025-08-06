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
  (filename, outputC, dbg, dbgModule) <- parseArgs

  let basePath = FilePath.takeDirectory filename
  let ctx = if dbg || dbgModule then Def.debugContext else Def.runtimeContext

  Def.inPrintContext ctx $ do  -- debug printing 
    prelude <- loadPrelude

    -- first, get dat prelude
    errOrModules <- compilerContext basePath prelude $ loadModule dbgModule filename

    case errOrModules of
      Left errs -> liftIO $ do
        TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs
        exitFailure

      Right modules -> do
        -- TEMP: i wanna check the typechecked module.
        cmod <- Def.localPrintContext (if dbgModule then Def.debugContext else Def.runtimeContext) $ finalizeModule modules

        if outputC 
          then
            liftIO $ TextIO.writeFile "test.c" cmod
          else
            liftIO $ TextIO.putStrLn cmod


parseArgs :: IO (Filename, ShouldOutputC, DebugPrinting, DebugPrintOnlyFirstModule)
parseArgs = do
  args <- getArgs
  let findArg = \case
        "--output-c" -> \(fn, _, dbgp, dbgm) -> (fn, True, dbgp, dbgm)
        "--debug" -> \(fn, oc, _, dbgm) -> (fn, oc, True, dbgm)
        "--print-current" -> \(fn, oc, dbgp, _) -> (fn, oc, dbgp, True)
        filename -> \(_, oc, dbgp, dbgm) -> (Just filename, oc, dbgp, dbgm)
  let (mFilename, outputC, debugPrinting, debugPrintFirstModule) = foldr findArg (Nothing, False, False, False) args
  pure $ case mFilename of
    Just name -> (name, outputC, debugPrinting, debugPrintFirstModule)
    Nothing -> error "No filename provided."


type Filename = String
type ShouldOutputC = Bool
type DebugPrinting = Bool
type DebugPrintOnlyFirstModule = Bool
