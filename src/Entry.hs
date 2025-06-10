-- This was created, because the Haskell LSP does not seem to work for app/Main.hs
{-# LANGUAGE LambdaCase #-}
module Entry (compilerMain) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Parser (parse)
import Resolver (resolve)
import qualified AST.Def as Def
import AST.Def (PP(..))
import Data.Text (Text)
import qualified Data.Text as Text
-- import Pipeline (loadPrelude, loadModule, finalizeModule)


compilerMain :: IO ()
compilerMain = do
  (filename, outputC) <- parseArgs

  -- first, get dat prelude
  -- prelude <- loadPrelude

  -- try compile module
  -- emod <- loadModule Nothing filename

  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> TextIO.putStrLn err
    Right ast -> do
      (errs, mod) <- resolve Nothing ast
      Def.ctxPrint pp mod

      
  pure ()
  -- case emod of
  --   Left errs -> TextIO.putStrLn errs
  --   Right modul -> do

  --     -- all good, finalize.
  --     cmod <- finalizeModule prelude modul

  --     if outputC 
  --       then TextIO.writeFile "test.c" cmod
  --       else TextIO.putStrLn cmod


s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)

parseArgs :: IO (Filename, ShouldOutputC)
parseArgs = do
  args <- getArgs
  let (mFilename, outputC) = foldr (\case { "--output-c" -> \(fn, _) -> (fn, True); fn -> \(_, oc) -> (Just fn, oc) }) (Nothing, False) args
  pure $ case mFilename of
    Just name -> (name, outputC)
    Nothing -> error "No filename provided."


type Filename = String
type ShouldOutputC = Bool
