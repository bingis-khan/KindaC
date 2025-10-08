{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module Expect (expect) where

import Data.List ( isPrefixOf, find, sort, sortBy )
import Data.Functor ((<&>))
import Data.Char (isSpace, isDigit)
import Data.Foldable (for_)
import System.Directory (listDirectory)
import System.IO.Temp (withTempDirectory)
import Test.Hspec (parallel, hspec, it, describe, shouldBe, runIO, Expectation, expectationFailure)
import AST.Prelude (Prelude)
import Data.Text (Text)
import System.Process (readProcessWithExitCode)
import System.FilePath ((</>), takeBaseName)
import System.Exit (ExitCode(..))
-- import Pipeline (loadPrelude, loadModule, finalizeModule)
import qualified Data.Text.IO as TextIO
import qualified Data.Text as Text
import qualified Control.Exception as E
import Test.HUnit.Lang (HUnitFailure(HUnitFailure), FailureReason (ExpectedButGot))
import Control.Exception (catch)
import GHC.Exception (SomeException)
import qualified Data.List.NonEmpty as NonEmpty
import Control.Monad.IO.Class (liftIO)
import InterModular (CompilationState, runModuleCtx, resumeModuleCtx)
import Pipeline (loadPrelude, loadModule, codegen)
import Entry (defaultConfig)
import TypingContext (TypingContext(..), globalTypeUni)
import BaseCtx (withBaseContext)
import Lens.Micro ((^.))
import AST.Typed (topLevelStatements)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified AST.Def as Def
import AST.Def (PrintfType)
import Data.Maybe (fromMaybe)
import System.Timeout (timeout)

-- smol config
testdir :: FilePath
testdir = "test/data/expect"

pf :: PrintfType r => String -> r
pf = Def.pf


expect :: IO ()
expect = do
  tests <- toPhases <$> listDirectory testdir
  (preludeAndState, _) <- withBaseContext (defaultConfig "") $ runModuleCtx "" loadPrelude

  withTempDirectory "." "intermediate-test-outputs" $ \dir ->
    hspec $ parallel $ do
      for_ tests $ \(mphase, filenames) -> do
        let phase = fromMaybe "other" (Def.pp <$> mphase)
        let desc = Map.findWithDefault "<description not provided>" mphase phaseNames
        describe (pf "%: %" phase desc) $ do
          for_ filenames $ \filename -> do
            let path = testdir </> filename
            header <- runIO $ readHeader path

            it filename $ do
              let second = 1000000
              errorOrFilepath <- timeout (second `div` 2) $ compileAndOutputFile preludeAndState path dir  -- NOTE: for some reason, 'cyclic evaluation in fixio' gave way to busy looping when I moved this statement here. Timeout was added to "replace" that.

              -- TODO: I think the idiomatic way to use a lot of those is to use sstuff like beforeAll or something. Everything inside 'it' is executed in parallel, so yeh. How do I make tests depend on each other? (I mean, if I have something like beforeAll, maybe I don't need it?)
              case errorOrFilepath of
                Nothing         -> expectationFailure $ "Timeout..."
                Just (Left err) -> expectationFailure $ "Compiling error:\n" <> Text.unpack err
                Just (Right cpath) -> do
                  let execpath = dir </> takeBaseName filename
                  (exitCode, ccout, ccerr) <- readProcessWithExitCode "cc" [cpath, "-o", execpath] ""

                  case exitCode of
                    ExitSuccess -> pure ()
                    ExitFailure i -> expectationFailure
                      $ "cc exited with code " <> show i <> ".\n"
                      <> "stdout:\n"
                      <> ccout
                      <> "\n"
                      <> "stderr:\n"
                      <> ccerr

                  -- kinda weird, make it look better (the idea is to make all tests visible. this should be fixed if you do the previously mentioned beforeAll stuff.)
                  mresult <- if exitCode == ExitSuccess
                    then fmap Just $ readProcessWithExitCode execpath [] ""
                    else pure Nothing

                  case mresult of
                    Just (execexit, _, _) -> execexit `shouldBe` header.expectedExitCode
                    Nothing -> expectationFailure "C code not compiled."

                  case mresult of
                    Just (_, stdout, _) -> lines stdout `shouldBeWithWildcard` header.expectedOutput
                    Nothing -> expectationFailure "C code not compiled."

                  return ()


shouldBeWithWildcard :: [String] -> [String] -> Expectation
shouldBeWithWildcard is expected =
  let
    wildcard = "\\*"
    wildlen = length wildcard
    allmatch = all (\(lineis, lineexpected) ->
        if lineexpected `endsWith` wildcard
          then lineis `startsWith` trim (dropEnd wildlen lineexpected)  -- drop, because we have to drop the wildcard
          else lineis == lineexpected) (zipPad is expected)
  in if allmatch
    then pure ()
    else do
      -- expectationFailure $ show $ (\(l, r) -> (l, trim (dropEnd wildlen r))) <$> zipPad is expected
      E.throwIO (HUnitFailure Nothing $ ExpectedButGot Nothing (unlines expected) (unlines is))


expectNoError :: Either Error a -> Expectation
expectNoError (Right _) = pure ()
expectNoError (Left err) = expectationFailure $ "Compiling error:\n" <> Text.unpack err


type Error = Text
compileAndOutputFile :: (Prelude, CompilationState) -> FilePath -> FilePath -> IO (Either Error FilePath)
compileAndOutputFile (prelude, state) filepath outdirpath = do
  let compile = fmap fst $ withBaseContext (defaultConfig "") $ do
        let basePath = "."  -- maybe make a special testing "module" directory for testing module imports?
        etmod <- resumeModuleCtx state basePath $ loadModule (Just prelude) filepath
        case etmod of
          Left err -> pure $ Left $ Text.unlines $ NonEmpty.toList err
          Right (mods, tc) -> do
            let tmods = concat $ NonEmpty.toList $ topLevelStatements <$>  mods
            cmod <- codegen tc tmods
            let outpath = outdirpath </> takeBaseName filepath <> ".c"
            liftIO $ TextIO.writeFile outpath cmod
            pure $ Right outpath
  catch compile $ \e -> pure $ Left $ Text.pack $ "(exception)\n" <> show (e :: SomeException)



data TestHeader = TestHeader
  { name :: Maybe String
  , expectedExitCode :: ExitCode
  , expectedOutput :: [String]  -- output CAN be empty!
  } deriving Show

readHeader :: FilePath -> IO TestHeader
readHeader path = readFile path <&> \m ->
  let ctlLines = takeWhile ("#" `isPrefixOf`) $ lines m

      testName = trim . drop 2 <$> find ("#$" `isPrefixOf`) ctlLines
      exitCode = maybe ExitSuccess ((intToExitCode . read) . trim . drop 2) $ find ("#?" `isPrefixOf`) ctlLines
      expected = trim . drop 1 <$> filter (not . (\line -> any (`isPrefixOf` line) ["#$", "#?", "#="])) ctlLines
  in TestHeader { name = testName, expectedExitCode = exitCode, expectedOutput = expected }


intToExitCode :: Int -> ExitCode
intToExitCode 0 = ExitSuccess
intToExitCode x = ExitFailure x


type Phase = Int
toPhases :: [FilePath] -> [(Maybe Phase, [FilePath])]
toPhases
  = Map.toList  -- map has a defined "sorted" order.
  . fmap sort
  . Map.fromListWith (<>)
  . map (\s -> (tryParseNum (takeWhile isDigit s), [s]))
  . sort

tryParseNum :: [Char] -> Maybe Int
tryParseNum = \case
  [] -> Nothing
  xs -> Just (read xs)

phaseNames :: Map (Maybe Phase) String
phaseNames = Map.fromList
  [ (Just 0, "Parsing")
  , (Just 1, "General")
  , (Just 2, "Function Datatypes")
  , (Just 3, "Datatypes")
  , (Just 4, "Records")
  , (Just 5, "Typeclasses")
  , (Just 6, "Pointers")
  , (Just 7, "Full")
  , (Nothing, "Others")
  ]


trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

zipPad :: (Monoid a, Monoid b) => [a] -> [b] -> [(a, b)]
zipPad [] [] = []
zipPad (l:ls) [] = (l, mempty) : zipPad ls []
zipPad [] (r:rs) = (mempty, r) : zipPad [] rs
zipPad (l:ls) (r:rs) = (l, r) : zipPad ls rs

startsWith :: String -> String -> Bool
startsWith base ending = all (uncurry (==)) $ zip base ending

endsWith :: String -> String -> Bool
endsWith base ending | length base < length ending = False
endsWith base ending =
  all (uncurry (==)) $ zip (reverse base) (reverse ending)

dropEnd :: Int -> [a] -> [a]
dropEnd len = reverse . drop len . reverse


infixl 3 <?>
(<?>) :: String -> Maybe String -> String
(<?>) s Nothing = s
(<?>) s (Just rs) = s <> rs
