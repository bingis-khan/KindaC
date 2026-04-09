{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module Expect (expect) where

import Assertion
import Data.List ( isPrefixOf, find, sort )
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
import Pipeline (loadPrelude, loadModule)
import Entry (defaultConfig)
import BaseCtx (withBaseContext)
import AST.Typed (topLevelStatements)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified AST.Def as Def
import AST.Def (PrintfType)
import Data.Maybe (fromMaybe, mapMaybe)
import System.Timeout (timeout)
import Data.Either (partitionEithers)
import Control.Monad (when)
import Mono (mono)
import CPrinter (cModule)

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
            (headerParseErrors, header) <- runIO $ readHeader path

            it filename $ do
              -- reporting parse errors at the start, because that's the easiest to fix.
              when (not $ null $ headerParseErrors) $ do
                expectationFailure $ unlines $
                  [ "Failed to parse some assertions, yo:"
                  ] <> map (\(og, err) -> Def.pf "Error in '%': %" og err) headerParseErrors


              let second = 1000000
              errorOrFilepath <- timeout (second `div` 2) $ compileAndOutputFile preludeAndState path dir  -- NOTE: for some reason, 'cyclic evaluation in fixio' gave way to busy looping when I moved this statement here. Timeout was added to "replace" that.

              case errorOrFilepath of
                Nothing         -> expectationFailure $ "Timeout..."
                Just (Left err) -> expectationFailure $ "Compiling error:\n" <> Text.unpack err
                Just (Right (cpath, codestate)) -> do
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
                    Just (execexit, stdout, _) -> do
                      execexit `shouldBe` header.expectedExitCode

                      lines stdout `shouldBeWithWildcard` header.expectedOutput

                    Nothing -> expectationFailure "C code not compiled."

                  -- last, check assertions about generated code
                  case mapMaybe (checkAssertion codestate) header.assertions of
                    asses@(_:_) -> expectationFailure $
                      "There were following assertion errors:\n" <> unlines (map (" - " <>) asses)
                    [] -> pure ()

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


type Error = Text
compileAndOutputFile :: (Prelude, CompilationState) -> FilePath -> FilePath -> IO (Either Error (FilePath, CodeState))
compileAndOutputFile (prelude, state) filepath outdirpath = do
  let compile = fmap fst $ withBaseContext (defaultConfig "") $ do
        let basePath = "."  -- maybe make a special testing "module" directory for testing module imports?
        etmod <- resumeModuleCtx state basePath $ loadModule (Just prelude) filepath
        case etmod of
          Left err -> pure $ Left $ Text.unlines $ NonEmpty.toList err
          Right (mods, tc) -> do
            let tmods = concat $ NonEmpty.toList $ topLevelStatements <$>  mods
            mmod <- mono tc tmods
            let cmod = cModule mmod
            let outpath = outdirpath </> takeBaseName filepath <> ".c"
            liftIO $ TextIO.writeFile outpath cmod

            let codestate = CodeState tc mods mmod
            pure $ Right (outpath, codestate)
  catch compile $ \e -> pure $ Left $ Text.pack $ "(exception)\n" <> show (e :: SomeException)



data TestHeader = TestHeader
  { name :: Maybe String
  , expectedExitCode :: ExitCode
  , expectedOutput :: [String]  -- output CAN be empty!
  , assertions :: [Assertion]
  } deriving Show

readHeader :: FilePath -> IO ([(String, AssertionParseError)], TestHeader)
readHeader path = readFile path <&> \m ->
  let ctlLines = takeWhile ("#" `isPrefixOf`) $ lines m

      testName = trim . drop 2 <$> find ("#$" `isPrefixOf`) ctlLines
      exitCode = maybe ExitSuccess ((intToExitCode . read) . trim . drop 2) $ find ("#?" `isPrefixOf`) ctlLines
      expected = trim . drop 1 <$> filter (not . (\line -> any (`isPrefixOf` line) ["#$", "#?", "#="])) ctlLines
      errOrAssertions
        = map (parseAssertion . trim . drop 2)
        $ filter ("#=" `isPrefixOf`)
          ctlLines
      (assertionErrors, assertions) = partitionEithers errOrAssertions
  in (assertionErrors, TestHeader { name = testName, expectedExitCode = exitCode, expectedOutput = expected, assertions = assertions })


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

