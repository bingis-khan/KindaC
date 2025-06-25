{-# LANGUAGE OverloadedRecordDot #-}
module Expect (expect) where

import Data.List ( isPrefixOf, find, sort )
import Data.Functor ((<&>))
import Data.Char (isSpace)
import Data.Foldable (for_)
import System.Directory (listDirectory)
import System.IO.Temp (withTempDirectory)
import Test.Hspec (parallel, hspec, it, describe, shouldBe, runIO, Expectation, expectationFailure)
import AST.Prelude (Prelude)
import Data.Text (Text)
import System.Process (readProcessWithExitCode)
import System.FilePath ((</>), takeBaseName)
import System.Exit (ExitCode(..))
import Pipeline (loadPrelude, loadModule, finalizeModule)
import qualified Data.Text.IO as TextIO
import qualified Data.Text as Text
import qualified Control.Exception as E
import Test.HUnit.Lang (HUnitFailure(HUnitFailure), FailureReason (ExpectedButGot))
import Control.Exception (catch)
import GHC.Exception (SomeException)

-- smol config
testdir :: FilePath
testdir = "test/data/expect"


expect :: IO ()
expect = do
  tests <- sort <$> listDirectory testdir
  prelude <- loadPrelude

  withTempDirectory "." "intermediate-test-outputs" $ \dir ->
    hspec $ parallel $ do
      for_ tests $ \filename -> do
        let path = testdir </> filename
        runIO $ putStrLn filename
        header <- runIO $ readHeader path
        describe (filename <?> (": " <>) <$> header.name) $ do
            errorOrFilepath <- runIO $ compileAndOutputFile prelude path dir

            it "should compile" $ do
              expectNoError errorOrFilepath

            -- TODO: I think the idiomatic way to use a lot of those is to use sstuff like beforeAll or something. Everything inside 'it' is executed in parallel, so yeh. How do I make tests depend on each other? (I mean, if I have something like beforeAll, maybe I don't need it?)
            case errorOrFilepath of
              Left _ -> pure ()  -- should be no error.
              Right cpath -> do
                let execpath = dir </> takeBaseName filename
                (exitCode, ccout, ccerr) <- runIO $ readProcessWithExitCode "cc" [cpath, "-o", execpath] ""
                it "should compile the generated C source" $ do

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
                  then fmap Just $ runIO $ readProcessWithExitCode execpath [] ""
                  else pure Nothing

                it "should not fail" $ do
                  case mresult of
                    Just (execexit, _, _) -> execexit `shouldBe` header.expectedExitCode
                    Nothing -> expectationFailure "C code not compiled."

                it "should have correct output" $ do
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
compileAndOutputFile :: Prelude -> FilePath -> FilePath -> IO (Either Error FilePath)
compileAndOutputFile prelude filepath outdirpath = do
  let compile = do
        etmod <- loadModule (Just prelude) filepath
        case etmod of
          Left err -> pure $ Left err
          Right tmod -> do
            cmod <- finalizeModule prelude tmod
            let outpath = outdirpath </> takeBaseName filepath <> ".c"
            TextIO.writeFile outpath cmod
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
      expected = trim . drop 1 <$> filter (not . (\line -> any (`isPrefixOf` line) ["#$", "#?"])) ctlLines
  in TestHeader { name = testName, expectedExitCode = exitCode, expectedOutput = expected }


intToExitCode :: Int -> ExitCode
intToExitCode 0 = ExitSuccess
intToExitCode x = ExitFailure x



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
