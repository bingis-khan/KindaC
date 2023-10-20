{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections #-}
{-# LANGUAGE EmptyCase #-}

import Test.Hspec (hspec, describe, it, shouldBe, Spec, Expectation, expectationFailure)
import Data.Text (Text)
import Data.Foldable (for_, fold)
import System.Directory (listDirectory)
import AST (Untyped, TopLevel, StmtF (FunctionDefinition, DataDefinition), Stmt, GDataDef (DD))
import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import Data.Maybe (mapMaybe, listToMaybe)
import Data.Fix (Fix(Fix))
import Parser (parse)
import Debug.Trace (traceShowId)
import Data.Functor.Foldable (cata, para)
import Data.Monoid (Sum(..))



testDir :: FilePath
testDir = "test/data"

filePaths :: IO [FilePath]
filePaths = listDirectory testDir


main :: IO ()
main = do
  paths <- filePaths
  files <- traverse (\fn -> (fn,) <$> TextIO.readFile (testDir <> "/" <> fn)) paths-- Right now, I don't know how to load a file before every spec (so that for every 'it', it would use the same file), so I'll just load em before.
  hspec $ for_ files testFile



testFile :: (FilePath, Source) -> Spec
testFile (filename, file) = describe filename $ do
  let res = compile filename file
  it "whole file" $ do
    let maybeError = eitherToMaybe res
    case maybeError of
      Nothing -> return ()
      Just err -> expectationFailure $ Text.unpack err

  case res of
    Left _ -> return ()
    Right res -> do
      -- Only run tests after a properly compiled code
      let additionalSpecs = findSpecs file
      for_ additionalSpecs $ \spec ->
        it (specLabel spec) $ testSpec spec res



-- This is the resulting type of the compilation. Will be changed after I add more phases
type Source = Text
type Result = TopLevel Untyped

-- This should be changed as the result get's changed
compile :: FilePath -> Source -> Either Text Result
compile = parse

testSpec :: AdditionalSpec -> Result -> Expectation
testSpec (InvalidSpec _ _) _ = expectationFailure "Invalid spec"
testSpec (Functions num) stmts =
  let numOfFunctions = countStatements (\case { FunctionDefinition _ _ -> True; _ -> False }) stmts
  in fromIntegral numOfFunctions `shouldBe` num

testSpec (TopLevelStatements num) stmts =
  let numOfTLStmts = length stmts
  in fromIntegral numOfTLStmts `shouldBe` num

testSpec (DataDefinitions num) stmts =
  let numOfDDs = countStatements (\case { DataDefinition _ -> True; _ -> False }) stmts
  in fromIntegral numOfDDs `shouldBe` num
testSpec (DataConstructors name num) stmts = 
  let firstDDWithName = listToMaybe $ mapMaybe (\case { Fix (DataDefinition (DD ddname _ cons)) | ddname == name -> Just (length cons); _ -> Nothing }) $ streamStatements stmts
  in case firstDDWithName of
    Nothing -> expectationFailure $ Text.unpack $ "No Datatype with name \"" <> name <> "\""
    Just num' -> fromIntegral num' `shouldBe` num

streamStatements :: Result -> [Stmt Untyped]
streamStatements = concatMap cat
  where
    cat :: Stmt Untyped -> [Stmt Untyped]
    cat s@(Fix s') = [s] <> foldMap (:[]) s'

countStatements f = getSum . foldMap cat
  where
    cat :: Stmt Untyped -> Sum Int
    cat = cata $ \s -> if f s
        then Sum (1 :: Int) <> fold s
        else fold s



findSpecs :: Source -> [AdditionalSpec]
findSpecs = mapMaybe (parseSpec . Text.stripStart . Text.drop 1 . Text.strip) . takeWhile ((=="#") . Text.take 1 . Text.stripStart) . dropWhile (Text.null . Text.strip) . Text.lines

parseSpec :: Text -> Maybe AdditionalSpec
parseSpec line =
  let (pre, post') = Text.break (==':') line
      post = Text.stripStart $ Text.drop 1 post'
      tread = read . Text.unpack
  in if Text.null post
    then Nothing
    else Just $ case pre of
      "functions" -> Functions (tread post)
      "top level statements" -> TopLevelStatements (tread post)
      "data definitions" -> DataDefinitions (tread post)
      "data constructors" ->
        let [dt, amt] = Text.words post
        in DataConstructors dt (tread amt)
      s -> InvalidSpec s post


specLabel :: AdditionalSpec -> String
specLabel (Functions _) = "functions"
specLabel (TopLevelStatements _) = "top level statements"
specLabel (DataDefinitions _) = "data definitions"
specLabel (DataConstructors name _) = Text.unpack $ "data constructors of " <> name
specLabel (InvalidSpec name value) = Text.unpack $ "Invalid Spec (" <> name <> ": " <> value <> ")"

data AdditionalSpec
  = InvalidSpec Text Text
  | Functions Word
  | TopLevelStatements Word
  | DataDefinitions Word
  | DataConstructors Text Word



-- Utils
eitherToMaybe :: Either a b -> Maybe a
eitherToMaybe (Left a) = Just a
eitherToMaybe (Right _) = Nothing