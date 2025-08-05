#!/usr/bin/env runghc
{-# LANGUAGE LambdaCase #-}

import System.Environment (getArgs)
import Data.List (intercalate, sort)
import Data.Char (isAlphaNum, toLower, isSpace, isDigit)
import System.Directory (listDirectory)
import Data.Bifunctor (bimap)


main :: IO ()
main = do
  (groupId, filename, newName) <- parseArgs
  newestTestId <- getNewestTestFromGroup groupId
  let thisTestId = newestTestId + 1
  let leftPaddedTestId =  -- no need to pad it with more than one zero!
        if thisTestId < 10
          then "0" <> show thisTestId
          else show thisTestId
  let testName = show groupId <> "_t" <> leftPaddedTestId <> "_" <> newName <> ".kc"
  saveTest filename testName
  putStrLn testName

saveTest :: FilePath -> FilePath -> IO ()
saveTest fileToCopy testName = do
  contents <- readFile fileToCopy
  writeFile ("test/data/expect/" <> testName) contents

getNewestTestFromGroup :: Int -> IO Int
getNewestTestFromGroup ourGroupId = do
  dir <- listDirectory "test/data/expect"
  let groupIds = fmap (bimap read read) $ filter (not . null . snd) $ filter (not . null . fst) $ (\name -> (takeWhile isDigit name, takeWhile isDigit $ drop 2 $ dropWhile isDigit name)) <$> dir
  let ourGroup = fmap snd $ filter ((==ourGroupId) . fst) groupIds
  let highestId = take 1 $ reverse $ sort ourGroup
  pure $ case highestId of
    [] -> 0  -- when first from group, the first test will start from '1'
    x : _ -> x

parseArgs :: IO (Int, FilePath, FilePath)
parseArgs = do
  testId : filename : nameOfTest <- getArgs

  let shortenSpaces = unwords . words
  let replaceChars = \case
        c | isSpace c -> '-'
        c | isAlphaNum c -> toLower c
  let actualNameOfTest = intercalate "-" $ map replaceChars . shortenSpaces <$> nameOfTest
  pure (read testId, filename, actualNameOfTest)
