{-# LANGUAGE OverloadedStrings #-}

import Test.Hspec (hspec, describe, it, shouldReturn)
import Data.Text (Text)
import Data.Foldable (for_)
import System.Directory (listDirectory)



testDir :: FilePath
testDir = "test/data"

filePaths :: IO [FilePath]
filePaths = listDirectory testDir


-- Testing a single program
testProgram :: FilePath -> IO (Maybe Text)
testProgram _ = return Nothing


main :: IO ()
main = do
  paths <- filePaths
  hspec $ describe "program" $ for_ paths $ \filename -> do
    it filename $ testProgram filename `shouldReturn` Nothing
