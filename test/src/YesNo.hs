module YesNo (yesno) where
import Test.Hspec (hspec, describe, parallel, it, runIO, shouldReturn, shouldSatisfy)
import System.Directory (listDirectory)
import Data.Foldable (for_)
import Data.Maybe (listToMaybe, isJust)
import Pipeline (loadModule)
import Std (preparePrelude)
import AST.Converged (Prelude)
import Data.Either (isRight)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import Control.Monad (when)
import Data.Char (isSpace)


yespath, nopath :: FilePath
yespath = "test/data/yesno/yes"
nopath = "test/data/yesno/no"

yesno :: IO ()
yesno = do
  yesnames <- listDirectory yespath
  nonames <- listDirectory nopath
  prelude <- preparePrelude

  hspec $ parallel $ do
    describe "Programs that should compile OK" $ do
      for_ yesnames $ \filename -> do
        let path = yespath <> "/" <> filename

        label <- runIO $ readLabel path
        it (mkLabel filename label) $ do
          label `shouldSatisfy` isJust
          compile prelude path `shouldReturn` True

    describe "Programs that should fail" $ do
      for_ nonames $ \filename -> do
        let path = nopath <> "/" <> filename

        label <- runIO $ readLabel path
        it (mkLabel filename label) $ do
          label `shouldSatisfy` isJust -- this is an error in the definition of the test
          compile prelude path `shouldReturn` False

mkLabel :: FilePath -> Maybe String -> String
mkLabel path Nothing = path
mkLabel path (Just label) = path <> ": " <> label

readLabel :: FilePath -> IO (Maybe String)
readLabel path = readFile path <&> \m -> do
  firstLine <- listToMaybe $ lines m
  if "#" `isPrefixOf` firstLine
    then Just $ trim $ tail firstLine
    else Nothing

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

compile :: Prelude -> FilePath -> IO Bool
compile prelude path = isRight <$> loadModule (Just prelude) path
