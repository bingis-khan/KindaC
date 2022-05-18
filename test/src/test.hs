import Test.Hspec (hspec)



data Level = Level
  { name :: String
  , paths :: [String]
  } deriving (Show, Eq, Ord)

findLevels :: IO [Level]
findLevels = return $ sort . undefined

main :: IO ()
main = hspec $ do
  undefined