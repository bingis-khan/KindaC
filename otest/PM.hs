module PM (main) where

import Data.List (intercalate, partition)
import Data.Functor ((<&>))
import Data.Maybe (listToMaybe)
import Data.Bifunctor (first)
import Data.Map (Map)

unit :: String -> CaseMatch
unit s = Con s []

match :: Match
match = Match $ zipWith (\label kase -> Case kase ("e" <> show label)) [1..]
  [ Con "Add" [ unit "Zero", unit "Zero" ]
  , Con "Mul" [ unit "Zero", Var "x" ]
  , Con "Add" [ Con "Succ" [Var "x"], Var "y" ]
  , Con "Mul" [ Var "x", unit "Zero" ]
  , Con "Mul" [ Con "Add" [ Var "x", Var "y" ], Var "z" ]
  , Con "Add" [ Var "x", unit "Zero" ]
  , Var "x"
  ]

main :: IO ()
main = do
  print match
  let (Match kases) = match
  let (_, _, selecteds) = sortByConAndEliminateUnreachable kases
  putStrLn $ unlines $ map show selecteds
  putStrLn "Dupsko"


data Selected
  = Selected
    { con :: String
    , cases :: [([CaseMatch], String)]
    }
instance Show Selected where
  show (Selected con kases) = ((con <> "\n") <>) $ unlines $ map (\(cases, label) -> (("  " <>) $ ("("<>) $ (<>")") $ intercalate ", " $ map show cases) <> "                  -> " <> label) kases

sortByConAndEliminateUnreachable :: [Case] -> ([Case], Maybe (Variable, Label), [Selected])
sortByConAndEliminateUnreachable cases =
  let 
    go ((Case (Con name submatches) label) : cases) = go cases <&> \sels ->
      let (mSel, others) = first listToMaybe $ partition (\(Selected con _) -> con == name) sels
      in case mSel of
        Nothing -> Selected name [(submatches, label)] : sels
        Just (Selected con kases) -> Selected con ((submatches, label) : kases) : others
    go ((Case (Var x) label) : cases) = (cases, Just (x, label), [])
    go [] = ([], Nothing, [])

  in go cases


parseCases :: Match -> PCase
parseCases (Match cases) = case cases of
  -- case 2
  cases | all (isVar . caseMatch) cases -> undefined

  -- case 3
  cases | all (isVar . caseMatch) cases -> undefined

  -- case 4
  cases | all (isVar . caseMatch) cases -> undefined

isCase3 :: [Case] -> Maybe (Map Constructor [(CaseMatch, ())])
isCase3 = undefined


data Match = Match [Case] deriving Eq
instance Show Match where
  show (Match cases) = ("match\n" <>) $ unlines $ map (("  " <>) . show) cases

data Case = Case
  { caseMatch :: CaseMatch
  , label :: Label
  } deriving Eq
instance Show Case where
  show (Case kasem label) = "| " <> show kasem <> "                           -> " <> label

data CaseMatch
  = Var Variable
  | Con Constructor [CaseMatch]
  deriving Eq
instance Show CaseMatch where
  show (Var var) = var
  show (Con name []) = name
  show (Con name (x:xs)) = name <> "(" <> intercalate ", " (map show (x:xs)) <> ")"

type Variable = String
type Label = String
type Constructor = String


---- PARSED

data PCase
  = Case1 Label
  | Case2 Variable PCase
  | Case3 (Map Constructor [([Variable], PCase)]) PCase
  | Case4 [(Map Constructor [([Variable], PCase)], PCase)]
