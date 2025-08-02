{-# LANGUAGE OverloadedStrings, OverloadedRecordDot #-}
{-# LANGUAGE LambdaCase #-}
module Error (Error(toError), renderError) where

import Data.Text (Text)
import qualified AST.Def as Def
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Text as Text
import AST.Def (Location(startPos))
import Text.Megaparsec (SourcePos(sourceLine))
import qualified Text.Megaparsec as TM
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Char (isSpace)


class Error err where
  toError :: Text -> err -> Text

renderError :: Text -> Text -> NonEmpty (Def.Location, Maybe Text) -> Text
renderError source errorTitle errors =
  let
    items = errors <&> uncurry (errorItem source)
  in Text.unlines
   $ "error: " <> errorTitle
   : NonEmpty.toList items
    

errorItem :: Text -> Def.Location -> Maybe Text -> Text
errorItem source location comment = Text.unlines
  [ padding <> "|"
  , " " <> Text.pack (show lineNum) <> " | " <> Text.strip line
  , padding <> "| " <> errorPadding <> errorUnderline <> mComment
  ] where
    lineNum = TM.unPos location.startPos.sourceLine
    locationTextLength = length $ show lineNum
    padding = Text.replicate (locationTextLength + 2) " "  -- front + back padding

    errorPadding = Text.replicate (TM.unPos location.startPos.sourceColumn - 1 - errorPaddingRemoved) " "
    errorPaddingRemoved = Text.foldl (\s -> (+s) . spaceSize) (0 :: Int) $ Text.takeWhile isSpace line
    spaceSize = \case
      ' ' -> 1
      '\t' -> TM.unPos TM.defaultTabWidth
      _ -> undefined

    line = wholeLineAtLocation source location

    errorUnderline = Text.replicate errorLength "^"
    errorLength = location.offsetTo - location.offsetFrom

    mComment = case comment of
      Nothing -> mempty
      Just cum -> "--- " <> cum

-- NOTE: i uglified this function to try to get padding n stuff
wholeLineAtLocation :: Text -> Def.Location -> Text
wholeLineAtLocation source loc =
  fmap (snd . Text.breakOnEnd "\n" . fst) (Text.breakOnAll "\n" source) !! (TM.unPos loc.startPos.sourceLine - 1)
