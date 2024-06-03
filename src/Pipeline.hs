module Pipeline (loadModule, dbgLoadModule) where

import AST (Module, Typed, Prelude)
import qualified Data.Text.IO as TextIO
import Parser (parse)
import Resolver (resolve)
import Typecheck (typecheck, dbgTypecheck)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty
import ASTPrettyPrinter (tModule, rModule)


-- Loads and typechecks a module.
--   TODO: WRT errors: I should probably make a type aggregating all the different types of errors and put it in AST.hs.
--   However, right now, I can just turn them into strings. THIS IS TEMPORARY.
loadModule :: Maybe Prelude -> FilePath -> IO (Either Text (Module Typed))
loadModule mPrelude filename = do
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> pure $ Left err
    Right ast -> do
      (errs, rmod) <- resolve mPrelude ast

      let mtmod = typecheck mPrelude rmod
      case mtmod of
        Left tes -> 
          let errors = (s2t errs ++) $ NonEmpty.toList $ s2t tes
          in pure $ Left $ Text.unlines errors

        Right _ | (not . null) errs -> pure $ Left $ Text.unlines $ s2t errs
        Right tmod -> pure $ Right tmod

dbgLoadModule :: Maybe Prelude -> FilePath -> IO Text
dbgLoadModule mPrelude filename = do
  source <- TextIO.readFile filename
  case parse filename source of
    Left err -> pure err
    Right ast -> do
      (rerrs, rmod) <- resolve mPrelude ast
      print rerrs
      putStrLn $ rModule rmod

      let (terrs, tmod) = dbgTypecheck mPrelude rmod
      let errors = s2t rerrs ++ s2t terrs
      pure $ Text.unlines
        [ Text.unlines errors
        , Text.empty
        , Text.pack $ tModule tmod
        ]


s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)
