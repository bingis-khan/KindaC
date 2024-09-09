module Pipeline (loadModule) where

import qualified Data.Text.IO as TextIO
import Parser (parse)
import Resolver (resolve)
import Typecheck (typecheck)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty

import AST.Converged (Prelude)
import AST.Common (Module)
import AST.Typed (Typed)
-- import ASTPrettyPrinter (tModule, rModule, mModule)
-- import Mono (monoModule)



compile :: Prelude -> Module Typed -> IO Text
compile prelude mod = do
  undefined

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

      mtmod <- typecheck mPrelude rmod
      case mtmod of
        Left tes -> 
          let errors = (s2t errs ++) $ NonEmpty.toList $ s2t tes
          in pure $ Left $ Text.unlines errors

        Right _ | (not . null) errs -> pure $ Left $ Text.unlines $ s2t errs
        Right tmod -> pure $ Right tmod

-- dbgLoadModule :: Maybe Prelude -> FilePath -> IO Text
-- dbgLoadModule mPrelude filename = do
--   source <- TextIO.readFile filename
--   case parse filename source of
--     Left err -> pure err
--     Right ast -> do
--       (rerrs, rmod) <- resolve mPrelude ast
--       print rerrs
--       putStrLn $ rModule rmod

--       let (terrs, tmod) = dbgTypecheck mPrelude rmod
--       let errors = s2t rerrs ++ s2t terrs

--       case errors of
--         [] -> do
--           putStrLn $ tModule tmod

--           case mPrelude of
--             Just prelude -> do
--               mmod <- monoModule prelude tmod
--               pure $ Text.pack $ mModule mmod

--             Nothing -> pure mempty

--         _ -> pure $ Text.unlines
--           [ Text.unlines errors
--           , Text.empty
--           , Text.pack $ tModule tmod
--           ]


s2t :: (Functor f, Show a) => f a -> f Text
s2t = fmap (Text.pack . show)
