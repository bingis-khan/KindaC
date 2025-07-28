{-# LANGUAGE OverloadedRecordDot #-}
module CompilerContext (CompilerContext, CompilerState(..), BasePath, storeModule, ModuleLoader, compilerContext, addErrors, preludeHackContext, mkModulePath) where

import Data.Text (Text)
import Data.Map (Map)
import qualified AST.Untyped as U
import AST.Common (Module)
import AST.Typed (TC)
import Control.Monad.Trans.RWS (RWST)
import qualified Control.Monad.Trans.RWS as RWST
import Data.List.NonEmpty (NonEmpty (..), (<|))
import AST.Prelude (Prelude (..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map as Map
import System.FilePath ((<.>), (</>))
import qualified System.FilePath as FilePath
import qualified AST.Def as Def
import qualified Data.Text as Text



compilerContext :: BasePath -> Prelude -> CompilerContext (Maybe (Module TC)) -> IO (Either (NonEmpty Text) (NonEmpty (Module TC)))
compilerContext basepath prelude fn = fmap fst $ RWST.evalRWST go (basepath, prelude) $ CompilerState
  { errors = mempty
  , loadedModules = mempty
  , orderedModules = NonEmpty.singleton prelude.tpModule
  } where
    go :: CompilerContext (Either (NonEmpty Text) (NonEmpty (Module TC)))
    go = do
      mtmod <- fn
      errs <- RWST.gets errors
      mods <- RWST.gets orderedModules
      pure $ case mtmod of
        Just tmod ->
          case errs of
            [] -> Right $ NonEmpty.reverse $ tmod <| mods
            e:es -> Left $ e :| es

        Nothing -> do  -- module could not be compiled
          Left $ case errs of
            e:es -> e :| es
            _ -> error "[COMPILER ERROR]: no errors while module could not be compiled."


preludeHackContext :: CompilerContext a -> IO a
preludeHackContext fn = fmap fst $ RWST.evalRWST fn ("kcsrc/prelude.kc", error "no prelude") $ CompilerState
  { errors = mempty
  , loadedModules = mempty
  , orderedModules = NonEmpty.singleton (error "module")
  }


type CompilerContext = RWST (BasePath, Prelude) () CompilerState IO

type BasePath = FilePath
data CompilerState = CompilerState
  { errors :: [Text]
  , loadedModules :: ModuleStore
  , orderedModules :: NonEmpty (Module TC)  -- at the end must have at least one element.
  }

type ModuleStore = Map U.ModuleQualifier (Maybe (Module TC))
-- NOTE: the 'Maybe' here will prevent us from trying to load the module again!

type ModuleLoader = U.ModuleQualifier -> CompilerContext (Maybe (Module TC))

storeModule :: U.ModuleQualifier -> Maybe (Module TC) -> CompilerContext ()
storeModule mq mtmod = do
  RWST.modify $ \s -> s { loadedModules = Map.insert mq mtmod s.loadedModules }
  case mtmod of
    Just tmod -> RWST.modify $ \s -> s { orderedModules = tmod <| s.orderedModules }  -- we PREPEND to the list of ordered modules!
    Nothing -> pure ()

-- Right now only text geg
addErrors :: [Text] -> CompilerContext ()
addErrors errs = RWST.modify $ \s -> s { errors = s.errors <> errs }  -- we append to the end here.

mkModulePath :: U.ModuleQualifier -> CompilerContext FilePath
mkModulePath (U.ModuleQualifier modules) = do
  basePath <- RWST.asks fst
  let moduleFileNames = Text.unpack . Def.fromModName <$> NonEmpty.toList modules
  let fullpath = basePath </> FilePath.joinPath moduleFileNames <.> "kc"
  pure fullpath
