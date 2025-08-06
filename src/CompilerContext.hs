{-# LANGUAGE OverloadedRecordDot, OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module CompilerContext (CompilerContext(..), CompilerState(..), BasePath, storeModule, ModuleLoader, compilerContext, addErrors, preludeHackContext, mkModulePath, relativeTo, prelude, asPrintContext, silentContext) where

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
import AST.Def (PrintContext (..))
import Control.Monad.IO.Class (liftIO, MonadIO)
import qualified Control.Monad.Trans.Reader as Reader
import Control.Monad (unless)
import qualified Data.Text.IO as TextIO
import Control.Monad.Fix (MonadFix)



-- I cannot put this in Def, because it accesses other AST modules.


compilerContext :: BasePath -> Prelude -> CompilerContext (Maybe (Module TC)) -> PrintContext (Either (NonEmpty Text) (NonEmpty (Module TC)))
compilerContext bejspaf prilud fn = do
  ctxdata <- PrintContext Reader.ask
  fmap fst $ liftIO $ RWST.evalRWST (fromCompilerContext go) (CCC { basepath = bejspaf, prelude = prilud, printContext = ctxdata }) $ CompilerState
    { errors = mempty
    , loadedModules = mempty
    , orderedModules = NonEmpty.singleton prilud.tpModule
    } where
    go :: CompilerContext (Either (NonEmpty Text) (NonEmpty (Module TC)))
    go = do
      mtmod <- fn
      errs <- CompilerContext $ RWST.gets errors
      mods <- CompilerContext $ RWST.gets orderedModules
      pure $ case mtmod of
        Just tmod ->
          case errs of
            [] -> Right $ NonEmpty.reverse $ tmod <| mods
            e:es -> Left $ e :| es

        Nothing -> do  -- module could not be compiled
          Left $ case errs of
            e:es -> e :| es
            _ -> error "[COMPILER ERROR]: no errors but module could not be compiled."


relativeTo :: BasePath -> CompilerContext a -> CompilerContext a
relativeTo newBasePath = CompilerContext . RWST.local (\ccc ->
  ccc { basepath = newBasePath }) . fromCompilerContext

preludeHackContext :: CompilerContext a -> PrintContext a
preludeHackContext fn = do
  ctxData <- PrintContext Reader.ask
  let ccc = CCC
        { basepath = "/home/bob/prj/KindaC/kcsrc/prelude.kc"  -- HACK: im testing the standalone executable. quick hack to get all the source files.
        , prelude = error "tried to access prelude WHILE parsing prelude."
        , printContext = ctxData
        }
  fmap fst $ liftIO $ RWST.evalRWST (fromCompilerContext fn) ccc $ CompilerState
    { errors = mempty
    , loadedModules = mempty
    , orderedModules = NonEmpty.singleton (error "module")
    }

-- ahmahgad, this is so SHIT.
asPrintContext :: PrintContext a -> CompilerContext a
asPrintContext pc = do
  ctxdata <- CompilerContext $ RWST.asks printContext
  liftIO $ Reader.runReaderT (fromPrintContext pc) ctxdata

silentContext :: CompilerContext a -> CompilerContext a
silentContext = CompilerContext . RWST.local (\c -> c { printContext = Def.runtimeContext }) . fromCompilerContext


newtype CompilerContext a = CompilerContext { fromCompilerContext :: RWST CCConfig () CompilerState IO a } deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadFix)

instance (a ~ ()) => Def.PrintableContext (CompilerContext a) where
  printInContext c = do
    ctxData <- CompilerContext $ RWST.asks printContext

    unless ctxData.silent $
      liftIO $ TextIO.putStrLn $ Def.ctx ctxData c

  -- should later be replaced by more granular printing configuration!
  unsilenceablePrintInContext c = do
      ctxData <- CompilerContext $ RWST.asks printContext
      liftIO $ TextIO.putStrLn $ Def.ctx ctxData c

data CCConfig = CCC
  { basepath :: BasePath
  , prelude :: Prelude
  , printContext :: Def.CtxData
  }

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
  CompilerContext $ RWST.modify $ \s -> s { loadedModules = Map.insert mq mtmod s.loadedModules }
  case mtmod of
    Just tmod -> CompilerContext $ RWST.modify $ \s -> s { orderedModules = tmod <| s.orderedModules }  -- we PREPEND to the list of ordered modules!
    Nothing -> pure ()

-- Right now only text geg
-- its all kinda crappy.
--   i want to be able to count the total amount of errors n shi
addErrors :: Text -> [Text] -> CompilerContext ()
addErrors _ [] = pure ()
addErrors moduleName errs = CompilerContext $ RWST.modify $ \s -> s { errors = s.errors <> (("Errors in module " <> moduleName <> ":") : errs) }  -- we append to the end here.

mkModulePath :: U.ModuleQualifier -> CompilerContext FilePath
mkModulePath (U.ModuleQualifier modules) = do
  basePath <- CompilerContext $ RWST.asks $ \ccc -> ccc.basepath
  let moduleFileNames = Text.unpack . Def.fromModName <$> NonEmpty.toList modules
  let fullpath = basePath </> FilePath.joinPath moduleFileNames <.> "kc"
  pure fullpath
