{-# LANGUAGE OverloadedRecordDot, OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}
module CompilerContext (CompilerContext(..), CompilerState(..), BasePath, storeModule, ModuleLoader, compileInContext, addErrors, preludeHackContext, mkModulePath, relativeTo, prelude, asPrintContext, silentContext, nextTypeID, modifyTypeUni, modifyUniUni, nextUnionUniID, getTypeUni) where

import Data.Text (Text)
import Data.Map.Strict (Map)
import qualified AST.Untyped as U
import AST.Common (Module)
import AST.Typed (TC, T)
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWST
import Data.List.NonEmpty (NonEmpty (..), (<|))
import AST.Prelude (Prelude (..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict as Map
import System.FilePath ((<.>), (</>))
import qualified System.FilePath as FilePath
import qualified AST.Def as Def
import qualified Data.Text as Text
import AST.Def (PrintContext (..), pc, vsep, pp, ppLines)
import Control.Monad.IO.Class (liftIO, MonadIO)
import qualified Control.Monad.Trans.Reader as Reader
import Control.Monad (unless)
import qualified Data.Text.IO as TextIO
import Control.Monad.Fix (MonadFix)
import qualified AST.Typed as T
import TypeFix (typefix)



-- I cannot put this in Def, because it accesses other AST modules.


compileInContext :: BasePath -> (Prelude, CompilerState) -> CompilerContext (Maybe (Module TC)) -> PrintContext (Either (NonEmpty Text) (Module T))
compileInContext bejspaf (prilud, ps) fn = do

  
  ctxdata <- PrintContext Reader.ask
  fmap fst $ liftIO $ RWST.evalRWST (fromCompilerContext go) (CCC { basepath = bejspaf, prelude = prilud, printContext = ctxdata }) $ CompilerState
    { errors = mempty
    , globalTypeIDGen = ps.globalTypeIDGen
    , globalUnionIDGen = ps.globalUnionIDGen

    , globalTypeUni = ps.globalTypeUni
    , globalEnvAddition = ps.globalEnvAddition

    , loadedModules = mempty
    , orderedModules = NonEmpty.singleton prilud.tpModule
    }
    where

    go :: CompilerContext (Either (NonEmpty Text) (Module T))
    go = do
      mtmod <- fn
      errs <- CompilerContext $ RWST.gets errors
      mods <- CompilerContext $ RWST.gets orderedModules
      case mtmod of
        Just tmod ->
          case errs of
            [] -> do
              typeUni <- CompilerContext $ RWST.gets globalTypeUni
              envAdds <- CompilerContext $ RWST.gets globalEnvAddition
              let tcmods = NonEmpty.reverse $ tmod <| mods
              tm <- CompilerContext.asPrintContext $ typefix typeUni envAdds tcmods
              pc $ ppLines tm
              pure $ Right tm

            e:es -> pure $ Left $ e :| es

        Nothing ->  -- module could not be compiled
          pure $ Left $ case errs of
            e:es -> e :| es
            _ -> error "[COMPILER ERROR]: no errors but module could not be compiled."


relativeTo :: BasePath -> CompilerContext a -> CompilerContext a
relativeTo newBasePath = CompilerContext . RWST.local (\ccc ->
  ccc { basepath = newBasePath }) . fromCompilerContext

preludeHackContext :: CompilerContext a -> PrintContext (a, CompilerState)
preludeHackContext fn = do
  ctxData <- PrintContext Reader.ask
  let ccc = CCC
        { basepath = "/home/bob/prj/KindaC/kcsrc/prelude.kc"  -- HACK: im testing the standalone executable. quick hack to get all the source files.
        , prelude = error "tried to access prelude WHILE parsing prelude."
        , printContext = ctxData
        }
  liftIO $ do
    (pmod, s, ()) <- RWST.runRWST (fromCompilerContext fn) ccc $ CompilerState
      { errors = mempty
      , globalTypeIDGen = TypeIDGen $ T.TypeID 0
      , globalTypeUni = T.TypeUni mempty mempty
      , globalUnionIDGen = UnionIDGen $ T.UnionUniID 0
      , globalEnvAddition = mempty
      , loadedModules = mempty
      , orderedModules = NonEmpty.singleton (error "module")
      }
    pure (pmod, s)

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

  -- for efficient typechecking
  , globalTypeIDGen :: TypeIDGen
  , globalUnionIDGen :: UnionIDGen
  , globalTypeUni :: T.TypeUni
  , globalEnvAddition :: T.EnvAdditions

  , loadedModules :: ModuleStore
  , orderedModules :: NonEmpty (Module TC)  -- at the end must have at least one element.
  }

type ModuleStore = Map U.ModuleQualifier (Maybe (Module TC))
-- NOTE: the 'Maybe' here will prevent us from trying to load the module again!

type ModuleLoader = U.ModuleQualifier -> CompilerContext (Maybe (Module TC))


newtype TypeIDGen = TypeIDGen T.TypeID

nextTypeID :: CompilerContext T.TypeID
nextTypeID = do
  TypeIDGen tid@(T.TypeID x) <- CompilerContext $ RWST.gets globalTypeIDGen
  CompilerContext $ RWST.modify $ \s ->
    let TypeIDGen (T.TypeID xx) = s.globalTypeIDGen
    in s { globalTypeIDGen = TypeIDGen $ T.TypeID $ xx + 1 }
  pure tid


newtype UnionIDGen = UnionIDGen T.UnionUniID

nextUnionUniID :: CompilerContext T.UnionUniID
nextUnionUniID = do
  UnionIDGen uid@(T.UnionUniID x) <- CompilerContext $ RWST.gets globalUnionIDGen
  CompilerContext $ RWST.modify $ \s -> s { globalUnionIDGen = UnionIDGen $ T.UnionUniID $ x + 1 }
  pure uid


getTypeUni :: CompilerContext T.TypeUni
getTypeUni = CompilerContext $ RWST.gets globalTypeUni


-- modify type unions
modifyTypeUni :: (T.TypeTypeUni -> T.TypeTypeUni) -> CompilerContext ()
modifyTypeUni f = 
  CompilerContext $ RWST.modify $ \s -> s { globalTypeUni = s.globalTypeUni { T.typeUni = f s.globalTypeUni.typeUni } }

-- modify env unions
modifyUniUni :: (T.UnionTypeUni -> T.UnionTypeUni) -> CompilerContext ()
modifyUniUni f = CompilerContext $ RWST.modify $ \s -> s { globalTypeUni = s.globalTypeUni { T.unionUni = f s.globalTypeUni.unionUni } }


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
