{-# LANGUAGE OverloadedRecordDot, OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- should join pipeline and 
module InterModular (module InterModular) where

import AST.Def (TypeID, UnionUniID, Log (plog), Context, typingContext, PrintfType)
import Data.Text (Text)
import Data.Map (Map, (!?))
import qualified AST.Untyped as U
import AST.Common (Module, Function, FunDec (functionId, functionOther))
import AST.Typed (TC, FunOther (functionScheme), Scheme (Scheme))
import Data.List.NonEmpty (NonEmpty ((:|)))
import TypingContext (globalTypeUni, TypingContext)
import qualified TypingContext as TC
import Control.Monad.Trans.RST (RST)
import qualified Control.Monad.Trans.RST as RST
import Data.Functor ((<&>))
import Control.Monad.Trans.Class (lift)
import Stats (FunInstTrack(..), numLoadedModules, numCreatedTypes, numCreatedUnions)
import qualified AST.Def as Def
import AST.Common (Function(functionDeclaration))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader(local))
import Control.Monad.Fix (MonadFix)
import Lens.Micro.Mtl ((.=), (%=), use)
import Lens.Micro.TH (makeLenses)
import Control.Monad.RWS (MonadState)
import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NonEmpty
import Lens.Micro ((&), (^.))
import Control.Monad (join)
import System.FilePath ((</>), (<.>))
import qualified Data.Text as Text
import qualified System.FilePath as FilePath
import qualified System.Directory as Directory
import qualified Data.Set as Set
import BaseCtx (BaseCtx, countUp, trackInstantiation)


-- handles:
--  - module loading and cache
--  - global typing context
--  - errors

newtype InterModular a = IM { fromIM :: RST Constants CompilationState BaseCtx a } deriving (Functor, Applicative, Monad, MonadIO, MonadFail, MonadFix, MonadReader Constants, MonadState CompilationState)

type BasePath = FilePath  -- base filepath for loading modules.
type Loader = U.ModuleQualifier -> InterModular (Maybe (Module TC))

data Constants = Constants
  { basepath :: BasePath
  }

data CompilationState = CompilationState
  { _errors :: [Text]

  , _tc :: TypingContext

  , _loadedModules :: Map U.ModuleQualifier (Maybe (Module TC))
  , _orderedModules :: [Module TC]
  }
$(makeLenses ''CompilationState)


pf :: PrintfType r => String -> r
pf = Def.printf Def.G

moduleCtx :: FilePath -> InterModular (Maybe (Module TC)) -> BaseCtx (Either (NonEmpty Text) (NonEmpty (Module TC), TypingContext))
moduleCtx = resumeModuleCtx emptyState


-- saves compilation state: for testing purposes
runModuleCtx :: FilePath -> InterModular a -> BaseCtx (a, CompilationState)
runModuleCtx path fmod =
  RST.runRST (fromIM fmod) (Constants { basepath = path }) emptyState

-- also for testing.
resumeModuleCtx :: CompilationState -> FilePath -> InterModular (Maybe (Module TC)) -> BaseCtx (Either (NonEmpty Text) (NonEmpty (Module TC), TypingContext))
resumeModuleCtx state path fmmod = do
  (mmod, imState) <- RST.runRST (fromIM fmmod) (Constants { basepath = path }) state

  let (tids, uids) = TC.numTypesAndUnionsDefined $ imState^.tc
  numCreatedTypes .= tids
  numCreatedUnions .= uids

  case mmod of
    Nothing -> do
      let errs = imState ^. errors & NonEmpty.fromList
      pure $ Left errs

    Just tmod -> case imState ^. errors of
      e:es -> pure $ Left $ e :| es
      [] -> do
        -- REMEMBER TO REVERSE. Modules are PUSHED onto the stack, so we have to reverse it yo.
        let tmods = NonEmpty.reverse $ tmod :| imState ^. orderedModules
        pf "All modules: %" (length tmods) :: BaseCtx ()
        pure $ Right (tmods, imState^.tc)



emptyState :: CompilationState
emptyState = CompilationState
  { _errors = []
  , _tc = TC.emptyContext
  , _loadedModules = mempty
  , _orderedModules = mempty
  }

-- Right now only text geg
-- its all kinda crappy.
--   i want to be able to count the total amount of errors n shi
addErrors :: Text -> [Text] -> InterModular ()
addErrors _ [] = pure ()
addErrors moduleName errs = --IM $ RST.modify $ \s -> s { errors = s.errors <> (("Errors in module " <> moduleName <> ":") : errs) }  -- we append to the end here.
  errors %= (<> (("Errors in module " <> moduleName <> ":") : errs))

storeModule :: U.ModuleQualifier -> Maybe (Module TC) -> InterModular ()
storeModule modname mmod = do
  imLift $ countUp numLoadedModules
  pf "Store module: % (%)" modname (maybe "could not parse" (const "ok") mmod :: Context)
  loadedModules %= Map.insert modname mmod
  case mmod of
    Nothing -> pure ()
    Just md -> do
      orderedModules %= (md:)

-- currently, moduleLoader is situated here. I guess it makes more sense? maybe? i dunno, im really undecisive and I hate it....
moduleLoader :: FilePath -> (FilePath -> InterModular (Maybe (Module TC))) -> Text -> Loader
moduleLoader stdPath loadModule compilingModule mq = do
  mtmod <- findLoadedModule mq
  case mtmod of
    Just lmtmod -> pure $ Just lmtmod
    Nothing -> do
      filepath <- InterModular.mkModulePath mq
      projectModuleExists <- liftIO $ Directory.doesFileExist filepath
      lmtmod <- if projectModuleExists
        then do
          lmtmod <- relativeTo filepath $ loadModule filepath
          pure lmtmod

        else do
          -- make std path in a funny way. (no particular reason, it was just easier. good composition yo.)
          stdpath <- relativeTo stdPath $ mkModulePath mq
          stdModuleExists <- liftIO $ Directory.doesFileExist stdpath
          if stdModuleExists
            then do
              lmtmod <- relativeTo stdpath $ loadModule stdpath
              pure lmtmod

            else do
              addErrors compilingModule [Text.pack $ Def.pf "Could not find module %s. (Searched both for '%s' and std '%s')" (show mq) filepath stdpath]
              pure Nothing

      storeModule mq lmtmod
      pure lmtmod


findLoadedModule :: U.ModuleQualifier -> InterModular (Maybe (Module TC))
findLoadedModule mq = use loadedModules <&> (!? mq) <&> join



nextTypeID :: InterModular TypeID
nextTypeID = do
  tc' <- use tc
  let (tid, tc'') = TC.nextTypeID tc'
  tc .= tc''
  pure tid

nextUnionUniID :: InterModular UnionUniID
nextUnionUniID = do
  tc' <- use tc
  let (uid, tc'') = TC.nextUnionUniID tc'
  tc .= tc''
  pure uid


modifyTypeUni :: (TC.TypeTypeUni -> TC.TypeTypeUni) -> InterModular ()
modifyTypeUni f = tc %= TC.modifyTypeUni f

modifyUniUni :: (TC.UnionTypeUni -> TC.UnionTypeUni) -> InterModular ()
modifyUniUni f = tc %= TC.modifyUniUni f


getTypeUni :: InterModular TC.TypeUni
getTypeUni = use $ tc . globalTypeUni

numTypesAndUnionsDefined :: InterModular (Int, Int)
numTypesAndUnionsDefined = use tc <&> TC.numTypesAndUnionsDefined

trackInstantiation :: (Int, Int) -> Function TC -> InterModular ()
trackInstantiation (beforeTypes, beforeUnions) fn = do
  (afterTypes, afterUnions) <- numTypesAndUnionsDefined
  let Scheme tvars unions assocs = fn.functionDeclaration.functionOther.functionScheme
  let inst = FunInstTrack fn.functionDeclaration.functionId.varName.fromVN (afterTypes - beforeTypes) (afterUnions - beforeUnions) (length tvars) (length unions) (length assocs)
  IM $ lift $ BaseCtx.trackInstantiation inst


addEnvAdditions :: TC.Envs -> InterModular ()
addEnvAdditions newEnvAdditions = do
  undefined
  -- tc . globalEnvAddition' %= Map.unionWith mergeEnvAdditions newEnvAdditions

mergeEnvAdditions :: Ord a => [a] -> [a] -> [a]
mergeEnvAdditions new old =
    let oldSet = Set.fromList old
    in old <> filter (`Set.notMember` oldSet) new



mkModulePath :: U.ModuleQualifier -> InterModular FilePath
mkModulePath (U.ModuleQualifier modules) = do
  basePath <- IM $ RST.asks $ \ccc -> ccc.basepath
  let moduleFileNames = Text.unpack . Def.fromModName <$> NonEmpty.toList modules
  let fullpath = basePath </> FilePath.joinPath moduleFileNames <.> "kc"
  pure fullpath

relativeTo :: BasePath -> InterModular a -> InterModular a
relativeTo newBasePath = IM . RST.local (\ccc ->
  ccc { basepath = newBasePath }) . fromIM


imLift :: BaseCtx a -> InterModular a
imLift !x = IM $! lift $! x


instance (unit ~ ()) => Log (InterModular unit) where
  plog lt x = do
    typePrinter <- wholeTypePrinter
    unionPrinter <- wholeUnionPrinter
    unionIDPrinter <- unionIDPrinter
    IM $ lift $ plog lt $ local (\c -> c { typingContext = Just (typePrinter, unionPrinter, unionIDPrinter ) }) x

wholeTypePrinter :: InterModular (TypeID -> Context)
wholeTypePrinter = do
  tu <- use $ tc . globalTypeUni
  pure $ TC.ppTypeFromUniSafe tu

wholeUnionPrinter :: InterModular (UnionUniID -> Context)
wholeUnionPrinter = do
  tu <- use $ tc . globalTypeUni
  pure $ TC.ppUnionFromUniSafe tu

unionIDPrinter :: InterModular (UnionUniID -> Context)
unionIDPrinter = do
  tu <- use $ tc . globalTypeUni
  pure $ TC.ppUnionIDFromUniSafe tu
