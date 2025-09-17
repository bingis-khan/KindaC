-- This was created, because the Haskell LSP does not seem to work for app/Main.hs
{-# LANGUAGE LambdaCase, OverloadedRecordDot, OverloadedStrings #-}
module Entry (compilerMain, defaultConfig) where

import qualified Data.Text.IO as TextIO
import System.Environment (getArgs)
import Pipeline (startFromModule, codegen)
import Control.Monad.IO.Class (liftIO)
import qualified System.FilePath as FilePath
import qualified Data.Text as Text
import qualified Data.List.NonEmpty as NonEmpty
import System.Exit (exitFailure)
import qualified AST.Def as Def
import GHC.Debug.Stub (withGhcDebug)
import Data.Time (getCurrentTime, diffUTCTime, nominalDiffTimeToSeconds)
import Data.Fixed (showFixed)
import AST.Def (LogType (Stat, G, PP), pf)
import Data.Function ((&))
import Data.Maybe (fromMaybe)
import Control.Monad (when)
import Stats
import Lens.Micro ((^.))
import Data.List (sort)
import BaseCtx (Output(..), Config (..), withBaseContext)


compilerMain :: IO ()
compilerMain = do
  startT <- getCurrentTime
  config <- parseArgs

  (_, stats) <- withBaseContext config $ do
    etfMod <- startFromModule config.filename

    case etfMod of
      Left errs -> liftIO $ do
        TextIO.putStrLn $ Text.unlines $ NonEmpty.toList errs
        exitFailure

      Right tfMod -> do
        cmod <- codegen tfMod

        case config.output of
          File name -> liftIO $ TextIO.writeFile name cmod
          Stdout -> liftIO $ TextIO.putStrLn cmod
          NoOutput -> pure ()


  printStats config stats
  when config.statG $ do
    endT <- liftIO getCurrentTime
    let diff = nominalDiffTimeToSeconds $ diffUTCTime endT startT
    Def.pf "Time: %" $ showFixed False diff



printStats :: Config -> Stats -> IO ()
printStats cfg s = do
  when cfg.statR $ do
    pf "R expr: %\nR stmt: %" (s ^. rExprNum) (s ^. rStmtNum)

  when cfg.statT $ do
    pf "T expr: %\nT stmt: %" (s ^. tExprNum) (s ^. tStmtNum)
    pf "T unique types: %\nT unique unions: %" (s ^. numCreatedTypes) (s ^. numCreatedUnions)
    pf "T num unis: %" (s ^. numSeparateUnifications)
    pf "T tv maps: %" (s ^. numTVMaps)
    pf "T cs maps: %" (s ^. numCSMaps)

  when cfg.statM $ do
    pf "M expr: %" $ s ^. mExprNum
    pf "M stmt: %" $ s ^. mStmtNum
    pf "M type: %" $ s ^. mTypeNum
    pf "M union: %" $ s ^. mUnionNum

    pf "MF expr: %" $ s ^. mfExprNum
    pf "MF stmt: %" $ s ^. mfStmtNum
    pf "MF type: %" $ s ^. mfTypeNum
    pf "MF union: %" $ s ^. mfUnionNum

  when cfg.statG $ do
    pf "Modules loaded: %" (s ^. numLoadedModules)

  when cfg.statT $ do
    pf "Num instantiations: %" $ s ^. instantiationsByNumTypes & length

    let top10costliest = take 10 $ reverse $ sort $ s ^. instantiationsByNumTypes
    Def.plog PP $ Def.indent "Top 10 costliest instantiations:" $
      Def.ppLines top10costliest



parseArgs :: IO Config
parseArgs = do
  args <- getArgs
  let (mFilename, fconfig) = foldr understandOpt (Nothing, defaultConfig) $ map parseOpt args
  pure $ case mFilename of
    Just name -> fconfig name
    Nothing -> error "No filename provided."

-- parses a single --opt=dupsko or --opt
parseOpt :: String -> (String, Maybe String)
parseOpt = fmap ((\s -> if null s then Nothing else Just s) . drop 1) . span (/='=')

understandOpt :: (String, Maybe String) -> (Maybe String, FilePath -> Config) -> (Maybe String, FilePath -> Config)
understandOpt ('-':'-':optname, opt) (mfname, fc) = (,) mfname $ (. fc) $ \c -> case optname of
  "debug" -> maybe
    -- default case
    (c
      { dbgP = True
      , dbgR = True
      , dbgT_AST = True
      , dbgF = True
      , dbgM = True
      , dbgG = True
      })

    -- specific case
    (\chars -> foldr (\char cc -> case char of
      'p' -> cc { dbgP = True }
      'r' -> cc { dbgR = True }
      'u' -> cc { dbgT_Uni = True }
      't' -> cc { dbgT_AST = True }
      'f' -> cc { dbgF = True }
      'm' -> cc { dbgM = True }
      'g' -> cc { dbgG = True }
      _ -> error $ Def.pf "Unknown option %." char
    ) c chars)

    opt

  "stats" -> maybe
    -- default case
    (c { statP = True, statR = True, statT = True, statF = True, statM = True, statG = True })

    -- specific case
    (\chars -> foldr (\char cc -> case char of
      'p' -> cc { statP = True }
      'r' -> cc { statR = True }
      't' -> cc { statT = True }
      'f' -> cc { statF = True }
      'm' -> cc { statM = True }
      'g' -> cc { statG = True }
      _ -> error $ Def.pf "Unknown option %." char
    ) c chars)

    opt

  "only-current" -> c { printOnlyCurrent = True }
  "print-opts" -> undefined
  "no-output" -> c { output = NoOutput }
  "output-c" -> c { output = File $ fromMaybe "test.c" mfname }

  _ -> error $ Def.pf "Unrecorgnized option %." optname

understandOpt (name, Nothing) (_, fc) = (Just name, fc)
understandOpt (fname, Just _) _ = error $ Def.pf "You've just posted cringe. (filename has '='. i've determined that % is a filename, because it does not start with '--')" fname


defaultConfig :: FilePath -> Config
defaultConfig fn = Config
  { filename = fn
  , output = Stdout  -- TODO: when it becomes a real compiler, change it to a File with the name from filepath.
  , printOnlyCurrent = False

  , dbgP = False
  , dbgR = False
  , dbgT_Uni = False
  , dbgT_AST = False
  , dbgF = False
  , dbgM = False
  , dbgG = False

  , statP = False
  , statR = False
  , statT = False
  , statF = False
  , statM = False
  , statG = False
  }
