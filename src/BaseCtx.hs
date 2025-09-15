{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module BaseCtx (module BaseCtx) where
import Control.Monad.Fix (MonadFix)
import Control.Monad.Trans.RST (RST)
import Stats (Stats, Counter, FunInstTrack, instantiationsByNumTypes, emptyStats)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.RWS (MonadReader, MonadState, MonadTrans (..))
import Lens.Micro (Lens')
import AST.Def (Log (plog), CtxData, LogType (..), ctx, debugContext)
import Lens.Micro.Mtl ((+=), (%=))
import qualified Control.Monad.Trans.RST as RST
import Control.Monad (when)
import qualified Data.Text.IO as TextIO
import Data.Foldable (find)


-- LOGGING & STATS

newtype BaseCtx a = BaseCtx (RST Config Stats IO a) deriving (Functor, Applicative, Monad, MonadFix, MonadFail, MonadIO, MonadReader Config, MonadState Stats)
data Config = Config
  { filename :: FilePath
  , output :: Output
  , printOnlyCurrent :: Flag

  , dbgP :: Flag
  , dbgR :: Flag
  , dbgT_Uni :: Flag
  , dbgT_AST :: Flag
  , dbgF :: Flag
  , dbgM :: Flag
  , dbgG :: Flag

  , statP :: Flag
  , statR :: Flag
  , statT :: Flag
  , statF :: Flag
  , statM :: Flag
  , statG :: Flag  -- general stats, mostly about module loading and stuff.
  }

data Output
  = Stdout
  | File String
  | NoOutput


type Flag = Bool


  
-- TODO: maybe more transformations will come?
withBaseContext :: Config -> BaseCtx a -> IO (a, Stats)
withBaseContext config (BaseCtx fx) = RST.runRST fx config emptyStats


-- TODO: maybe make it MonadBaseCtx to execute actions in BaseCtx? then this would not be needed. and make plog a normal function.
countUp :: Lens' Stats Counter -> BaseCtx ()
countUp accessor = accessor += 1

countUp' :: MonadTrans t => Lens' Stats Counter -> t BaseCtx ()
countUp' accessor = lift $ countUp accessor

countUp'' :: (MonadTrans t, MonadTrans t') => Lens' Stats Counter -> t (t' BaseCtx) ()
countUp'' accessor = lift $ lift $ countUp accessor

trackInstantiation :: FunInstTrack -> BaseCtx ()
trackInstantiation fit = instantiationsByNumTypes %= (fit:)


instance (unit ~ ()) => Log (BaseCtx unit) where  -- base instance
  plog lt c = do
    config <- BaseCtx $ RST.ask

    when (isPrintingEnabled lt config) $
      liftIO $ TextIO.putStrLn $ ctx (configToContextData config) c

configToContextData :: Config -> CtxData
configToContextData = const debugContext

isPrintingEnabled :: LogType -> Config -> Bool
{-# inline isPrintingEnabled #-}
isPrintingEnabled l cfg
  = maybe False (($ cfg) . snd)
  $ find ((==l) . fst)
  [ (P, dbgP)
  , (R, dbgR)
  , (T_Uni, dbgT_Uni)
  , (T_AST, dbgT_AST)
  , (F, dbgF)
  , (M, dbgM)
  , (G, dbgG)
  ]
