{-# LANGUAGE TemplateHaskell, OverloadedRecordDot #-}
module Stats (module Stats) where

import Lens.Micro.TH (makeLenses)
import Data.Text (Text)


-- shit module to avoid TH bullshit in AST.Def

data FunInstTrack = FunInstTrack
  { name :: Text
  , newTypes :: Int
  , newUnions :: Int
  } deriving Eq

type Counter = Word  -- for stats.
data Stats = Stats
  { _rExprNum :: Counter
  , _rStmtNum :: Counter

  , _tExprNum :: Counter
  , _tStmtNum :: Counter

  , _fExprNum :: Counter
  , _fStmtNum :: Counter

  , _mExprNum :: Counter
  , _mStmtNum :: Counter

  , _numCreatedTypes :: Int
  , _numCreatedUnions :: Int
  , _numSeparateUnifications :: Counter

  , _instantiationsByNumTypes :: [FunInstTrack]

  , _numLoadedModules :: Counter
  }
makeLenses ''Stats

emptyStats :: Stats
emptyStats = Stats
  { _rExprNum = 0
  , _rStmtNum = 0
  , _tExprNum = 0
  , _tStmtNum = 0
  , _fExprNum = 0
  , _fStmtNum = 0
  , _mExprNum = 0
  , _mStmtNum = 0
  , _numCreatedTypes = 0
  , _numCreatedUnions = 0
  , _instantiationsByNumTypes = mempty
  , _numSeparateUnifications = 0
  , _numLoadedModules = 0
  }



instance Ord FunInstTrack where
  x `compare` x' = x.newTypes `compare` x'.newTypes
