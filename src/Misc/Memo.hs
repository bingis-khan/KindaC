{-# LANGUAGE TypeFamilies #-}
module Misc.Memo (memo, memo', emptyMemo, isMemoed, Memo(..), Memoizable) where

import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.Trans.RWS (RWST)
import qualified Control.Monad.Trans.RWS as RWS
import Data.Kind (Type)
import Control.Monad.Trans.State (StateT)
import qualified Control.Monad.Trans.State as StateT


-- Bad memoization thing I found useful. May be too general?
-- TODO: If I use it with something other than memo, replace RWST with a class and make different datatypes implement it.

newtype Memo id a = Memo { memoToMap :: Map id a }

memo :: (Monad ctx, Memoizable ctx, Ord r) => (OverallState ctx -> Memo r t) -> (Memo r t -> OverallState ctx -> OverallState ctx) -> (r -> (t -> ctx ()) -> ctx t) -> r -> ctx t
memo toMemo fromMemo transform r = do
  (Memo mem) <- memoGets toMemo
  case mem !? r of
    Just t -> pure t
    Nothing -> do
      -- unfortunately, we have to have this function, because we want to initialize the thunk first.
      let addMemo t = memoModify $ \s ->
            let (Memo m) = toMemo s
                m' = Memo $ Map.insert r t m
            in fromMemo m' s

      x <- transform r addMemo

      -- automatically call `addMemo` here?
      addMemo x  -- i'll try - i'll see what happens

      pure x

memo' :: (Monad ctx, Memoizable ctx, Ord r) => (OverallState ctx -> Memo r t) -> (Memo r t -> OverallState ctx -> OverallState ctx) -> r -> (r -> (t -> ctx ()) -> ctx t) -> ctx t
memo' toMemo fromMemo r transform = memo toMemo fromMemo transform r

isMemoed :: Ord a => a -> Memo a b -> Maybe b
isMemoed x (Memo mp) = mp !? x

emptyMemo :: Ord id => Memo id a
emptyMemo = Memo mempty


class Memoizable ctx where
  type OverallState ctx :: Type
  memoGets :: (OverallState ctx -> a) -> ctx a
  memoModify :: (OverallState ctx -> OverallState ctx) -> ctx () 

instance (Monoid w, Monad m) => Memoizable (RWST r w state m) where
  type OverallState (RWST r w state m) = state
  memoGets = RWS.gets
  memoModify = RWS.modify

instance Monad m => Memoizable (StateT state m) where
  type OverallState (StateT state m) = state
  memoGets = StateT.gets
  memoModify = StateT.modify
