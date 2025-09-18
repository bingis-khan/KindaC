module Control.Monad.Trans.RST (module Control.Monad.Trans.RST, module Control.Monad.Trans.RWS.Strict) where

import Control.Monad.Trans.RWS.Strict hiding (runRWST)
import qualified Control.Monad.Trans.RWS.Strict as RWS (runRWST)

-- funny
--  (in the future, I should make it its own datatype.)

type RST r s = RWST r () s

runRST :: Functor m => RST r s m a -> r -> s -> m (a, s)
runRST rst = (fmap . fmap) (\(x, s, ()) -> (x, s)) . RWS.runRWST rst

