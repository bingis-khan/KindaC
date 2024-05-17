module Std (preparePrelude, prepareStd) where
import Paths_KindaC (getDataFileName)


-- Right now all relies on the data directory.
-- When I distribute it, I might want to use TemplateHaskell to embed source files!

preparePrelude :: IO ()
preparePrelude = do
  fn <- getDataFileName "kcsrc/prelude/prelude.kc"
  undefined


prepareStd :: IO ()
prepareStd = undefined
