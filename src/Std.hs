module Std (preparePrelude, preludePath, prepareStd) where
import Paths_KindaC (getDataFileName)
import AST (Prelude)
import Pipeline (loadModule)
import qualified Data.Text as Text


-- Right now all relies on the data directory.
-- When I distribute it, I might want to use TemplateHaskell to embed source files!

preludePath :: String
preludePath = "kcsrc/prelude.kc"

preparePrelude :: IO Prelude
preparePrelude = do
  fn <- getDataFileName preludePath
  eprelude <- loadModule Nothing fn
  pure $ case eprelude of
    Left errors -> error $ unlines
      [ "OH SHIT MAN: There were errors while compiling prelude. Fix yo shit, bitch."
      , Text.unpack errors
      ]
    Right prelude -> prelude


prepareStd :: IO ()
prepareStd = return ()
