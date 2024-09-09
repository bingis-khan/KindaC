module AST.Converged where

-- TODO: make AST.Converged into AST after refactor

import AST.Common (Module)
import AST.Typed (Typed)


-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


type Prelude = Module Typed
