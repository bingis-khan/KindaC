{-# LANGUAGE OverloadedStrings #-}
module AST.Converged (module AST.Converged) where

-- TODO: make AST.Converged into AST after refactor
--  TODO today: what????? you mean, only the name, right?

import AST.Common (ConName (..), TCon (..))
import qualified AST.Typed as T
import Data.Fix (Fix(..))



-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


data Prelude = Prelude
  { tpModule       :: T.Module

  -- extra stuff for resolving/typechecking that is always needed.
  , unitValue      :: T.DataCon
  , toplevelReturn :: T.Expr -- includes the type one should refer to. should be Int (later U8)
  , boolType       :: T.Type
  , intType        :: T.Type
  , floatType      :: T.Type
  }


unitName :: ConName
unitName = CN "Unit"

tlReturnTypeName, boolTypeName, intTypeName, floatTypeName, unitTypeName :: TCon
tlReturnTypeName = TC "Int"  -- later U8
intTypeName      = TC "Int"  -- later a typeclass?
floatTypeName    = TC "Float"
boolTypeName     = TC "Bool"
unitTypeName     = TC "Unit"


-- Kinda of a weird solution. This "pack" describes the way a type could be found without Prelude.
data PreludeFind = PF TCon (Prelude -> T.Type)

-- since we have TCs, not sure if we need the added types (int, bool). maybe we can just find them normally, through conNames/tyNames.
tlReturnFind, boolFind, intFind, floatFind :: PreludeFind
tlReturnFind = PF tlReturnTypeName ((\(Fix (T.TypedExpr t _)) -> t) . toplevelReturn)
boolFind = PF boolTypeName boolType
intFind = PF intTypeName intType
floatFind = PF floatTypeName floatType

