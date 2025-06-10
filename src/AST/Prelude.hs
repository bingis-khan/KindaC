{-# LANGUAGE OverloadedStrings #-}
module AST.Prelude (module AST.Prelude) where

import qualified AST.Def as Def
import AST.Typed (T)
import AST.Common (Module, DataCon, Expr, Type)


-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


data Prelude = Prelude
  { tpModule       :: Module T

  -- extra stuff for resolving/typechecking that is always needed.
  , unitValue      :: DataCon T
  , toplevelReturn :: Expr  T-- includes the type one should refer to. should be Int (later U8)
  , boolType       :: Type T
  , intType        :: Type T
  , floatType      :: Type T
  }


unitName :: Def.ConName
unitName = Def.CN "Unit"

tlReturnTypeName, boolTypeName, intTypeName, floatTypeName, unitTypeName :: Def.TCon
tlReturnTypeName = Def.TC "Int"  -- later U8
intTypeName      = Def.TC "Int"  -- later a typeclass?
floatTypeName    = Def.TC "Float"
boolTypeName     = Def.TC "Bool"
unitTypeName     = Def.TC "Unit"


-- Kinda of a weird solution. This "pack" describes the way a type could be found without Prelude.
data PreludeFind = PF Def.TCon (Prelude -> Type T)

-- since we have TCs, not sure if we need the added types (int, bool). maybe we can just find them normally, through conNames/tyNames.
tlReturnFind, boolFind, intFind, floatFind :: PreludeFind
tlReturnFind = undefined  -- TODO: PF tlReturnTypeName ((\(Fix (TypedExpr t _)) -> t) . toplevelReturn)
boolFind = PF boolTypeName boolType
intFind = PF intTypeName intType
floatFind = PF floatTypeName floatType

