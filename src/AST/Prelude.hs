{-# LANGUAGE OverloadedStrings #-}
module AST.Prelude (module AST.Prelude) where

import qualified AST.Def as Def
import AST.Typed (TC)
import AST.Common (Module, DataCon, Expr, Type, Node (..))
import Data.Fix (Fix(..))


-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


data Prelude = Prelude
  { tpModule       :: Module TC

  -- extra stuff for resolving/typechecking that is always needed.
  , unitValue      :: DataCon TC
  , toplevelReturn :: Expr  TC  -- includes the type one should refer to. should be Int (later U8)
  , boolType       :: Type TC
  , intType        :: Type TC
  , floatType      :: Type TC
  , constStrType   :: Type TC
  , mkPtr          :: Type TC -> Type TC
  }


unitName :: Def.ConName
unitName = Def.CN "Unit"

tlReturnTypeName, boolTypeName, intTypeName, floatTypeName, unitTypeName, ptrTypeName, constStrTypeName :: Def.TCon
tlReturnTypeName = Def.TC "Int"  -- later U8
intTypeName      = Def.TC "Int"  -- later a typeclass?
floatTypeName    = Def.TC "Float"
boolTypeName     = Def.TC "Bool"
unitTypeName     = Def.TC "Unit"
ptrTypeName      = Def.TC "Ptr"
constStrTypeName = Def.TC "ConstStr"


-- Kinda of a weird solution. This "pack" describes the way a type could be found without Prelude.
data PreludeFind = PF Def.TCon (Prelude -> Type TC)

-- since we have TCs, not sure if we need the added types (int, bool). maybe we can just find them normally, through conNames/tyNames.
tlReturnFind, boolFind, intFind, floatFind, constStrFind :: PreludeFind
tlReturnFind = PF tlReturnTypeName ((\(Fix (N t _)) -> t) . toplevelReturn)
boolFind = PF boolTypeName boolType
intFind = PF intTypeName intType
floatFind = PF floatTypeName floatType
constStrFind = PF constStrTypeName constStrType

ptrFind :: Type TC -> PreludeFind
ptrFind t = PF ptrTypeName (`mkPtr` t)

