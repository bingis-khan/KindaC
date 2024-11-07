{-# LANGUAGE OverloadedStrings #-}
module AST.Converged (module AST.Converged) where

-- TODO: make AST.Converged into AST after refactor

import AST.Common (UniqueCon, VarName, UniqueVar, ConName (..), UniqueType, TCon (..), TVar)
import Data.Map (Map)
import qualified AST.Typed as T
import Data.Fix (Fix(..))



-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


data Prelude = Prelude
  { tpModule       :: T.Module

  , unitValue      :: T.DataCon
  , toplevelReturn :: T.Expr -- includes the type one should refer to. should be Int (later U8)
  , boolType       :: T.Type
  , intType        :: T.Type

  , varNames       :: Map VarName (Either (UniqueVar, T.Type) T.Function)
  , conNames       :: Map ConName T.DataCon
  , tyNames        :: Map TCon T.DataDef
  }


unitName :: ConName
unitName = CN "Unit"

tlReturnTypeName, boolTypeName, intTypeName :: TCon
tlReturnTypeName = TC "Int"  -- later U8
intTypeName      = TC "Int"  -- later a typeclass?
boolTypeName     = TC "Bool"


-- Kinda of a weird solution. This "pack" describes the way a type could be found without Prelude.
data PreludeFind = PF TCon (Prelude -> T.Type)

-- since we have TCs, not sure if we need the added types (int, bool). maybe we can just find them normally, through conNames/tyNames.
tlReturnFind, boolFind, intFind :: PreludeFind
tlReturnFind = PF tlReturnTypeName ((\(Fix (T.TypedExpr t _)) -> t) . toplevelReturn)
boolFind = PF boolTypeName boolType
intFind = PF intTypeName intType

