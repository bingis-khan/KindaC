{-# LANGUAGE OverloadedStrings #-}
module AST.Converged (module AST.Converged) where

-- TODO: make AST.Converged into AST after refactor

import AST.Common (Module, Type, UniqueCon, VarName, UniqueVar, ConName (..), UniqueType, TCon (..), Expr, TVar, EnvUnion)
import AST.Typed (Typed)

import Data.Map (Map)
import qualified AST.Typed as T
import Data.Fix (Fix(..))



-- the funny anti-cyclic (cucklic) module dependency
--    Common
-- Untyped Resolved Typed ...
--    Converged

-- i guess this means that I should take the Odin approach?


data Prelude = Prelude
  { tpModule :: Module Typed

  , unitValue :: (UniqueCon, Type Typed)
  , toplevelReturn :: Expr Typed  -- includes the type one should refer to. should be Int (later U8)
  , boolType :: Type Typed
  , intType :: Type Typed

  , varNames :: Map VarName (Either T.FunDec (UniqueVar, Type Typed))
  , conNames :: Map ConName (UniqueType, [TVar], [EnvUnion Typed], T.DataCon)
  , tyNames  :: Map TCon T.DataDef
  } deriving Show


unitName :: ConName
unitName = CN "Unit"

tlReturnTypeName, boolTypeName, intTypeName :: TCon
tlReturnTypeName = TC "Int"  -- later U8
intTypeName      = TC "Int"  -- later a typeclass?
boolTypeName     = TC "Bool"


-- Kinda of a weird solution. This "pack" describes the way a type could be found without Prelude.
data PreludeFind = PF TCon (Prelude -> Type Typed)

-- since we have TCs, not sure if we need the added types (int, bool). maybe we can just find them normally, through conNames/tyNames.
tlReturnFind, boolFind, intFind :: PreludeFind
tlReturnFind = PF tlReturnTypeName ((\(Fix (T.ExprType t _)) -> t) . toplevelReturn)
boolFind = PF boolTypeName boolType
intFind = PF intTypeName intType

