{-# LANGUAGE TypeFamilies, OverloadedRecordDot #-}
module AST.Typed (module AST.Typed) where

import AST.Common
import qualified AST.Def as Def

data Typed
type T = Typed

type instance XClass T = ClassDef T
type instance XTCon T = DataDef T
type instance XDTCon T = Def.UniqueType
type instance XDCon T = Def.UniqueCon
type instance XInstDef T = InstDef T
type instance XFunVar T = Def.UniqueVar
type instance XMem T = Def.MemName
type instance XDClass T = Def.UniqueClass



data Mod = Mod
  { topLevelStatements :: [AnnStmt T]
  , exports :: Exports T
  }
type instance Module Typed = Mod
