{-# LANGUAGE TypeFamilies, OverloadedRecordDot #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module AST.Typed (module AST.Typed) where

import AST.Common
import qualified AST.Def as Def
import Data.Map (Map)
import AST.Def (PP (..), (<+>))

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
type instance Rec T a = a

-- we will probably put it in T.
data Scheme phase = Scheme [TVar phase] [XEnvUnion phase]

data Variable
  = DefinedVariable Def.UniqueVar
  | DefinedFunction (Function T)
  | DefinedInstance (InstFun T)

data Mod = Mod
  { topLevelStatements :: [AnnStmt T]
  , exports :: Exports T
  }
type instance Module Typed = Mod


--------

instance (PP (XEnvUnion phase)) => PP (Scheme phase) where
  pp (Scheme tvars unions) = Def.ppSet pp tvars <+> Def.ppSet pp unions

