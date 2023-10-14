{-# LANGUAGE KindSignatures, FlexibleInstances, DeriveFunctor, LambdaCase #-}
module CPrint (cprint) where

import AST hiding (DD, FD)


import qualified Data.Set as Set
import Data.Fix (Fix(Fix))
import Data.Coerce (coerce)
import Data.Either (rights)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.String (fromString, IsString)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Foldable (fold, traverse_)
import Data.Unique (hashUnique)
import qualified Data.Text as Text
import Data.Functor.Foldable (cata, Base)
import AST (DataDec(..), FunDec (..))
import Data.List (intersperse)
import Data.Bifunctor (first)
import Data.Set (Set)


-- basic configuration
nesting, space :: Text
nesting = fromString "  "
space = fromString " "


cprint :: [Either MonoDataDec MonoDataDef] -> [Either MonoFunDec TFunDec] -> [TStmt] -> IO Text
cprint dds funs tls = do
    -- let globalVariables =
    --       let assignments = mapMaybe (\case { Fix (Assignment l (Fix (ExprType t _))) -> Just (l, t); _ -> Nothing }) tls
    --           locals = foldMap usedLocals $ rights funs
    --       in Set.intersection locals (Set.fromList $ map fst assignments)
    runCtx $ fold
      [ ppsd dds
      , ppsd funs
      , pptl tls
      ]

runCtx :: Ctx -> IO Text
runCtx (Ctx headers _ ctx) = do
  CtxCtx lines <- ctx
  let headers' = (<> fromString "\n\n") $ fromString $ unlines $ map (\s -> "#include <" ++ s ++ ">") $ Set.toList headers
  return $ headers' <> foldMap (<> fromString "\n") lines 


pptl :: [TStmt] -> Ctx
pptl tls = do
  pp "int"
  pp "main(int argc, char* argv[])"
  block tls

-- dt instances
instance PP MonoDataDec where
  pp (MonoDataDec tid tys) = do
    pp "static"
    endstmt $ ppDataDef tid tys

ppDataDef :: TypeID -> [TypedType] -> Ctx
ppDataDef  tid tys = pp "struct" <+> fold
  [ pp "d"
  , pp tid
  , pp "_"
  , pprepend "_" tys
  ]

instance PP TypedType where
  pp = cata go
    where
      go :: Base TypedType Ctx -> Ctx
      go = \case
        -- temporary type printing
        TCon con [] | 1 == hashUnique (fromTypeID con) -> pp "int"
        TCon con [] | 2 == hashUnique (fromTypeID con) -> include "stdbool.h" <> pp "bool"

        TCon con ts -> pp "t" <> pp con
        TFun args ret -> pp "br" <> pprepend "_" args <> pp "_ret_" <> ret

        -- this is unreachable. should probably improve my types...
        TVar tv -> error "unreachable"
        TDecVar tv -> error "unreachable"

instance PP TypeID where
  pp = pp . hashUnique . fromTypeID
  
instance PP MonoDataDef where
  pp (MonoDataDef (DD tid _ cons) tys) = do
    -- what kind of structure: enum, struct or ADT
    case cons of
      -- struct
      con :| [] -> ppDataDef tid tys <+> block (ppStructParam con)
     
      -- enum
      xs | all (\(DC _ params) -> null params) cons -> undefined

      -- adt
      xs -> undefined

ppStructParam :: TDataCon -> [Ctx]
ppStructParam (DC _ ts) = zipWith (\x t -> endstmt (pp t <+> pp "p" <> pp x)) [0 :: Int ..] ts


instance PP MonoFunDec where
  pp (MonoFunDec g (Fix (TFun params ret))) = endstmt $ do
    pp "static"
    pp ret
    pp g <> encloseSep "(" ")" ", " params

  -- erroneous condition
  pp _ = error "Function does not have a function type. (which should be impossible, my types suck dick)"

instance PP TFunDec where
  pp (FD g params ret body) = do
    pp "static" <+> pp ret
    pp g <> encloseSep "(" ")" ", " (fmap (\(l, t) -> pp t <+> pp t) params)
    ppsl body


instance PP TStmt where
  pp = cata $ go . first (\e@(Fix (ExprType t _)) -> (t, pp e))
    where
      go :: Base (Stmt Local h (TypedType, Ctx)) Ctx -> Ctx
      go = \case
        Assignment name (t, e) -> endstmt $ do
          ppParam t name
          pp "="
          e

        Return (_, e) -> endstmt $ do
          pp "return"
          e

        ExprStmt (_, e) -> endstmt e

        Print (Fix t, e) ->
          endstmt $ include "stdio.h" <> case t of
            -- temporary printing (will be done with a typeclass later)
            TCon g [] -> case hashUnique (fromTypeID g) of
              1 -> pp "printf(\"%d\\n\"," <+> e <> pp ")"
              2 -> include "stdbool.h" <> pp "printf(\"%s\\n\"," <+> e <+> pp "? \"True\" : \"False\"" <> pp ")"

instance PP TExpr where
  pp = cata $ \(ExprType t e) -> case e of
    Lit (LInt x) -> pp x
    Var name -> case name of
      Left loc -> pp loc
      Right global -> undefined

instance PP Global where
  pp = (pp "g" <>) . pp . hashUnique . fromGlobal

instance PP Local where
  pp = (pp "l" <>) . pp . hashUnique . fromLocal


ppParam :: TypedType -> Local -> Ctx
ppParam t l = do
  pp t
  pp l

include :: String -> Ctx
include headerName = Ctx (Set.singleton headerName) mempty mempty

pprepend :: (Foldable f, PP p, PP a) => p -> f a -> Ctx
pprepend x = foldMap ((<> pp x) . pp)

endstmt :: PP a => a -> Ctx
endstmt x = endl $ pp x <> pp ";"

block :: PP a => [a] -> Ctx
block xs = endl "{" <> nest (foldMap pp xs) <> pp "}"

nest :: PP a => a -> Ctx
nest x =
  let (Ctx headers () ioctxctx) = pp x
  in Ctx headers () $ do
    CtxCtx lines <- ioctxctx
    return $ CtxCtx $ if NonEmpty.last lines /= fromString ""
      then fmap (nesting <>) lines
      else fmap (nesting <>) (NonEmpty.init lines) `NonEmpty.prependList` NonEmpty.singleton (NonEmpty.last lines)

encloseSep :: (PP l, PP r, PP sep, PP a) => l -> r -> sep -> [a] -> Ctx
encloseSep l r s xs = pp l <> sepBy s xs <> pp r

sepBy :: (PP sep, PP a) => sep -> [a] -> Ctx
sepBy sep xs =
  let sep' = pp sep
      xs'  = map pp xs
  in mconcat $ intersperse sep' xs'


(<+>) :: Ctx -> Ctx -> Ctx
x <+> y = x <> pp " " <> y
infixr 6 <+>

-- pp class
class PP a where
  pp :: a -> Ctx

instance PP Ctx where
  pp = id

instance PP Int where
  pp = packCtx . show

instance PP String where
  pp = packCtx

packCtx :: String -> Ctx
packCtx = Ctx mempty () . pure . CtxCtx . pure . Text.pack

-- pps :: PP a => [a] -> Ctx
-- pps = foldMap pp

ppsl :: (Traversable t, PP a) => t a -> Ctx
ppsl = traverse_ (endl . pp)

ppsd :: PP a => [a] -> Ctx
ppsd = traverse_ (endl . endl . pp)


endl :: PP a => a -> Ctx
endl x =
  let (Ctx headers _ iolines) = pp x
  in Ctx headers () $ do
    CtxCtx lines <- iolines
    pure $ CtxCtx $ NonEmpty.append lines $ NonEmpty.singleton mempty

instance (PP a, PP b) => PP (Either a b) where
  pp = either pp pp


-- ctx
type Ctx = Ctx' IO ()
data Ctx' (m :: * -> *) a = Ctx (Set HeaderFile) a (m CtxCtx)
  deriving Functor

type HeaderFile = String

instance Semigroup Ctx where
  Ctx headers a ctx <> Ctx headers' b ctx' =
    Ctx (headers <> headers') (a <> b) (ctx <> ctx')

instance Monoid Ctx where
  mempty = Ctx mempty mempty mempty

instance Applicative (Ctx' IO) where
  Ctx headers f ctx <*> Ctx headers' x ctx' = Ctx (headers <> headers') (f x) (ctx <> ctx')
  pure x = Ctx mempty x mempty

instance Monad (Ctx' IO) where
  Ctx headers x ctx >>= f =
    let (Ctx headers y ctx') = f x
    in Ctx headers y (ctx <> ctxctx space <> ctx')

ctxctx :: Text -> IO CtxCtx
ctxctx = pure . CtxCtx . NonEmpty.singleton

newtype CtxCtx = CtxCtx (NonEmpty Text)

instance Semigroup CtxCtx where
  CtxCtx xs <> CtxCtx (h :| rest) =
    let (start, t) = tailsplit xs
    in CtxCtx $ NonEmpty.prependList start ((t <> h) :| rest)

instance Monoid CtxCtx where
  mempty = CtxCtx $ NonEmpty.singleton $ fromString ""

tailsplit :: NonEmpty a -> ([a], a)
tailsplit xs = (NonEmpty.init xs, NonEmpty.last xs)




