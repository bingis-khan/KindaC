{-# LANGUAGE OverloadedStrings, LambdaCase, NamedFieldPuns, TupleSections #-}
module Main where

import Parser
import Resolver (resolveAll)
import Data.Functor.Foldable (cata)
import AST
import Typecheck (typecheck)
import CPrettyPrinter (Context''(..), pp)
import ASTPrettyPrinter (ppModule, ppShow)

import System.Process (callCommand)
import System.Environment (getArgs)
import Data.Set (Set)
import Data.Fix
import Data.Functor ((<&>))
import Monomorphizer (monomorphize)
import qualified Data.Map as M
import Data.Unique (newUnique)
import Data.Map (Map, (!))
import Debug.Trace (traceShowId)
import Data.Foldable (toList)
import Data.Either (rights)
import Data.Biapplicative (bimap)
import Data.Text (Text)
import qualified Data.Text.IO as TIO


groupAfterParsing :: [TopLevel] -> ([UDataDec], [Either UFunDec UStmt])
groupAfterParsing =  mconcat . map go
  where
    go (FunDec fd) = (mempty, pure (Left fd))
    go (TLStmt stmt) = (mempty, pure (Right stmt))
    go (DataDec dd) = (pure dd, mempty)

prepareContext :: (Foldable t, Functor t) => Builtins -> t (TDataDec, [TypedType]) -> Context''
prepareContext builtins dds = Context { datas, builtins }
  where
    datas = M.fromList $ toList $ fmap (\(dd@(DD t _ _), tts) -> ((t, tts), dd)) dds


data CType = CType Text [(Text, Text)] Text

builtinTypes :: [CType]
builtinTypes =
  [ CType "Int" [] "int"
  , CType "Bool" [("True", "true"), ("False", "false")] "bool"
  ]

prepareTypes :: [CType] -> IO Builtins
prepareTypes builtinTypes = do
  (toTypes, fromTypes) <- bimap M.fromList M.fromList . unzip <$> traverse (\(CType name _ cName) -> TypeID <$> newUnique <&> \t -> ((name, Fix (TCon t [])), (t, cName))) builtinTypes
  (toCons, fromCons) <- bimap M.fromList M.fromList . unzip <$> traverse (\(name, cName, (cons, cCons)) -> Global <$> newUnique <&> \g -> ((cons, (g, toTypes ! name)), (g, cCons))) (concatMap (\(CType name cons cName) -> (name, cName,) <$> cons) builtinTypes)
  return $ Builtins toTypes fromTypes toCons fromCons

main :: IO ()
main = do
  -- -- Proof of another b00g. Happens with id(x) => x.
  -- let cs = [(Fix (TFun [Fix (TVar (TV "k"))] (Fix (TVar (TV "k")))), Fix (TFun [Fix (TVar (TV "a"))] (Fix (TVar (TV "b")))))]
  -- in print $ solve cs
  (filename:_) <- getArgs
  file <- TIO.readFile filename

  builtins <- prepareTypes builtinTypes
  print builtins
  case parse file of
    Left s -> putStrLn s
    Right tls -> do
      putStrLn $ ppShow undefined tls
      putStrLn $ ("\n" <>) $ (<> "\n") $ replicate 70 '-'
      let (datadecs, eFunStmts) = groupAfterParsing tls
      resolveAll builtins datadecs eFunStmts >>= \case
        Left res -> do
          putStrLn "Resolve Errors"
          print res
        Right rmodule -> do
          putStrLn $ ppModule undefined rmodule
          case typecheck builtins rmodule of
            Left ne -> print ne
            Right module' -> do
              putStrLn $ ppShow undefined module'
              let (dds, funs, stmts) = monomorphize builtins module'
              putStrLn $ ppShow undefined dds
              putStrLn $ ppShow undefined funs
              putStrLn $ ppShow undefined stmts
              writeFile "test.c" =<< pp (prepareContext builtins (rights dds)) dds funs stmts
              -- callCommand "gcc test.c"
              return ()
