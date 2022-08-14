{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
module Main where

import Parser
import Resolver (resolveAll)
import Data.Functor.Foldable (cata)
import AST
import Typecheck (typecheck)
import CPrettyPrinter (pp)
import ASTPrettyPrinter (ppModule, ppShow)

import System.Process (callCommand)
import System.Environment (getArgs)
import Data.Set (Set)
import Data.Fix
import Data.Functor ((<&>))
import Monomorphizer (monomorphize)


groupAfterParsing :: [TopLevel] -> ([UDataDec], [Either UFunDec UStmt])
groupAfterParsing =  mconcat . map go
  where
    go (FunDec fd) = (mempty, pure (Left fd))
    go (TLStmt stmt) = (mempty, pure (Right stmt))
    go (DataDec dd) = (pure dd, mempty)

main :: IO ()
main = do
  -- -- Proof of another b00g. Happens with id(x) => x.
  -- let cs = [(Fix (TFun [Fix (TVar (TV "k"))] (Fix (TVar (TV "k")))), Fix (TFun [Fix (TVar (TV "a"))] (Fix (TVar (TV "b")))))]
  -- in print $ solve cs
  (filename:_) <- getArgs
  file <- readFile filename
  case parse file of
    Left s -> putStrLn s
    Right tls -> do
      print tls
      let (datadecs, eFunStmts) = groupAfterParsing tls
      resolveAll (TypeID 0) datadecs eFunStmts >>= \case
        Left res -> do
          putStrLn "Resolve Errors"
          print res
        Right (_, rmodule) -> do
          putStrLn $ ppModule rmodule
          case typecheck rmodule of
            Left ne -> print ne
            Right module'@(TModule funs _ tstmts) -> do
              putStrLn $ ppShow module'
              let (funs, stmts) = monomorphize module'
              writeFile "test.c" $ pp funs tstmts
              callCommand "gcc test.c"
