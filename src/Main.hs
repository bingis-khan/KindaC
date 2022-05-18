{-# LANGUAGE TupleSections #-}
module Main where

import Parser
import Resolver (resolveAll)
import Data.Functor.Foldable (cata)
import AST
import Typecheck (typecheck)
import CPrettyPrinter (pp)
import ASTPrettyPrinter (ppModule)

import System.Process (callCommand)
import System.Environment (getArgs)
import Data.Set (Set)


groupAfterParsing :: [TopLevel] -> ([UDataDec], [Either UFunDec UStmt])
groupAfterParsing =  mconcat . map go
  where 
    go (FunDec fd) = (mempty, pure (Left fd))
    go (TLStmt stmt) = (mempty, pure (Right stmt))
    go (DataDec dd) = (pure dd, mempty)

main :: IO ()
main = do
  (filename:_) <- getArgs
  file <- readFile filename
  case parse file of
    Left s -> putStrLn s
    Right tls -> 
      let (datadecs, eFunStmts) = groupAfterParsing tls
      in case resolveAll (TypeID 0) (Global 0) datadecs eFunStmts of
        Left res -> print res
        Right (_, _, rmodule) -> case typecheck rmodule of
          Left ne -> print ne
          Right tstmts -> do
            writeFile "test.c" $ pp tstmts
            callCommand "gcc test.c"
