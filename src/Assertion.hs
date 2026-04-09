{-# LANGUAGE LambdaCase #-}
module Assertion (module Assertion) where
import AST.Def (pf, UniqueVar (varName), VarName (..))
import Control.Monad.State (State, runState, execState, evalState, StateT, evalStateT, lift)
import qualified Control.Monad.State as State
import TypingContext (TypingContext)
import AST.Common (Module, AnnStmt, functions, Function (functionDeclaration), FunDec (functionId, functionEnv))
import AST.Mono (M)
import AST.Typed (TC, exports)
import Data.List.NonEmpty (NonEmpty)
import Data.Foldable (find)
import Data.String (fromString)
import qualified Data.Text as Text
import qualified TypingContext as TC
import qualified AST.Typed as T
import Data.Char (isDigit)


data Assertion
  = EnvSize VarName Int
  deriving Show

data CodeState = CodeState TypingContext (NonEmpty (Module TC)) (Module M)
checkAssertion :: CodeState -> Assertion -> Maybe AssertionError
checkAssertion (CodeState tc mods _) = \case
  EnvSize name size ->
    let mfun = find (\fn -> fn.functionDeclaration.functionId.varName == name) $ foldMap (functions . exports) mods
    in case mfun of
      Just fn ->
        let (T.EnvDef _ env _) = TC.getEnv tc fn.functionDeclaration.functionEnv
        in assert (length env == size) $ pf "%: Expected env size: %. Actual env size: %. (%)" fn.functionDeclaration.functionId size (length env) env
      Nothing -> Just $ pf
        "Could not find function with name %." name

assert :: Bool -> String -> Maybe AssertionError
assert cond err = if cond
  then Nothing
  else Just err

type FunName = String
type AssertionParseError = String
type AssertionError = String
type OGAssertion = String



type Parser a = StateT ([String], Int) (Either (OGAssertion, AssertionParseError)) a
parseAssertion :: OGAssertion -> Either (OGAssertion, AssertionParseError) Assertion
parseAssertion ogass = startParsing $ \case
  "envsize" -> do
    fnname <- expectName
    expectedSize <- expectNum
    pure $ EnvSize (VN $ Text.pack fnname) expectedSize
  unknownName -> justError $ pf
    "Unknown function name: %" unknownName

  where
    expectName :: Parser String
    expectName = next

    expectNum :: Parser Int
    expectNum = do
      s <- next
      if all isDigit s
        then pure (read s)
        else justError $ pf
          "Expected number, but got '%'." s

    startParsing :: (String -> Parser a) -> Either (OGAssertion, AssertionParseError) a
    startParsing fn =
      case words ogass of
        [] -> Left (ogass, "Empty assertion.")
        (name : args) -> evalStateT (fn name) (args, 0)

    next :: Parser String
    next = do
      (args, idx) <- State.get
      if idx < length args
        then do
          State.modify' $ fmap (+1)
          pure (args !! idx)
        else do
          justError $ pf "Expected arg %, but got no more arguments." (idx + 1)

    justError :: String -> Parser a
    justError errmsg = lift $ Left (ogass, errmsg)

