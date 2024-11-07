{-# LANGUAGE LambdaCase, OverloadedRecordDot #-}
module Std (preparePrelude, preludePath, prepareStd) where
import Paths_KindaC (getDataFileName)
import AST.Converged (Prelude (..), unitName, tlReturnTypeName, boolTypeName, intTypeName)
import Pipeline (loadModule)
import qualified Data.Text as Text
import AST.Common (Module, Annotated (..), UniqueCon(..), UniqueType(..), UniqueVar(..), Result (..), fromResult, LitType (..), Type, TCon)
import AST.Typed (Typed)
import qualified AST.Typed as T
import qualified AST.Typed as T
import Data.Text (Text)
import Data.Fix (Fix(..))
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.List.NonEmpty (NonEmpty)
import Data.Map ((!?))
import Data.Functor ((<&>))
import qualified Data.List.NonEmpty as NonEmpty


-- Right now all relies on the data directory.
-- When I distribute it, I might want to use TemplateHaskell to embed source files!

preludePath :: String
preludePath = "kcsrc/prelude.kc"

preparePrelude :: IO Prelude
preparePrelude = do
  fn <- getDataFileName preludePath
  tmodule <- loadModule Nothing fn
  pure $ case tmodule of
    Left errors -> error $ unlines
      [ "OH SHIT MAN: There were errors while compiling prelude. Fix yo shit, bitch."
      , Text.unpack errors
      ]
    Right preludeModule -> 
      case makePrelude preludeModule of
        Left errors -> error $ unlines $
          "Although prelude as a module typechecked correctly, there were errors:" 
          : NonEmpty.toList errors
          
        Right prelude -> prelude


prepareStd :: IO ()
prepareStd = return ()


makePrelude :: Module Typed -> Either (NonEmpty String) Prelude
makePrelude prelude = fromResult $
  mkPrelude <$> unitOr <*> programReturnOr <*> boolTypeOr <*> intTypeOr
  where
    mkPrelude unitValue toplevelReturn boolType intType = Prelude    
      { tpModule = prelude

      , unitValue = unitValue
      , toplevelReturn = toplevelReturn
      , boolType = boolType
      , intType = intType

      , varNames = vars
      , conNames = cons
      , tyNames = types
      }

    -- check if there is a Unit type
    unitOr = case cons !? unitName of
      Just (uniqueType, [], [], T.DC unitCon []) -> 
        let unitType = Fix $ T.TCon uniqueType [] []  -- reconstruct the type of constructor
        in Success (unitCon, unitType)

      Just (ut, tvars, _, T.DC uc apps) ->
        Failure $ ne $ "[PRELUDE ERROR]: You may not use constructors that require arguments or their types require parameters. "  <> show uc <> " " <> show ut <> " " <> show apps <> " " <> show tvars
      Nothing -> Failure $ ne $ "[PRELUDE ERROR]: Could not find any constructor with the name '" <> show unitName <>  "'."

    -- gather all the types used by the compiler (right now, bad types are not checked for :) 

    programReturnValue = T.Lit (LInt 0)  -- default return value is zero
    programReturnOr = programReturnTypeOr <&> \prt -> Fix $ T.ExprType prt programReturnValue

    programReturnTypeOr = tryFindType "the default top level return type" tlReturnTypeName
    boolTypeOr = tryFindType "the boolean type" boolTypeName
    intTypeOr = tryFindType "the default interger type" intTypeName


    tryFindType :: String -> TCon -> Result (NonEmpty String) (Type Typed)
    tryFindType reason tcon = case types !? tcon of
      Just (T.DD uniqueType tvars unions _) -> Success $ Fix $ T.TCon uniqueType (Fix . T.TVar <$> tvars) unions
      Nothing -> Failure $ ne $ "[PRELUDE ERROR]: Could not find a type to represent " <> reason <> "of the program. Looking for '" <> show tcon <> "'."

    ne :: String -> NonEmpty String
    ne = NonEmpty.singleton


    -- gather all of this shit (copied from Resolver)
    cons = Map.fromList $ fmap (\(dc@(T.DC ci _), ty, unions, ts) -> (ci.conName, (ty, ts, unions, dc))) $ foldMap extractCons $ T.fromMod prelude
    extractCons = \case
      Fix (T.AnnStmt _ (T.DataDefinition (T.DD ty tvars unions dcons))) -> fmap (\(Annotated _ dccon) -> (dccon, ty, unions, tvars)) dcons
      _ -> []

    types = Map.fromList $ mapMaybe extractTypes $ T.fromMod prelude
    extractTypes = \case
      -- TODO, but not really: Expecting that Int and Bool types have no parameters, arguments and evironments, but this is not checked. :)
      Fix (T.AnnStmt _ (T.DataDefinition dd@(T.DD tid _ _ _))) -> Just (tid.typeName, dd)
      _ -> Nothing

    -- right now, we're only taking functions and IMMUTABLE variables. not sure if I should include mutable ones
    vars = Map.fromList $ mapMaybe extractVars $ T.fromMod prelude
    extractVars = \case
      Fix (T.AnnStmt _ (T.Assignment v (Fix (T.ExprType t _)))) -> Just (v.varName, Right (v, t))
      Fix (T.AnnStmt _ (T.FunctionDefinition fd@(T.FD _ v _ _) _)) -> Just (v.varName, Left fd)
      _ -> Nothing
