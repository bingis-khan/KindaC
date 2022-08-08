{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Resolver (resolveAll, bmUnion) where

import AST hiding (datatypes)
import qualified AST

import Control.Monad.Trans.State ( runState, withState, StateT(runStateT), State, evalState )
import qualified Control.Monad.Trans.State as ST
import Lens.Micro
import Lens.Micro.TH
import Control.Applicative (Const, liftA2)
import Data.Foldable (fold, traverse_)
import Data.Functor.Identity (Identity)
import Data.Functor.Foldable (cata, refold, transverse, Base, embed, hoist)
import Data.Fix (Fix(Fix), hoistFix, foldFix)

import Data.Map (Map, (!), (!?))
import qualified Data.Map as M

import Data.Bimap (Bimap, (!>))
import qualified Data.Bimap as BM

import Data.Set (Set, (\\))
import qualified Data.Set as S

import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Semigroup (sconcat)
import Data.Bifunctor (first)
import Data.Maybe (catMaybes, mapMaybe, listToMaybe, isJust, fromMaybe)
import Debug.Trace (trace, traceShowId)
import Data.Bifoldable (bifoldr, bifold, biconcatMap)
import Control.Monad ((<=<), when)
import Data.Tuple (swap)
import Data.Coerce (coerce)
import Control.Monad.Trans.Reader (Reader, runReader)
import qualified Control.Monad.Trans.Reader as R
import Control.Monad.Trans.RWS (RWS, runRWS, modify, get, tell, ask, withRWS)
import Control.Monad.Trans.Writer (Writer, runWriter)
import qualified Control.Monad.Trans.Writer as W
import Data.List (sort, group)
import Data.Bitraversable (bitraverse)
import Data.Either (partitionEithers)
import Control.Monad.Trans.Class (lift)
import GHC.IO (unsafePerformIO)




data ResolveError
  = UndeclaredVariable String
  | RedeclaredVariable String

  | UndeclaredType String Int -- Type name & arity
  | RedeclaredType String

  | RepeatingTVar TVar
  | FTVInDataConstructor TVar
  deriving Show


type Globals = Bimap String Global
type Datatypes = Map String TypeID

data TopLevelBindings' = TLBindings
  { _globalIDs :: [Global]
  , _globals :: Globals

  , _typeIDs :: [TypeID]
  , _datatypes :: Datatypes
  }

makeLenses ''TopLevelBindings'

-- I know that writer is not generally used, but it's perfect for errors.
-- At top level, we need TLBindings as State, but in functions, we don't want to modify anything - except errors.
-- That's basically RWS.
type TopLevelBindings = StateT TopLevelBindings' (Writer [ResolveError])


type Locals = Bimap String Local

data Bindings' = Bindings'
  { _localIDs :: [Local]
  , _variables :: NonEmpty Locals
  }

makeLenses ''Bindings'
type Bindings = RWS TopLevelBindings' [ResolveError] Bindings'



initialTLBindings :: TypeID -> Global -> TopLevelBindings'
initialTLBindings lastTypeID lastGlobal = TLBindings
  { _globalIDs = [lastGlobal ..]
  , _globals = BM.empty

  , _typeIDs = [lastTypeID ..]
  , _datatypes = M.empty
  }

initialBindings :: Bindings'
initialBindings = Bindings'
  { _localIDs = coerce [(1 :: Int) ..]
  , _variables = NE.singleton BM.empty
  }



--------------------------------------------
-- Classes
--------------------------------------------
class TopLevelResolvable r where
  resolveTL :: r String String String -> TopLevelBindings (r TypeID Global Local)

-- Newtypes so that the kind is the same for all parts of the AST.
-- Maybe types with TypeSynonymInstances would be better?
newtype R'FunDec  t g l = R'FunDec  { fromR'FunDec :: FunDec g l (Maybe (Type t)) (R'Stmt t g l) } deriving (Eq, Ord, Show)
newtype R'DataCon t g l = R'DataCon { fromR'DataCon :: DataCon g t } deriving (Eq, Ord, Show)
newtype R'DataDec t g l = R'DataDec { fromR'DataDec :: DataDec g t (R'DataCon t g l) } deriving (Eq, Ord, Show)

-- A bit of a hack, since all of the datatypes have (Type t) and not just t.
-- Cast it when we want to use it.
newtype R'Type t g l = R'Type { fromR'Type :: Type t } deriving (Eq, Ord, Show)

newtype R'List  a t g l     = R'List    { fromR'List :: [a t g l] }
newtype R'NList a t g l     = R'NList   { fromR'NList :: NonEmpty (a t g l) }
newtype R'Either e a t g l  = R'Either  { fromR'Either :: Either (e t g l) (a t g l) }


class Resolvable r where
  resolve :: r String String String -> Bindings (r TypeID Global Local)

-- Newtypes to be used with the Resolvable class.
newtype R'Expr  t g l = R'Expr    { fromR'Expr :: Expr l g } deriving (Eq, Show)
newtype R'Stmt  t g l = R'Stmt    { fromR'Stmt :: Stmt l g (R'Expr t g l) } deriving (Eq, Show)


toR'Stmt :: UStmt -> R'Stmt String String String
toR'Stmt = R'Stmt . hoistFix coerce   -- Conversion function, because coerce does not terminate, becuase of that y-combinator (Fix datatype).

fromR'Stmt' :: R'Stmt TypeID Global Local -> RStmt
fromR'Stmt' = hoistFix coerce . fromR'Stmt



-- Instances
instance TopLevelResolvable r => TopLevelResolvable (R'List r) where
  resolveTL = fmap R'List . traverse resolveTL . fromR'List

-- Nope, we need to do something special, so I'd not want to make an instance.
-- instance (TopLevelResolvable e, TopLevelResolvable a) => TopLevelResolvable (R'Either e a) where
--   resolveTL (R'Either e) = R'Either <$> bitraverse resolveTL resolveTL e


nextLocal :: Bindings Local
nextLocal = do
  bs <- get

  let l = head $ bs ^. localIDs
  modify $ \b -> b & localIDs %~ tail
  pure l


defineVar :: String -> Bindings Local
defineVar name = do
  localId <- nextLocal
  bs <- get

  let currentScope = (\cs -> concat ["In scope: ", show cs, ", define var: ", name] `trace` cs) $ NE.head $ bs ^. variables
  if BM.member name currentScope
    then tell [RedeclaredVariable name]
    else modify $ \bs -> bs & variables . ix 0 %~ BM.insert name localId

  pure localId



-- I know sentinel values with such a typesystem are bad, but I think it's just less annoying.
badGlobal = Global 0
badType = TypeID 0

-- Attempts to find a variable in scope.
-- First looks for it in locals, then in globals and if it does not find one
-- just throws an error and binds whatever.
findVar :: String -> Bindings (Either Global Local)
findVar name = do
  locals <- (^. variables) <$> get
  globals <- (^. globals) <$> ask

  let scopesWithLocal = NE.filter (BM.member name) locals -- All of the scopes with the variable.
  case scopesWithLocal of
    (scope : _) -> pure $ Right $ scope BM.! name
    []          -> case globals BM.!? name of
      Just gl -> pure $ Left gl
      Nothing -> tell [UndeclaredVariable name] >> pure (Left badGlobal)


findType :: String -> Int -> TopLevelBindings TypeID
findType name kind = do
  datatypes <- (^. datatypes) <$> ST.get

  case datatypes !? name of
    Nothing -> do
      tlError (UndeclaredType name kind)
      return (TypeID 0)
    Just gl ->
      return gl




-- References an already pre-scraped type.
existingType :: String -> TopLevelBindings TypeID
existingType name = do
  gs <- ST.get
  return $ fromMaybe (error $ concat ["Resolver error: Datatype '", name, "' is not defined, but *should* be."]) $ (gs ^. datatypes) !? name

-- This is the function to reference already "pre-scraped" globals - in this case functions and datatype constructors.
-- Bad stuff:
-- id = 1
-- id (x)
--   return x
-- print id  # What the fuck? Right now, it will print '1'.
existingGlobal :: String -> TopLevelBindings Global
existingGlobal name = do
  gs <- ST.get
  return $ fromMaybe (error $ concat ["Resolver error: Global '", name, "' is not defined, but *should* be."]) $ (gs ^. globals) BM.!? name

instance TopLevelResolvable R'Type where
  resolveTL (R'Type t) = R'Type <$> mapARS go t
    where
      go :: Base (Type String) (TopLevelBindings (Type TypeID)) -> TopLevelBindings (Base (Type TypeID) (Type TypeID))
      go (TCon name apps) = do
        apps' <- sequenceA apps
        t <- findType name (length apps')
        pure $ TCon t apps'

      -- Trash.
      go (TDecVar tdv) = pure (TDecVar tdv)
      go (TVar tv) = pure (TVar tv)
      go (TFun args ret) = liftA2 TFun (sequenceA args) ret


-- Finds a type. A convenience function to the R'Type instance
-- which automatically does the newtype conversions.
typeType :: UntypedType -> TopLevelBindings TypedType
typeType = coerce . resolveTL . R'Type


instance TopLevelResolvable R'DataCon where
  resolveTL (R'DataCon (DC name ts)) = do
    g <- existingGlobal name
    ts' <- traverse typeType ts
    return $ R'DataCon $ DC g ts'


-- In the future, maybe use the Typecheck's ftv, since it should be the same.
dcsftv :: (Functor f, Foldable f) => f (R'DataCon t g l) -> Set TVar
dcsftv = foldMap (godc . fromR'DataCon)
  where
    godc (DC _ ts) = mconcat $ map got ts
    got = cata $ \case
      (TVar tv) -> S.singleton tv
      t -> fold t

tlError :: ResolveError -> TopLevelBindings ()
tlError err = lift $ W.tell $ pure err

instance TopLevelResolvable R'DataDec where
  -- Note, that we assume that the names already exist in top level bindings,
  -- because we should've scraped them beforehand. So, instead of adding a global for the name
  -- we just look it up in the environment.
  resolveTL (R'DataDec (DD name tvs cons)) = do
    t <- existingType name

    let tvarSet = S.fromList tvs

    -- Check for repetitions and report an error if they exist.
    let repetitions = map head $ filter ((> 1) . length) $ group $ sort tvs
    traverse_ (tlError . RepeatingTVar) repetitions

    cons' <- traverse resolveTL cons

    -- Report any free type variables in data constructor.
    let ftvs = dcsftv cons'
    traverse_ (tlError . FTVInDataConstructor) $ ftvs \\ tvarSet

    -- In the future change the type to reflect the fact that tvars are unique.
    return $ R'DataDec $ DD t (S.toList tvarSet) cons'

-- instance TopLevelResolvable R'FunDec where
--   resolveTL (R'FunDec (FD name params ret body)) = do
--     g <- addOverwriteGlobal name   -- Special behaviour. We assume the right global is already here.
--     params' <- (traverse . traverse . traverse) typeType params  -- Resolve types but *not* names. It's just easier to do it here.
--     ret' <- traverse typeType ret

--     let
--       defineParameters :: [(String, t)] -> Bindings [(Local, t)]
--       defineParameters = traverse $ \(name, t) -> (,t) <$> defineVar name

--     -- And resolve the body, yo.
--     ((params'', body'), _) <- runBindings initialBindings $
--       liftA2 (,) (defineParameters params') (traverse resolve body)  -- Note, that we don't have to create a new scope -> outermost is the default.

--     return $ R'FunDec $ FD g params'' ret' body'

resolveFunDec :: Globals -> Global -> UFunDec -> TopLevelBindings (R'FunDec TypeID Global Local)
resolveFunDec gs g (FD name params ret body) = do
    params' <- (traverse . traverse . traverse) typeType params  -- Resolve types but *not* names. It's just easier to do it here.
    ret' <- traverse typeType ret

    let
      defineParameters :: [(String, t)] -> Bindings [(Local, t)]
      defineParameters = traverse $ \(name, t) -> (,t) <$> defineVar name

    -- And resolve the body, yo.
    ((params'', body'), _) <- runBindings initialBindings $ withRWS (\r s -> (r & globals %~ (`bmUnion` gs), s)) $
      liftA2 (,) (defineParameters params') (traverse (resolve . R'Stmt . hoistFix coerce) body)  -- Note, that we don't have to create a new scope -> outermost is the default.

    return $ R'FunDec $ FD g params'' ret' body'


asVar :: Either String String -> String
asVar = either id id  -- Bad life choices - see Expr in AST. 

instance Resolvable R'Expr where
  resolve = fmap R'Expr . transverse go . fromR'Expr
    where
      go = \case
        Lit l     -> pure $ Lit l
        Var name  -> Var <$> findVar (asVar name)
        Op l op r -> Op <$> l <*> pure op <*> r
        Call c args -> Call <$> c <*> sequenceA args



type PreStmt = Stmt String String (R'Expr TypeID Global Local)
type PostStmt = Stmt Local Global (R'Expr TypeID Global Local)

beginScope :: NonEmpty (Bindings PostStmt) -> Bindings (NonEmpty PostStmt)
beginScope body = do
  scopes <- get <&> \bs -> bs ^. variables
  modify $ \bs -> bs & variables .~ NE.cons BM.empty scopes
  bod <- sequenceA body
  modify $ \bs -> bs & variables .~ scopes   -- Kinda bad, but I thought we would be able to do some kind of temporary modification with state.

  return bod

instance Resolvable R'Stmt where
  resolve = fmap R'Stmt . mapARS (go <=< bindExpr resolve) . fromR'Stmt
    where
      go :: Base PreStmt (Bindings PostStmt) -> Bindings (Base PostStmt PostStmt)
      go (Print expr) = pure $ Print expr
      go (Assignment name expr) = defineVar name <&> \localId -> Assignment localId expr
      go (ExprStmt expr) = pure $ ExprStmt expr
      go (If cond ifTrue elseIfs ifFalse)
        =   If cond
        <$> beginScope ifTrue
        <*> (traverse . traverse) beginScope elseIfs
        <*> traverse beginScope ifFalse
      go (Return expr) = pure $ Return expr



-- Adds a new type and returns a sentinel value if
-- the type already exists (with an error).
addType :: String -> TopLevelBindings TypeID
addType typename = do
  dts <- ST.get <&> (^. datatypes)
  case dts !? typename of
    Nothing -> do
      nextTypeID <- ST.get <&> (\tlbs -> head (tlbs ^. typeIDs))
      ST.modify (\tlbs -> tlbs & typeIDs %~ tail & datatypes %~ M.insert typename nextTypeID)
      return nextTypeID
    Just ti -> do
      tlError (RedeclaredType typename)
      return badType


addGlobalWithID :: String -> Global -> TopLevelBindings ()
addGlobalWithID name gid =
  ST.modify (\tlbs -> tlbs & globals %~ BM.insert name gid)

forceGlobalWithID :: String -> Global -> TopLevelBindings ()
forceGlobalWithID name gid = do
  tlError (RedeclaredVariable name)
  addGlobalWithID name gid

checkGlobal :: String -> TopLevelBindings (Maybe Global)
checkGlobal name = ST.get <&> \tlbs -> (tlbs ^.globals) BM.!? name

-- If a global exists, overrides it.
-- If it doesn't - creates a new one.
addOverwriteGlobal :: String -> TopLevelBindings Global
addOverwriteGlobal name = do
  mGid <- traceShowId <$> checkGlobal (traceShowId name)
  gid <- case mGid of
    Nothing -> do
      nextGlobalID <- ST.get <&> \tlbs -> head (tlbs ^. globalIDs)
      ST.modify $ \tlbs -> tlbs & globalIDs %~ tail
      return nextGlobalID
    Just gid -> return gid

  addGlobalWithID name gid
  return gid

-- Adds a new global and returns a sentinel value
-- if the global already exists.
addGlobal :: String -> TopLevelBindings Global
addGlobal name = do
  mGid <- checkGlobal name
  case mGid of
    Nothing -> do
      -- Duplicate code. Should create some sort of "Dispenser" datatype.
      addOverwriteGlobal name
    Just ti -> do
      tlError (RedeclaredVariable name)
      return badGlobal


-- Add an existing local from locals to globals.
addTLVar :: Locals -> Local -> TopLevelBindings Global
addTLVar locals local = do
  let localName = locals !> local

  -- TLVars can shadow functions. AddGlobal will signal an error.
  addOverwriteGlobal localName


-- "runs" Bindings on TopLevelBindings -> converts between top level and function level.
runBindings :: Bindings' -> Bindings a -> TopLevelBindings (a, Bindings')
runBindings bindings bindingsRWS = do
  r <- ST.get
  let (a, bindings', errs) = runRWS bindingsRWS r bindings
  traverse_ tlError errs
  return (a, bindings')


-- This is only used for resolving statements - it will manage the
-- combined state of both Bindings and TopLevelBindings.
data TopLevelStatementResolver' = TLSR TopLevelBindings' Bindings' [ResolveError]
type TopLevelStatementResolver = State TopLevelStatementResolver'

tlsrRunBindings :: Bindings a -> TopLevelStatementResolver a
tlsrRunBindings f = do
  TLSR _ bs _ <- ST.get

  (x, bs') <- tlsrRunTLBindings $ runBindings bs f

  ST.modify $ \(TLSR tlbs _ errs) -> TLSR tlbs bs' errs
  return x

bmUnion :: (Ord a, Ord b) => Bimap a b -> Bimap a b -> Bimap a b
bmUnion l r = foldr (uncurry BM.insert) r $ BM.toList l

-- Runs TLBindings with user supplied globals.
-- Note: the ones already declared have priority.
tlsrRunTLBindings :: TopLevelBindings a -> TopLevelStatementResolver a
tlsrRunTLBindings f = do
  TLSR tlbs bs errs <- ST.get
  let
    ((x, tlbs''), errs') = runWriter $ runStateT f tlbs
  ST.put $ TLSR tlbs'' bs (errs <> errs')
  return x

ensureGlobalIsUndeclared :: String -> TopLevelStatementResolver ()
ensureGlobalIsUndeclared name = do
  funNameGlobal <- tlsrRunTLBindings $ checkGlobal name

  -- Error + recovery. We assume the function being here is correct.
  case funNameGlobal of
    Nothing -> pure () -- Cool, nothing is declared.

    -- Bad: a top-level variable with this name was already declared.
    Just g -> do
      -- Signal error and recover (we prefer replace the gid again with that of the function).
      tlsrRunTLBindings $ tlError (RedeclaredVariable name)


-- For now, only top level statements.
-- Resolves all, nuff said. 
-- RModule ~ Set RDataDec, Set RFunDec, (Int, [RTLStmt])
resolveAll :: TypeID -> Global -> [UDataDec] -> [Either UFunDec UStmt] -> Either (NonEmpty ResolveError) (TypeID, Global, RModule)
resolveAll nextTypeID nextGlobalID dds tls = case errs of
  []      -> Right (lastTypeID, lastGlobalID, rmodule)
  x : xs  -> Left (x :| xs)
  where
    -- NO! Haskell is a declarative language!
    -- I'm gonna make datatypes that represent what I want to do.
    -- NO SHORTCUTS!

    -- So, what I want:
    -- Get function names and datatype constructors - assign globals and check for repetitions.
    -- Get datatype names and check for repetitions.
    -- Now we have all of the globals and types (except for variables). That's that.

    -- Then, time to check all of the variables.
    -- We can use the mechanism from Resolvable.
    -- Treat global variables as normal variables and check them.
    -- That's what `check` is doing. Okay, it's done.
    -- All of the errors are caught here.

    -- Set up all of the state.
    ((rmodule, tlbs), errs) = runWriter (runStateT doStuff (initialTLBindings nextTypeID nextGlobalID))

    lastTypeID = head $ tlbs ^. typeIDs
    lastGlobalID = head $ tlbs ^. globalIDs

    -- Obviously temporary name.
    -- Main function for resolving the module.
    doStuff :: TopLevelBindings RModule
    doStuff = do
      -- Register each type.
      let typeNames = map (\(DD name _ _) -> name) dds  -- Get all type names.
      traverse_ addType typeNames

      -- Now, we want to find each global EXCEPT global variables.
      let functionNames = mapMaybe (either (\(FD name _ _ _) -> Just name) (const Nothing)) tls
          dataConstructorNames = concatMap (\(DD _ _ dcons) -> map (\(DC name _) -> name) $ NE.toList dcons) dds
      traverse_ addGlobal $ functionNames <> dataConstructorNames  -- Data constructors and function names start from upper and lower case letters respectively, so overlap is not possible. But we do the same thing, so I decided to join 'em.

      -- We now have all of the globals resolved (except variable names - we're gonna do it right now).

      -- Now onto actual resolving.
      -- First, we take care of data declarations - EZPZ.
      -- This might be a good time to check kinds?
      dds' <- S.fromList . map coerce . fromR'List <$> resolveTL (coerce dds :: R'List R'DataDec String String String)

      -- Now we'll start checking functions and top-level statements.
      -- tls' <- traverse (bitraverse (resolveTL . R'FunDec . fmap toR'Stmt) pure) tls

      -- Now, we can do the funny thing.
      -- In top level, declaration order matters. Why?
      -- x = f()
      -- f ()
      --   print x
      -- What the fuck?
      -- So, we throw our current globals out (except data constructors - they will never conflict - although maybe throwing them out and having them be "declared" will be the least surprising option?)
      -- Right now, no globals can repeat.
      -- But, do we allow top level redeclarations?
      -- Only redeclaration of a function with a top-level ?  <-- this one
      -- So, when we are resolving a statement, we have to delete all of the functions
      -- BUT leave the globals which were already declared.

      -- Save the current global state.
      availableGlobals <- (\x -> ("Available globals: " ++ show x) `trace` x) . (^. globals) <$> ST.get
      tlbs' <- ST.get

      let
          withAvailableGlobals = withState (\(TLSR tlbs bs res) -> TLSR (tlbs & globals %~ flip bmUnion availableGlobals) bs res)

          onFunOrStmt :: Either UFunDec UStmt -> TopLevelStatementResolver (Either (R'FunDec TypeID Global Local) (R'Stmt TypeID Global Local))
          -- On a top-level assignment, resolve the statement and add a global with this name.
          onFunOrStmt (Right stmt@(Fix (Assignment name _))) = do  -- Make a global out of the top level variable.
            rstmt <- tlsrRunBindings $ resolve $ toR'Stmt stmt
            tlsrRunTLBindings $ addOverwriteGlobal name
            return $ Right rstmt

          -- Normal statement - just resolve.
          onFunOrStmt (Right stmt) = do
            rstmt <- tlsrRunBindings $ resolve $ toR'Stmt stmt
            return $ Right rstmt

          -- Function - just resolve. Note, that functions cannot redeclare global variables.
          -- Also note, that, because functions can access each function no matter
          -- where it's declared, we use a special function to "inject" them.
          onFunOrStmt (Left ufd@(FD name _ _ _)) = do
            ensureGlobalIsUndeclared name
            let functionGid = availableGlobals BM.! name
            rfd <- tlsrRunTLBindings $ resolveFunDec availableGlobals functionGid ufd
            return $ Left rfd

          noFunTLBS = tlbs' & globals %~ \gs -> foldr BM.delete gs functionNames
          (tls'', TLSR tlsrTLBs tlsrBs errs) = runState (traverse onFunOrStmt tls) $ TLSR noFunTLBS initialBindings []

          -- We have to create a mapping between added globals and 

          -- Now we have functions :D as a set and top level statements
          (funs, tlStmts) = first (S.fromList . map coerce) $ partitionEithers tls''


          -- Now scrape all of the top level globals.
          -- We are searching for top-level assignments and we know,
          -- that those variables are accessible.

          scrapeAssignment (Right (Fix (Assignment name _))) = Just name
          scrapeAssignment _ = Nothing

          getBoth name = do
            l <- tlsrRunBindings (findVar name) <&> \case
               Right lo -> lo
               Left gl -> error "Resolver error: Huh? This local does not exist??? That... should not be possible."

            g <- tlsrRunTLBindings (checkGlobal name) <&> \case
              Just gl -> gl
              Nothing -> error "Resolver error: Huh??? This should have a global"

            return (l, g)

          tlgs = BM.fromList $ evalState (traverse getBoth $ mapMaybe scrapeAssignment tls) $ TLSR tlsrTLBs tlsrBs []

      lift $ W.tell errs

      -- Now, we can check for cycles. Todo! But it should be easy.
      -- undefined

      -- We can remove top-level variables from tlgs which were never used.
      -- todo

      -- And lastly, return the module.
      return $ RModule
        { rmFunctions = S.map (fmap fromR'Stmt' . fromR'FunDec) funs
        , rmDataDecs = dds'
        , rmTLStmts = map fromR'Stmt' tlStmts
        , rmTLLocaLGlobals = tlgs
        }


    -- Now for the resolving itself.
    -- Gather type names (they are all unique by this point) and assign them TypeIDs (ie: return a map).
    -- Now, assign each type mentioned in a type its TypeID.
    -- Then, gather (and map) data constructors to globals.
    -- Datatypes are done.

    -- Gather all of the function globals
    -- Keep all of the globals. Start resolving variable names.
    -- For each top level assignment, a corresponding global is generated. Also, keep track of which top level locals map to global bindings.
    --   OHSHID: How do I resolve locals for top level statements and functions simultaneously (where those locals are actually globals)? We need a persistent Bindings state and simultaneously keep adding stuff to TopLevel Bindings?
    --   There's a way. First, resolve top level statements, but keep the in either. Then, the type is roughly: [Either UFunDec RStmt]. After this, go through them and only add globals (and maps) on top level assignments.

    -- Then each function will create the appropriate bindings (remember the local-globals of top level statements) and start resolving the body - that's what we already have, so I won't elaborate.
    -- Now that we have a resolved body, finish that function.
    -- Do that for everything.
    -- That's it c:
    -- Additionally, you can check for cycles in data definitions later and check that kinds match.

    -- I kinda think Vars is a bad idea - parse, don't validate!
    -- We can keep redeclarations and undefined variables just as easily.
    -- Okay, time to refactor.
  