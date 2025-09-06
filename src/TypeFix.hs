{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE OverloadedRecordDot #-}
module TypeFix (typefix) where

import qualified AST.Typed as T
import Data.List.NonEmpty (NonEmpty)
import AST.Common (Module, AnnStmt, Function (..), DataDef (..), ClassDef (..), InstDef (..), StmtF (..), Expr, XMutAccess, IfStmt (..), CaseF (..), Type, TypeF (..), TVar (..), XEnvUnion, XEnv, ClassFunDec (..), InstFun (..), Decon, DeconF (..), ExprNode (N), XExprNode, DataCon (..), ExprF (..), LitType (..), XMem, XLamOther, ClassType, FunDec (..), ClassTypeF (..), MutAccess (..))
import AST.Typed (TC, T, topLevelStatements, TOTF (..), EnvUnionF, ScopeSnapshot, Scheme (..), FunOther (..), EnvUnion, FunctionTypeAssociation (..), ExprNode (ExprNode), LamDec (..), TypeFixStats (..))
import AST.Def (PrintContext, type (:.) (O), sequenceA2, traverse2, traverseSet, traverse3, pf, Counter)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Strict as RWST
import Misc.Memo (Memo, emptyMemo, memo, qmemo, memo')
import Data.Functor.Foldable (cata, project, embed)
import qualified AST.Def as Def
import Data.Bitraversable (bitraverse)
import Data.Fix (Fix(..))
import Control.Monad ((>=>))
import Data.Traversable (for)
import Control.Applicative (liftA3)
import Data.Map.Strict ((!?))
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Foldable (find, fold)
import Data.Functor ((<&>))
import Data.Either (fromRight)
import Data.Biapplicative (first)


typefix :: T.TypeUni -> T.EnvAdditions -> NonEmpty (Module TC) -> PrintContext (Module T, TypeFixStats)
typefix typeUni envAdds mods = do
  let stmts = concatMap topLevelStatements mods
  (modt, mem, ()) <- RWST.runRWST (fixStmts stmts) (typeUni, envAdds) emptyMemoShit
  pure (modt, TypeFixStats { tfTypeNodesVisited = mem.typeNodesVisited, tfUnionsVisited = mem.unionsVisited })

fixStmts :: [AnnStmt TC] -> TypeFix (Module T)
fixStmts = traverse fixStmt

fixStmt :: AnnStmt TC -> TypeFix (AnnStmt T)
fixStmt = cata $ \(O (O (Def.Annotated anns (Def.Located loc stmt)))) -> do
  stmt' <- bitraverse fixExpr pure stmt
  stmt'' <- fixStmtF stmt'
  pure $ Fix $ O $ O $ Def.Annotated anns $ Def.Located loc stmt''
  where
    fixStmtF :: StmtF TC (Expr T) (TypeFix (AnnStmt T)) -> TypeFix (StmtF T (Expr T) (AnnStmt T))
    fixStmtF = \case
      Pass -> pure Pass
      Print expr -> pure $ Print expr
      Assignment var loc expr -> pure $ Assignment var loc expr
      Mutation var loc other accesses expr -> do
        taccesses <- traverse fixMutAccess accesses
        pure $ Mutation var loc other taccesses expr
      If ifstmt -> If <$> fixIfStmt ifstmt
      Switch cond cases -> Switch cond <$> traverse fixCase cases
      ExprStmt expr -> pure $ ExprStmt expr
      Return expr -> Return <$> fixExpr expr
      While cond stmts -> do
        tstmts <- sequenceA stmts
        pure $ While cond tstmts
      Fun fn -> Fun <$> fixFun fn
      Inst inst -> Inst <$> fixInst inst
      Other () -> pure $ Other ()

fixIfStmt :: IfStmt TC (Expr T) (TypeFix (AnnStmt T)) -> TypeFix (IfStmt T (Expr T) (AnnStmt T))
fixIfStmt ifstmt = do
  ift <- sequenceA ifstmt.ifTrue
  ifels <- traverse sequenceA2 ifstmt.ifElifs
  ifel <- sequenceA2 ifstmt.ifElse
  pure $ IfStmt
    { condition = ifstmt.condition
    , ifTrue = ift
    , ifElifs = ifels
    , ifElse = ifel
    }

fixCase :: CaseF TC (Expr T) (TypeFix (AnnStmt T)) -> TypeFix (CaseF T (Expr T) (AnnStmt T))
fixCase kase = do
  tdecon <- fixDecon kase.deconstruction
  tstmts <- sequenceA kase.caseBody
  pure $ Case tdecon kase.caseCondition tstmts

fixDecon :: Decon TC -> TypeFix (Decon T)
fixDecon = cata $ \(N node deconF) -> fmap embed $ liftA2 N (fixNode node) (fixDeconF =<< sequenceA deconF) where
  fixDeconF :: DeconF TC (Decon T) -> TypeFix (DeconF T (Decon T))
  fixDeconF = \case
    CaseVariable var -> pure $ CaseVariable var
    CaseConstructor con decons -> do
      tdd <- fixCon con
      pure $ CaseConstructor tdd decons
    CaseRecord dd record -> do
      tdd <- fixDataDef dd
      pure $ CaseRecord tdd record
    CaseIgnore -> pure CaseIgnore

fixNode :: XExprNode TC -> TypeFix (XExprNode T)
fixNode en = fixType en.t <&> \tt -> ExprNode tt en.loc


fixExpr :: Expr TC -> TypeFix (Expr T)
fixExpr = cata $ \(N n e) -> fmap embed $ liftA2 N (fixNode n) (fixExprF =<< sequenceA e) where
  fixExprF :: ExprF TC (Expr T) -> TypeFix (ExprF T (Expr T))
  fixExprF = \case
    Lit lt -> pure $ Lit $ fixLitType lt
    Var v vother -> do
      tv <- fixVar v
      pure $ Var tv vother
    Con con cother -> do
      tcon <- fixCon con
      pure $ Con tcon cother

    RecCon dd mems -> do
      tdd <- fixDataDef dd
      pure $ RecCon tdd mems
    RecUpdate x mems -> pure $ RecUpdate x mems
    MemAccess x mem -> pure $ MemAccess x mem

    UnOp uop x -> pure $ UnOp uop x
    BinOp l bop r -> pure $ BinOp l bop r
    Call c as -> pure $ Call c as
    As x tt -> As x <$> fixType tt
    Lam ld params ret -> do
      tld <- fixLamDec ld
      tparams <- traverse2 fixType params
      pure $ Lam tld tparams ret

fixLamDec :: XLamOther TC -> TypeFix (XLamOther T)
fixLamDec (LamDec uv env) = LamDec uv <$> fixEnv env

fixLitType :: LitType TC -> LitType T
fixLitType = \case
  LInt i -> LInt i
  LFloat f -> LFloat f
  LString s -> LString s

fixType :: Type TC -> TypeFix (Type T)
fixType = qmemo memoType (\mem s -> s { memoType = mem }) $ getType >=> traverse fixType >=> thisAnd (RWST.modify $ \s -> s { typeNodesVisited = s.typeNodesVisited + 1 }) >=> \xxx -> do
 case xxx of
    TFun union params ret -> do
      tunion <- fixUnion union
      pure $ Fix $ TFun tunion params ret
    TCon dd tvs unions -> do
      tdd <- fixDataDef dd
      tunions <- for unions $ \(union, ts, t) -> do
        liftA3 (,,) (fixUnion union) (traverse fixType ts) (fixType t)
      pure $ Fix $ TCon tdd tvs tunions
    TO (TVar tv) -> Fix . TO . TVar <$> fixTVar tv
    TO (TyVar tyv) -> pure $ Fix $ TO $ TyVar tyv

fixClassType :: ClassType TC -> TypeFix (ClassType T)
fixClassType = cata $ sequenceA >=> fmap embed . \case
  Self -> pure Self
  NormalType nt -> NormalType <$> case nt of
    TFun union params ret -> do
      tunion <- fixUnion union
      pure $ TFun tunion params ret
    TCon dd tvs unions -> do
      tdd <- fixDataDef dd
      tunions <- for unions $ \(union, ts, t) -> do
        liftA3 (,,) (fixUnion union) (traverse fixType ts) (fixType t)
      pure $ TCon tdd tvs tunions
    TO (TVar tv) -> TO . TVar <$> fixTVar tv
    TO (TyVar tyv) -> pure $ TO $ TyVar tyv

getType :: Type TC -> TypeFix (TypeF TC (Type TC))
getType tid = do
  tu <- RWST.asks fst
  pure $ snd $ T.getTypeFromUni tu tid

fixTVar :: TVar TC -> TypeFix (TVar T)
fixTVar tv = do
  classes <- traverseSet fixClass tv.tvClasses
  pure $ TV { fromTV = tv.fromTV, binding = tv.binding, tvClasses = classes }

fixUnion :: XEnvUnion TC -> TypeFix (XEnvUnion T)
fixUnion = memo memoUnion (\mem s -> s { memoUnion = mem }) $ \uid addMemo -> mdo
  RWST.modify $ \s -> s { unionsVisited = s.unionsVisited + 1 }

  u <- getUnion uid
  let tu = T.EnvUnion { T.unionID = u.unionID, T.union = union }
  addMemo tu

  union <- for u.union $ \(muci, ufi, assocs, env) -> do
    tassocs <- traverse fixType assocs
    tenv <- fixEnv env
    pure (muci, ufi, tassocs, tenv)
  pure tu

fixEnv :: T.Env -> TypeFix (XEnv T)
fixEnv (T.RecursiveEnv eid isEmpty) = pure $ T.RecursiveEnv eid isEmpty
fixEnv (T.Env eid env locs currentEnvStack) = do
  nes <- newEnvVars
  oadd <- optionalAddition

  -- here, actually typefix 'em
  vars <- for (nes <> oadd) $ \(v, l, t) -> do
    tv <- fixVar v
    tt <- fixType t
    pure (tv, l, tt)
  pure $ T.Env eid vars locs currentEnvStack
  where
      newEnvVars = fmap fold $ traverse (tryExpandEnvironmentOfClass . (\(v, l, t) -> (v, l, t))) env

      currentLevel = Def.envStackToLevel currentEnvStack

      optionalAddition :: TypeFix [(T.Variable, Def.Locality, Type TC)]
      optionalAddition = do
        adds <- RWST.asks snd
        oldVars <- Set.fromList <$> newEnvVars
        pure $ filter (`Set.notMember` oldVars) $ fromMaybe mempty $ adds !? eid

      tryExpandEnvironmentOfClass :: (T.VariableF TC (Type TC), Def.Locality, Type TC) -> TypeFix [(T.Variable, Def.Locality, Type TC)]
      tryExpandEnvironmentOfClass = \case
        vlt@(T.DefinedClassFunction cfd@(CFD cd _ _ _ () _) snap selfid uci, _, tid) -> do
          self <- getType selfid
          unT <- getType tid >>= \case
            TFun union _ _ -> getUnion union <&> T.union
            _ -> error "should not happen!!!"
          pure $ case self of
            (TCon dd _ _) ->
              -- failable: select instantiated function env. this might have been after errors, so we're not assuming anything.
              let mvars = do
                    insts <- snap !? cd
                    currentInst <- insts !? dd
                    currentFun <- find (\ifn -> ifn.instClassFunDec == cfd) currentInst.instFuns

                    (_, ufi, assocs, e) <- find (\case { (Just uci', _, _, _) -> uci == uci'; _ -> False }) unT
                    pure (currentFun, currentInst, ufi, assocs, e)
              in case mvars of
                -- this probably is not needed anymore!
                Just (ifn, currentInst, ufi, assocs, T.Env instEnvID instEnvVars _ instEnvStack)
                  -- this function is from this or "higher" environment.
                  -- | Def.envStackToLevel instEnvStack <= currentLevel ->
                  | instEnvStack `Def.isHigherOrSameLevel` currentEnvStack ->
                  -- | Set.member instEnvID (Set.fromList (eid : currentEnvStack)) ->
                    let fnLocality = if Def.envStackToLevel instEnvStack < currentLevel
                          then Def.FromEnvironment (Def.envStackToLevel instEnvStack)
                          else Def.Local
                    in [(T.DefinedClassFunction cfd snap selfid uci, fnLocality, tid)]  -- TEMP: we are redoing the "DefinedClassFunction" (instead of just dropping DefinedFunction), because currently in Mono we rely on this.
                    -- NOTE: NOTICE THAT WE TAKE currentInst instead of using the recursive instance. This is because we don't substitute recursive instances (because we have no memoization).

                  -- we need "take out" variables from this function.
                  -- NOTE: we add the `eid` to currentEnvStack, because if inst is actually INSIDE the function, it would have `eid` in its env stack. We need it, because (due to how insts are resolved) we might have an instance from a completely different place, which will need to leave alone and create an env mod for it.
                  | (eid : currentEnvStack) `Def.isHigherOrSameLevel` instEnvStack -> []  -- NOTE: this is taken care of in `addExtraToEnv` and `EnvAdditions`

                  | otherwise -> [vlt]  -- do not touch it. might be a class function from a different scope and will need to be "completed."
                    -- let
                    --   usedVarsInThisEnv = Set.fromList $ env <&> \(v, _, t) -> (v, t)
                    --   usedVarsInInst = unpackFromEnvironment instLevel instEnvVars
                    --   usedVarsInInstDeduped = filter (\(v, _, t) -> Set.notMember (v, t) usedVarsInThisEnv) usedVarsInInst
                    -- in usedVarsInInstDeduped

                _ -> [vlt]  -- there was an error probably.
            -- 
            -- i think the only time it should be like this is when expanding environments with tvars.
            _ -> [vlt]  -- error $ pf "type of class fun is not a constructor (%: %) (union: %) - should not happen?" selfid self unT
        vlt -> pure [vlt]


getUnion :: XEnvUnion TC -> TypeFix (EnvUnionF TC (Type TC))
getUnion uid = do
  tu <- RWST.asks fst
  pure $ snd $ T.getUnionFromUni tu uid


fixVar :: T.Variable -> TypeFix T.TVariable
fixVar = \case
  T.DefinedVariable uv -> pure $ T.DefinedVariable uv
  T.DefinedFunction fn assocs snap ufi -> do
    tfn <- fixFun fn
    tassocs <- traverse fixType assocs
    tsnap <- fixSnap snap
    pure $ T.DefinedFunction tfn tassocs tsnap ufi
  T.DefinedClassFunction cfd ss t uci -> do
    tcfd <- fixClassFunDec cfd
    tss <- fixSnap ss
    tt <- fixType t
    pure $ T.DefinedClassFunction tcfd tss tt uci


fixClass :: ClassDef TC -> TypeFix (ClassDef T)
fixClass = memo memoClass (\mem s -> s { memoClass = mem }) $ \cd addMemo -> mdo
  let tcd = ClassDef cd.classID tcfds cd.classDeclarationLocation
  tcfds <- for cd.classFunctions $ \(CFD _ cfdId params ret () loc) -> do
    tparams <- traverse (bitraverse fixDecon fixClassType) params
    tret <- fixClassType ret
    pure $ CFD tcd cfdId tparams tret () loc
  pure tcd

fixClassFunDec :: ClassFunDec TC -> TypeFix (ClassFunDec T)
fixClassFunDec (CFD klass cfdId _ _ _ _) = do
  cd <- fixClass klass
  pure $ fromMaybe (error "must find class function") $
    find (\(CFD _ checkedId _ _ _ _) -> cfdId == checkedId) cd.classFunctions


fixDataDef :: DataDef TC -> TypeFix (DataDef T)
fixDataDef = memo memoDataDefinition (\mem s -> s { memoDataDefinition = mem }) $ \dd addMemo -> mdo
  let tdd = DD dd.ddName tscheme tcons dd.ddAnns
  addMemo tdd

  tscheme <- fixScheme dd.ddScheme
  let
    innerFixCon :: DataCon TC -> TypeFix (DataCon T)
    innerFixCon dc = do
      ts <- traverse fixType dc.conTypes
      pure $ DC tdd dc.conID ts dc.conAnns
  tcons <- bitraverse (traverse3 fixType) (traverse innerFixCon) dd.ddCons
  pure tdd

fixCon :: DataCon TC -> TypeFix (DataCon T)
fixCon dc = do
  dd <- fixDataDef dc.conDataDef
  pure $ fromMaybe (error "must find data con") $
    find (\ccd -> ccd.conID == dc.conID) $ fromRight (error "must be a data def with cons") $ dd.ddCons


fixFun :: Function TC -> TypeFix (Function T)
fixFun = memo memoFunction (\mem s -> s { memoFunction = mem }) $ \fn addMemo -> mdo
    let fd = fn.functionDeclaration
    let fundec = FD env fd.functionId params ret other
    let tfn = Function fundec funbody
    addMemo tfn
    env <- fixEnv fd.functionEnv
    params <- traverse (bitraverse fixDecon fixType) fd.functionParameters
    ret <- fixType fd.functionReturnType
    other <- fixFunOther fd.functionOther


    funbody <- traverse fixStmt fn.functionBody
    pure tfn

fixFunDec :: FunDec TC -> TypeFix (FunDec T)
fixFunDec fd = do
    FD
      <$> fixEnv fd.functionEnv
      <*> pure fd.functionId
      <*> traverse (bitraverse fixDecon fixType) fd.functionParameters
      <*> fixType fd.functionReturnType
      <*> fixFunOther fd.functionOther

fixInst :: InstDef TC -> TypeFix (InstDef T)
fixInst = memo memoInstance (\mem s -> s { memoInstance = mem }) $ \instdef _ -> mdo
    klass <- fixClass instdef.instClass
    itype <- bitraverse fixDataDef (traverse fixTVar) instdef.instType

    let tinstDef = InstDef
          { instClass = klass
          , instType = itype
          , instFuns = ifuns
          , instConstraints = ()
          }
    let
      fixInstFun :: InstFun TC -> TypeFix (InstFun T)
      fixInstFun ifn = InstFun
        <$> fixFunDec ifn.instFunDec
        <*> traverse fixStmt ifn.instFunBody
        <*> fixClassFunDec ifn.instClassFunDec
        <*> pure tinstDef
  
    ifuns <- traverse fixInstFun instdef.instFuns
    pure tinstDef



fixFunOther :: FunOther TC -> TypeFix (FunOther T)
fixFunOther fo = FunOther
  <$> fixScheme fo.functionScheme
  <*> traverse fixFunAssoc fo.functionAssociations
  <*> pure fo.functionAnnotations
  <*> pure fo.functionLocation

fixFunAssoc :: FunctionTypeAssociation TC -> TypeFix (FunctionTypeAssociation T)
fixFunAssoc (FunctionTypeAssociation tv t cfd uci) = FunctionTypeAssociation
  <$> fixTVar tv
  <*> fixType t
  <*> fixClassFunDec cfd
  <*> pure uci

fixScheme :: Scheme TC -> TypeFix (Scheme T)
fixScheme (Scheme tvs unions) = Scheme
  <$> traverse fixTVar tvs
  <*> traverse (\(union, ts, t) -> liftA3 (,,) (fixUnion union) (traverse fixType ts) (fixType t)) unions

-- for this i guess i would just index by IDs!
fixSnap :: ScopeSnapshot TC -> TypeFix (ScopeSnapshot T)
fixSnap = Def.bitraverseMap fixClass $ Def.bitraverseMap fixDataDef fixInst



fixMutAccess :: XMutAccess TC -> TypeFix (XMutAccess T)
fixMutAccess = traverse fixType . first fixMA where
  fixMA :: MutAccess TC -> MutAccess T
  fixMA = \case
    MutRef loc  -> MutRef loc
    MutField loc mem -> MutField loc mem



type TypeFix a = RWST (T.TypeUni, T.EnvAdditions) () MemoShit PrintContext a

data MemoShit = MemoShit
  { memoFunction :: Memo (Function TC) (Function T)
  , memoDataDefinition :: Memo (DataDef TC) (DataDef T)
  , memoClass :: Memo (ClassDef TC) (ClassDef T)
  , memoInstance :: Memo (InstDef TC) (InstDef T)
  , memoType :: Memo (Type TC) (Type T)
  , memoUnion :: Memo (XEnvUnion TC) (XEnvUnion T)

  -- stats
  , typeNodesVisited :: Counter
  , unionsVisited :: Counter
  }

emptyMemoShit :: MemoShit
emptyMemoShit = MemoShit
  { memoFunction = emptyMemo
  , memoDataDefinition = emptyMemo
  , memoClass = emptyMemo
  , memoInstance = emptyMemo
  , memoType = emptyMemo
  , memoUnion = emptyMemo

  , typeNodesVisited = 0
  , unionsVisited = 0
  }

thisAnd :: Monad m => m () -> a -> m a
thisAnd f x = do
  f
  pure x
