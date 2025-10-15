{-# LANGUAGE LambdaCase #-}

module Core.Gen.Pretty
  ( PrettyError(..)
  , prettyGenerated
  ) where

import Core.Show (showTerm)
import Core.Type

import Control.Monad (foldM)
import Control.Monad.State.Strict (State, execState, get, modify)
import qualified Data.List as L
import Data.List (stripPrefix)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- | Errors that may arise when prettifying a generated term.
data PrettyError
  = PrettyError String
  deriving (Eq, Show)

prettyErr :: String -> Either PrettyError a
prettyErr = Left . PrettyError

-- | Queue entries track Bend variables that still need to be consumed.
data QueueEntry = QueueEntry
  { qeName :: String
  , qeType :: Type
  }

-- | Environment carried while walking the raw term.
data Env = Env
  { envQueue    :: [QueueEntry]
  , envBindings :: M.Map String String
  , envUsed     :: S.Set String
  }

-- | State accumulated while emitting pretty-printed lines.
data PrettyState = PrettyState
  { psIndent :: !Int
  , psLines  :: [String]
  }

newtype PrettyM a = PrettyM { runPrettyM :: State PrettyState a }
  deriving (Functor, Applicative, Monad)

runPretty :: PrettyM () -> String
runPretty action =
  let finalState = execState (runPrettyM action) (PrettyState 0 [])
  in unlines . reverse $ psLines finalState

emitLine :: String -> PrettyM ()
emitLine txt = PrettyM $ do
  st <- get
  let line = replicate (psIndent st * 2) ' ' ++ txt
  modify $ \s -> s { psLines = line : psLines s }

withIndent :: PrettyM a -> PrettyM a
withIndent (PrettyM action) = PrettyM $ do
  modify (\st -> st { psIndent = psIndent st + 1 })
  result <- action
  modify (\st -> st { psIndent = psIndent st - 1 })
  pure result

-- | Entry point used by CLI generation pipeline.
prettyGenerated
  :: String   -- ^ simple function name
  -> Type     -- ^ declared generator type
  -> [Term]   -- ^ helper context terms
  -> Term     -- ^ raw λ-term produced by the miner
  -> Either PrettyError String
prettyGenerated funName funType ctxTerms rawTerm = do
  SigPieces tyParams valParams retType <- extractSignature funType
  let helperNames = map renderHelper ctxTerms
      initialQueue = map (uncurry QueueEntry) valParams
      initialUsed =
        S.fromList $
          funName : map fst valParams ++ tyParams ++ helperNames
      env0 = Env initialQueue M.empty initialUsed
  (bodyTerm, env1) <- stripInitialLambdas helperNames funName rawTerm env0
  bodyWriter <- emitBody env1 bodyTerm
  let header = renderHeader funName tyParams valParams retType
      doc = runPretty $ do
        emitLine header
        withIndent bodyWriter
  pure (ensureTrailingNewline doc)

ensureTrailingNewline :: String -> String
ensureTrailingNewline txt
  | null txt        = "\n"
  | last txt == '\n' = txt
  | otherwise        = txt ++ "\n"

-- | Signature pieces extracted from the generator type.
data SignaturePieces = SigPieces [String] [(String, Type)] Type

extractSignature :: Type -> Either PrettyError SignaturePieces
extractSignature typ = do
  let (args, ret) = collectArgs typ
      partitioned = span (\(_, t) -> isSetType t) args
      (tyParams, valParams) = partitioned
  pure $ SigPieces (map fst tyParams) valParams ret
  where
    isSetType t = case cut t of
      Set -> True
      _   -> False

renderHelper :: Term -> String
renderHelper = showTerm False

stripInitialLambdas
  :: [String]  -- ^ helper display names, in order
  -> String    -- ^ recursive function display name
  -> Term
  -> Env
  -> Either PrettyError (Term, Env)
stripInitialLambdas helperDisplays recName term env =
  let expected = helperDisplays ++ [recName]
  in foldM step (term, env) expected
  where
    step (currentTerm, curEnv) targetName =
      case cut currentTerm of
        Lam binder _ lamBody ->
          let mappedEnv =
                curEnv
                  { envBindings = M.insert binder targetName (envBindings curEnv)
                  , envUsed     = S.insert targetName (envUsed curEnv)
                  }
              nextTerm = lamBody (Var binder 0)
          in pure (nextTerm, mappedEnv)
        other -> prettyErr $
          "Expected λ-binder for helper `" ++ targetName ++ "` but found: " ++ show other

renderHeader :: String -> [String] -> [(String, Type)] -> Type -> String
renderHeader name tyParams valParams retType =
  "def "
  ++ name
  ++ renderGenerics tyParams
  ++ "("
  ++ renderParams valParams
  ++ ") -> "
  ++ showTerm False retType
  ++ ":"
  where
    renderGenerics [] = ""
    renderGenerics params = "<" ++ L.intercalate ", " params ++ ">"
    renderParams = L.intercalate ", " . map renderParam
    renderParam (paramName, paramType) =
      paramName ++ ": " ++ showTerm False paramType

emitBody :: Env -> Term -> Either PrettyError (PrettyM ())
emitBody env term = case cut term of
  Lam binder _ lamBody -> do
    (_, env') <- bindNext binder env
    emitBody env' (lamBody (Var binder 0))
  NatM zeroBranch succBranch -> emitNat env zeroBranch succBranch
  LstM nilBranch consBranch  -> emitList env nilBranch consBranch
  BitM falseBranch trueBranch -> emitBool env falseBranch trueBranch
  SigM _          -> prettyErr "Pair matches are not supported in generated code yet"
  other -> emitReturn env other

emitNat :: Env -> Term -> Term -> Either PrettyError (PrettyM ())
emitNat env zeroBranch succBranch = do
  (scrut, envAfterPop) <- popQueue env
  zeroDoc <- emitCase envAfterPop "0n" zeroBranch
  (predName, envSucc) <- pushNatBinder scrut envAfterPop
  let succPattern = "1n+" ++ predName
  succDoc <- emitCase envSucc succPattern succBranch
  pure $ do
    emitLine ("match " ++ qeName scrut ++ ":")
    withIndent $ do
      zeroDoc
      succDoc

emitList :: Env -> Term -> Term -> Either PrettyError (PrettyM ())
emitList env nilBranch consBranch = do
  (scrut, envAfterPop) <- popQueue env
  nilDoc <- emitCase envAfterPop "[]" nilBranch
  ((headName, tailName), envCons) <- pushListBinders scrut envAfterPop
  let patternTxt = headName ++ " <> " ++ tailName
  consDoc <- emitCase envCons patternTxt consBranch
  pure $ do
    emitLine ("match " ++ qeName scrut ++ ":")
    withIndent $ do
      nilDoc
      consDoc

emitBool :: Env -> Term -> Term -> Either PrettyError (PrettyM ())
emitBool env falseBranch trueBranch = do
  (scrut, envAfterPop) <- popQueue env
  falseDoc <- emitCase envAfterPop "False" falseBranch
  trueDoc  <- emitCase envAfterPop "True" trueBranch
  pure $ do
    emitLine ("match " ++ qeName scrut ++ ":")
    withIndent $ do
      falseDoc
      trueDoc

emitCase :: Env -> String -> Term -> Either PrettyError (PrettyM ())
emitCase env patternTxt branchTerm = do
  branchDoc <- emitBody env branchTerm
  pure $ do
    emitLine ("case " ++ patternTxt ++ ":")
    withIndent branchDoc

emitReturn :: Env -> Term -> Either PrettyError (PrettyM ())
emitReturn env term = do
  exprTxt <- renderExpr env term
  pure $ emitLine ("return " ++ exprTxt)

bindNext :: String -> Env -> Either PrettyError (QueueEntry, Env)
bindNext binder env = case envQueue env of
  [] -> prettyErr ("Queue exhausted while binding `" ++ binder ++ "`")
  (entry:rest) ->
    let env' = env
          { envQueue = rest
          , envBindings = M.insert binder (qeName entry) (envBindings env)
          }
    in pure (entry, env')

popQueue :: Env -> Either PrettyError (QueueEntry, Env)
popQueue env = case envQueue env of
  [] -> prettyErr "Attempted to match but the parameter queue is empty"
  (entry:rest) ->
    let env' = env { envQueue = rest }
    in pure (entry, env')

pushNatBinder :: QueueEntry -> Env -> Either PrettyError (String, Env)
pushNatBinder scrut env = case cut (qeType scrut) of
  Nat -> do
    (predName, env1) <- freshName "p" env
    let predEntry = QueueEntry predName Nat
    pure (predName, env1 { envQueue = predEntry : envQueue env1 })
  other ->
    prettyErr $
      "Expected Nat type when introducing predecessor binder, found: "
      ++ showTerm False other

pushListBinders :: QueueEntry -> Env -> Either PrettyError ((String, String), Env)
pushListBinders scrut env =
  case cut (qeType scrut) of
    Lst elemType -> do
      (headName, env1) <- freshName "h" env
      (tailName, env2) <- freshName "t" env1
      let headEntry = QueueEntry headName elemType
          tailEntry = QueueEntry tailName (qeType scrut)
          envFinal = env2 { envQueue = headEntry : tailEntry : envQueue env2 }
      pure ((headName, tailName), envFinal)
    other ->
      prettyErr $
        "Expected list type when introducing head/tail binders, found: "
        ++ showTerm False other

freshName :: String -> Env -> Either PrettyError (String, Env)
freshName base env =
  let candidates = base : [base ++ show n | n <- [(1 :: Int)..]]
      chosen = L.find (`S.notMember` envUsed env) candidates
  in case chosen of
      Nothing -> prettyErr "Unable to generate a fresh binder name"
      Just name ->
        let env' = env { envUsed = S.insert name (envUsed env) }
        in pure (name, env')

renderExpr :: Env -> Term -> Either PrettyError String
renderExpr env term =
  let renamed = renameVars (envBindings env) term
  in pure (formatExpr (showTerm False renamed))

formatExpr :: String -> String
formatExpr = addCommaSpacing . replaceAngles
  where
    addCommaSpacing [] = []
    addCommaSpacing (',' : ' ' : rest) = ',' : ' ' : addCommaSpacing rest
    addCommaSpacing (',' : rest) = ',' : ' ' : addCommaSpacing rest
    addCommaSpacing (c : rest) = c : addCommaSpacing rest

    replaceAngles = replaceSub "<>" " <> "

replaceSub :: String -> String -> String -> String
replaceSub needle replacement haystack =
  case stripPrefix needle haystack of
    Just rest -> replacement ++ replaceSub needle replacement rest
    Nothing -> case haystack of
      [] -> []
      (c:cs) -> c : replaceSub needle replacement cs

renameVars :: M.Map String String -> Term -> Term
renameVars mapping = go
  where
    go tm = case tm of
      Var k i      -> Var (M.findWithDefault k k mapping) i
      Ref{}        -> tm
      Sub t        -> Sub (go t)
      Fix k f      -> Fix k (\v -> go (f v))
      Let k mt v f -> Let k (fmap go mt) (go v) (\v' -> go (f v'))
      Use k v f    -> Use k (go v) (\v' -> go (f v'))
      Chk x t      -> Chk (go x) (go t)
      Tst x        -> Tst (go x)
      Set          -> Set
      Emp          -> Emp
      EmpM         -> EmpM
      Uni          -> Uni
      One          -> One
      UniM f       -> UniM (go f)
      Bit          -> Bit
      Bt0          -> Bt0
      Bt1          -> Bt1
      BitM f t     -> BitM (go f) (go t)
      Nat          -> Nat
      Zer          -> Zer
      Suc n        -> Suc (go n)
      NatM z s     -> NatM (go z) (go s)
      Lst t        -> Lst (go t)
      Nil          -> Nil
      Con h t      -> Con (go h) (go t)
      LstM n c     -> LstM (go n) (go c)
      Enu xs       -> Enu xs
      Sym s        -> Sym s
      EnuM cs d    -> EnuM (map (\(s,t) -> (s, go t)) cs) (go d)
      Sig a b      -> Sig (go a) (go b)
      Tup a b      -> Tup (go a) (go b)
      SigM f       -> SigM (go f)
      All a b      -> All (go a) (go b)
      Lam k mt f   -> Lam k (fmap go mt) (\v -> go (f v))
      App f x      -> App (go f) (go x)
      Eql t a b    -> Eql (go t) (go a) (go b)
      Rfl          -> Rfl
      EqlM f       -> EqlM (go f)
      Rwt e f      -> Rwt (go e) (go f)
      Met n t ctx  -> Met n (go t) (map go ctx)
      Era          -> Era
      Sup l a b    -> Sup (go l) (go a) (go b)
      SupM l f     -> SupM (go l) (go f)
      Loc sp t     -> Loc sp (go t)
      Log s x      -> Log (go s) (go x)
      Pri p        -> Pri p
      Num n        -> Num n
      Val v        -> Val v
      Op2 o a b    -> Op2 o (go a) (go b)
      Op1 o a      -> Op1 o (go a)
      Pat ts ms cs -> Pat (map go ts)
                            (map (\(k,x) -> (k, go x)) ms)
                            (map (\(ps,t) -> (map go ps, go t)) cs)
      Frk l a b    -> Frk (go l) (go a) (go b)
      IO t         -> IO (go t)
