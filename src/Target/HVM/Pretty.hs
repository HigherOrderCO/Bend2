module Target.HVM.Pretty
  ( PrettyError(..)
  , prettyGenerated
  ) where

import Core.Show (showTerm)
import Core.Type
import Target.HVM.HVM (HCore(..))

import Control.Monad.State.Strict (State, execState, get, modify)
import Data.Char (toLower)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-------------------------------------------------------------------------------
-- Pretty-print state
-------------------------------------------------------------------------------

data PrettyError
  = PrettyError String
  deriving (Eq, Show)

prettyErr :: String -> Either PrettyError a
prettyErr = Left . PrettyError

newtype PrettyM a = PrettyM { runPrettyM :: State PrettyState a }
  deriving (Functor, Applicative, Monad)

data PrettyState = PrettyState
  { psIndent :: !Int
  , psLines  :: [String]
  }

data QueueEntry = QueueEntry
  { qeName :: String
  , qeType :: Type
  }

data Env = Env
  { envQueue    :: [QueueEntry]
  , envBindings :: M.Map String String
  , envUsed     :: S.Set String
  }

runPretty :: PrettyM () -> String
runPretty action =
  let finalState = execState (runPrettyM action) (PrettyState 0 [])
  in unlines . reverse $ psLines finalState

emitLine :: String -> PrettyM ()
emitLine txt = PrettyM $ do
  st <- get
  let indent = replicate (psIndent st * 2) ' '
      line   = if null txt then "" else indent ++ txt
  modify $ \s -> s { psLines = line : psLines s }

emitBlank :: PrettyM ()
emitBlank = emitLine ""

incIndent :: PrettyM ()
incIndent = PrettyM $ modify (\st -> st { psIndent = psIndent st + 1 })

decIndent :: PrettyM ()
decIndent = PrettyM $ modify (\st -> st { psIndent = max 0 (psIndent st - 1) })

-------------------------------------------------------------------------------
-- Public entry point
-------------------------------------------------------------------------------

prettyGenerated :: String -> Type -> [Term] -> HCore -> Either PrettyError String
prettyGenerated simpleName funType ctxTerms rawTerm = do
  SignaturePieces tyParams valParams retType <- extractSignature funType

  let helperNames = map showHelper ctxTerms
      initialQueue = map (uncurry QueueEntry) valParams
      usedSeed = S.fromList (simpleName : helperNames ++ map fst valParams)
      env0 = Env initialQueue M.empty usedSeed

  (stripped, env1) <- stripInitialLambdas helperNames simpleName rawTerm env0
  bodyWriter <- emitBody env1 stripped

  let doc = runPretty $ do
        emitDef simpleName tyParams valParams retType
        incIndent
        bodyWriter
        decIndent
        emitBlank
  pure (ensureTrailingNewline doc)

showHelper :: Term -> String
showHelper = showTerm False

data SignaturePieces = SignaturePieces
  [String]
  [(String, Type)]
  Type

extractSignature :: Type -> Either PrettyError SignaturePieces
extractSignature typ = do
  let (args, ret) = collectTypeArgs typ
      (typeParams, valueParams) = span (\(_, t) -> case cut t of
        Set -> True
        _   -> False) args
  pure $ SignaturePieces (map fst typeParams) valueParams ret

collectTypeArgs :: Type -> ([(String, Type)], Type)
collectTypeArgs = go []
  where
    go acc (All a (Lam k _ body)) = go (acc ++ [(k, a)]) (body (Var k 0))
    go acc other                  = (acc, other)

-------------------------------------------------------------------------------
-- Lambda handling
-------------------------------------------------------------------------------

stripInitialLambdas :: [String] -> String -> HCore -> Env -> Either PrettyError (HCore, Env)
stripInitialLambdas helpers selfName term env = do
  (afterHelpers, env1) <- foldlM stripOne (term, env) helpers
  stripSelf afterHelpers env1
  where
    stripOne (HLam binder body, e) target =
      let e' = addBinding binder target e
      in pure (body, e')
    stripOne _ target = prettyErr $ "Expected λ for helper " ++ target

    stripSelf (HLam binder body) e =
      let e' = addBinding binder selfName e
      in pure (body, e')
    stripSelf _ _ = prettyErr "Expected λ for recursive binder"

addBinding :: String -> String -> Env -> Env
addBinding binder target env =
  env
    { envBindings = M.insert binder target (envBindings env)
    , envUsed     = S.insert target (envUsed env)
    }

-------------------------------------------------------------------------------
-- Emit body
-------------------------------------------------------------------------------

emitBody :: Env -> HCore -> Either PrettyError (PrettyM ())
emitBody env term = case term of
  HLam binder body -> do
    (_, env') <- bindNext binder env
    emitBody env' body
  HNif zeroBranch succBranch -> emitNat env zeroBranch succBranch
  HMat nilBranch consBranch  -> emitList env nilBranch consBranch
  HBif falseBranch trueBranch -> emitBool env falseBranch trueBranch
  HGet pairBranch -> emitPair env pairBranch
  HUse unitBranch -> emitUnit env unitBranch
  HErf            -> prettyErr "Empty match not supported"
  other           -> emitReturn env other

emitNat :: Env -> HCore -> HCore -> Either PrettyError (PrettyM ())
emitNat env zeroBranch succBranch = do
  (scrutinee, envAfterPop) <- popQueue env
  zeroWriter <- emitBody envAfterPop zeroBranch
  let scrutType = qeType scrutinee
  (predName, envSucc) <- pushFresh "p" scrutType envAfterPop
  succWriter <- emitBody envSucc succBranch
  pure $ emitMatch (qeName scrutinee) $ do
    emitCase "0n" zeroWriter
    emitCase ("1n+" ++ predName) succWriter

emitList :: Env -> HCore -> HCore -> Either PrettyError (PrettyM ())
emitList env nilBranch consBranch = do
  (scrutinee, envAfterPop) <- popQueue env
  nilWriter <- emitBody envAfterPop nilBranch
  let (headType, tailType) = listComponentTypes (qeType scrutinee)
  (tailName, env1) <- pushFresh "t" tailType envAfterPop
  (headName, env2) <- pushFresh "h" headType env1
  consWriter <- emitBody env2 consBranch
  pure $ emitMatch (qeName scrutinee) $ do
    emitCase "[]" nilWriter
    emitCase (headName ++ " <> " ++ tailName) consWriter

emitBool :: Env -> HCore -> HCore -> Either PrettyError (PrettyM ())
emitBool env falseBranch trueBranch = do
  (scrutinee, envAfterPop) <- popQueue env
  falseWriter <- emitBody envAfterPop falseBranch
  trueWriter  <- emitBody envAfterPop trueBranch
  pure $ emitMatch (qeName scrutinee) $ do
    emitCase "False" falseWriter
    emitCase "True"  trueWriter

emitPair :: Env -> HCore -> Either PrettyError (PrettyM ())
emitPair env pairBranch = do
  (scrutinee, envAfterPop) <- popQueue env
  let (firstType, secondType) = pairComponentTypes (qeType scrutinee)
  (secondName, env1) <- pushFresh "b" secondType envAfterPop
  (firstName, env2) <- pushFresh "a" firstType env1
  pairWriter <- emitBody env2 pairBranch
  pure $ emitMatch (qeName scrutinee) $ do
    emitCase ("(" ++ firstName ++ ", " ++ secondName ++ ")") pairWriter

emitUnit :: Env -> HCore -> Either PrettyError (PrettyM ())
emitUnit env unitBranch = do
  (scrutinee, envAfterPop) <- popQueue env
  unitWriter <- emitBody envAfterPop unitBranch
  pure $ emitMatch (qeName scrutinee) (emitCase "()" unitWriter)

emitReturn :: Env -> HCore -> Either PrettyError (PrettyM ())
emitReturn env term = do
  expr <- renderExpr env term
  pure (emitLine ("return " ++ expr))

-------------------------------------------------------------------------------
-- Environment helpers
-------------------------------------------------------------------------------

bindNext :: String -> Env -> Either PrettyError (QueueEntry, Env)
bindNext binder env =
  case envQueue env of
    [] -> prettyErr $ "Queue exhausted while binding " ++ binder
    entry:rest ->
      let target = qeName entry
          env' = env
            { envQueue    = rest
            , envBindings = M.insert binder target (envBindings env)
            , envUsed     = S.insert target (envUsed env)
            }
      in pure (entry, env')

popQueue :: Env -> Either PrettyError (QueueEntry, Env)
popQueue env =
  case envQueue env of
    [] -> prettyErr "Attempted to match but queue is empty"
    entry:rest -> pure (entry, env { envQueue = rest })

pushFresh :: String -> Type -> Env -> Either PrettyError (String, Env)
pushFresh base typ env = do
  name <- freshName base (envUsed env)
  let entry = QueueEntry name typ
      env'  = env
        { envQueue = entry : envQueue env
        , envUsed  = S.insert name (envUsed env)
        }
  pure (name, env')

freshName :: String -> S.Set String -> Either PrettyError String
freshName base used =
  let candidates = base : [base ++ show n | n <- [1 :: Int ..]]
  in case filter (`S.notMember` used) candidates of
       []     -> prettyErr "Unable to allocate fresh name"
       (x:_) -> pure x

listComponentTypes :: Type -> (Type, Type)
listComponentTypes typ = case cut typ of
  Lst elemType -> (elemType, Lst elemType)
  _            -> (Set, Set)

pairComponentTypes :: Type -> (Type, Type)
pairComponentTypes typ = case cut typ of
  Sig a b -> (a, b)
  _       -> (Set, Set)

-------------------------------------------------------------------------------
-- Emit helpers
-------------------------------------------------------------------------------

emitDef :: String -> [String] -> [(String, Type)] -> Type -> PrettyM ()
emitDef name tyParams valParams retType =
  emitLine $
    "def " ++ name
      ++ renderGenerics tyParams
      ++ "(" ++ L.intercalate ", " (map renderParam valParams) ++ ")"
      ++ " -> " ++ showTerm False retType ++ ":"
  where
    renderGenerics [] = ""
    renderGenerics params = "<" ++ L.intercalate ", " params ++ ">"

    renderParam (paramName, paramType) =
      paramName ++ ": " ++ showTerm False paramType

emitMatch :: String -> PrettyM () -> PrettyM ()
emitMatch scrutinee body = do
  emitLine ("match " ++ scrutinee ++ ":")
  incIndent
  body
  decIndent

emitCase :: String -> PrettyM () -> PrettyM ()
emitCase pat body = do
  emitLine ("case " ++ pat ++ ":")
  incIndent
  body
  decIndent

-------------------------------------------------------------------------------
-- Expression rendering
-------------------------------------------------------------------------------

renderExpr :: Env -> HCore -> Either PrettyError String
renderExpr env = pure . render
  where
    rename name = M.findWithDefault name name (envBindings env)

    render term = case term of
      HVar n       -> rename n
      HRef nick    -> map toLower nick
      HTup a b     -> "(" ++ render a ++ ", " ++ render b ++ ")"
      HNull        -> "()"
      HNil         -> "[]"
      HBt0         -> "False"
      HBt1         -> "True"
      HZer         -> "0n"
      HSuc _ ->
        let (count, base) = collectSucc term
        in case base of
             HZer -> show count ++ "n"
             _    -> show count ++ "n+" ++ render base
      HCon h t     -> render h ++ " <> " ++ render t
      HApp f x     -> renderApp f [x]
      HEql t a b   -> render t ++ "{" ++ render a ++ "==" ++ render b ++ "}"
      HRwt e p b   -> "rewrite " ++ render e ++ " " ++ render p ++ " " ++ render b
      HInc t       -> "inc(" ++ render t ++ ")"
      HUva n       -> show n
      HSpn n body  -> "&" ++ map toLower n ++ "(" ++ render body ++ ")"
      HGen nick ctx typ seed ->
        "?" ++ map toLower nick ++ " " ++ render ctx ++ " : " ++ render typ ++ renderSeed seed
      other        -> show other

    renderApp f args =
      let (fn, rest) = flattenApp f args
          renderedArgs = L.intercalate ", " (map render rest)
      in case fn of
           HVar n -> rename n ++ "(" ++ renderedArgs ++ ")"
           HRef nick -> map toLower nick ++ "(" ++ renderedArgs ++ ")"
           _ -> render fn ++ "(" ++ renderedArgs ++ ")"

    flattenApp fun acc = case fun of
      HApp f x -> flattenApp f (x:acc)
      _        -> (fun, acc)

    renderSeed seed = case seed of
      HUva 0 -> ""
      HUva n -> " #" ++ show n
      other  -> " #" ++ render other

    collectSucc :: HCore -> (Int, HCore)
    collectSucc = go 0
      where
        go acc (HSuc inner) = go (acc + 1) inner
        go acc other        = (acc, other)

-------------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------------

ensureTrailingNewline :: String -> String
ensureTrailingNewline txt
  | null txt = "\n"
  | last txt == '\n' = txt
  | otherwise = txt ++ "\n"

foldlM :: (Monad m) => (a -> b -> m a) -> a -> [b] -> m a
foldlM _ acc [] = return acc
foldlM f acc (x:xs) = f acc x >>= \acc' -> foldlM f acc' xs
