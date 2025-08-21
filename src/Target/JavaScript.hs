{-./../Core/Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Target.JavaScript where

import Control.Monad (forM)
import Core.Type
import Data.Int (Int64)
import Data.List (intercalate, isPrefixOf, isSuffixOf, isInfixOf)
import Data.Maybe (fromJust)
import Data.Word (Word64)
import Debug.Trace
import qualified Control.Monad.State as ST
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.ByteString.Lazy.Char8 as BL

-- Compilable Term (only runtime-relevant constructs)
data CT
  = CVar String Int
  | CRef String
  | CLam String (CT -> CT)
  | CApp CT CT
  | CLet CT (CT -> CT) 
  | CFix String (CT -> CT)
  -- Data constructors
  | CZer
  | CSuc CT
  | CNil
  | CCon CT CT
  | COne
  | CBt0
  | CBt1
  | CSym String
  | CTup CT CT
  -- Pattern matching lambdas
  | CSwi CT CT
  | CBif CT CT
  | CMat CT CT
  | CCse [(String, CT)] CT
  | CGet CT
  | CUse CT
  | CEql CT
  -- Numeric
  | CVal NVal
  | COp2 NOp2 CT CT
  | COp1 NOp1 CT
  -- Others
  | CEra
  | CSup CT CT CT
  | CSupM CT CT CT
  | CFrk CT CT CT
  | CPri PriF

type CTBook = M.Map String CT

-- Convert CT back to Term for substitution
ctToTerm :: CT -> Term
ctToTerm (CVar k i) = Var k i
ctToTerm _ = error "ctToTerm: only variables can be converted back"

-- Convert Term to CT (erase types, keep runtime values)
termToCT :: Book -> Term -> Int -> CT
termToCT book term dep = case term of
  Var k i      -> CVar k i
  Ref k i      -> CRef k
  Sub t        -> termToCT book t dep
  Fix k f      -> CFix k (\x -> termToCT book (f (ctToTerm x)) (dep+1))
  Let k t v f  -> CLet (termToCT book v dep) (\x -> termToCT book (f (ctToTerm x)) (dep+1))
  Use k v f    -> termToCT book (f v) dep  -- Inline directly, no binding
  Set          -> CEra
  Chk x _      -> termToCT book x dep
  Tst x        -> termToCT book x dep
  Emp          -> CEra
  EmpM         -> CLam "x$" (\_ -> CEra)
  Uni          -> CEra
  Bit          -> CEra
  Nat          -> CEra
  Lst _        -> CEra
  Enu _        -> CEra
  Num _        -> CEra
  Sig _ _      -> CEra
  All _ _      -> CEra
  Eql _ _ _    -> CEra
  Met _ _ _    -> CEra
  Loc _ t      -> termToCT book t dep
  One          -> COne
  Zer          -> CZer
  Suc n        -> CSuc (termToCT book n dep)
  Nil          -> CNil
  Con h t      -> CCon (termToCT book h dep) (termToCT book t dep)
  Bt0          -> CBt0
  Bt1          -> CBt1
  Sym s        -> CSym s
  Tup a b      -> CTup (termToCT book a dep) (termToCT book b dep)
  Val v        -> CVal v
  Lam k _ f    -> CLam k (\x -> termToCT book (f (ctToTerm x)) (dep+1))
  App f x      -> CApp (termToCT book f dep) (termToCT book x dep)
  UniM f       -> CLam "x$" (\x -> CApp (CUse (termToCT book f dep)) x)
  BitM f t     -> CLam "x$" (\x -> CApp (CBif (termToCT book f dep) (termToCT book t dep)) x)
  NatM z s     -> CLam "x$" (\x -> CApp (CSwi (termToCT book z dep) (termToCT book s dep)) x)
  LstM n c     -> CLam "x$" (\x -> CApp (CMat (termToCT book n dep) (termToCT book c dep)) x)
  EnuM c d     -> CLam "x$" (\x -> CApp (CCse (map (\(s,t) -> (s, termToCT book t dep)) c) (termToCT book d dep)) x)
  SigM f       -> CLam "x$" (\x -> CApp (CGet (termToCT book f dep)) x)
  Op2 o a b    -> COp2 o (termToCT book a dep) (termToCT book b dep)
  Op1 o a      -> COp1 o (termToCT book a dep)
  Log s x      -> termToCT book x dep  -- For JavaScript, just return the result expression
  Pri p        -> CPri p
  Rfl          -> CEra
  EqlM _       -> CEra
  Era          -> CEra
  Sup l a b    -> CSup (termToCT book l dep) (termToCT book a dep) (termToCT book b dep)
  SupM l f     -> CSupM CEra (termToCT book l dep) (termToCT book f dep)
  Frk l a b    -> CFrk (termToCT book l dep) (termToCT book a dep) (termToCT book b dep)
  Rwt _ _      -> CEra  -- Erases at runtime
  Pat _ _ _  -> error "unreachable"

-- JavaScript State Monad
type JSM = ST.State Int

-- Fresh name generation
fresh :: JSM String
fresh = do
  n <- ST.get
  ST.put (n + 1)
  return $ "$x" ++ show n

-- Name conversion
nameToJS :: String -> String
nameToJS x = "$" ++ map (\c -> if c == '/' || c == '.' || c == '-' || c == '#' then '$' else c) x

-- Statement generation
set :: String -> String -> JSM String
set name expr = return $ "var " ++ name ++ " = " ++ expr ++ ";"

-- Operator conversion
operToJS :: NOp2 -> String
operToJS ADD = "+"
operToJS SUB = "-"
operToJS MUL = "*"
operToJS DIV = "/"
operToJS MOD = "%"
operToJS POW = "**"
operToJS EQL = "==="
operToJS NEQ = "!=="
operToJS LST = "<"
operToJS GRT = ">"
operToJS LEQ = "<="
operToJS GEQ = ">="
operToJS AND = "&"
operToJS OR  = "|"
operToJS XOR = "^"
operToJS SHL = "<<"
operToJS SHR = ">>"

-- Get function arguments
getArguments :: CT -> ([String], CT)
getArguments = go 0 where
  go dep (CLam nam bod) =
    let (args, body) = go (dep+1) (bod (CVar nam dep))
    in (nam:args, body)
  go _ body = ([], body)

-- Get application chain
getAppChain :: CT -> (CT, [CT])
getAppChain = go [] where
  go acc (CApp fun arg) = go (arg:acc) fun
  go acc term = (term, acc)

-- Get arity of a function
arityOf :: CTBook -> String -> Int
arityOf book name = case M.lookup name book of
  Just ct -> length $ fst $ getArguments ct
  Nothing -> 0

-- Check if it's a recursive call
isRecCall :: String -> Int -> CT -> [CT] -> Bool
isRecCall fnName arity (CRef appFunName) appArgs = 
  appFunName == fnName && length appArgs == arity
isRecCall _ _ _ _ = False

-- Check if it's a saturated call
isSatCall :: CTBook -> CT -> [CT] -> Bool
isSatCall book (CRef funName) appArgs = arityOf book funName == length appArgs
isSatCall _ _ _ = False

-- Main function compilation
fnToJS :: CTBook -> String -> CT -> JSM String
fnToJS book fnName ct = do
  let (fnArgs, fnBody) = getArguments ct
  bodyName <- fresh
  bodyStmt <- ctToJS book fnName fnArgs True bodyName fnBody 0  
  let tco = isInfixOf "/*TCO*/" bodyStmt
  let bod = "{" ++ bodyStmt ++ "return " ++ bodyName ++ "; }"
  let fun = jsDefFun fnName fnArgs tco bod
  let cur = jsDefCur fnName fnArgs
  return $ fun ++ "\n" ++ cur

-- Generate function definition
jsDefFun :: String -> [String] -> Bool -> String -> String
jsDefFun name [] _ body = 
  "const " ++ nameToJS name ++ "$ = (() => " ++ body ++ ")()"
jsDefFun name args True body =
  "function " ++ nameToJS name ++ "$(" ++ intercalate "," args ++ ") {while(1)" ++ body ++ "}"
jsDefFun name args False body =
  "function " ++ nameToJS name ++ "$(" ++ intercalate "," args ++ ") " ++ body

-- Generate curried version
jsDefCur :: String -> [String] -> String
jsDefCur name args =
  let head = "const " ++ nameToJS name ++ " = " ++ concat (map (\x -> x ++ " => ") args)
      body = nameToJS name ++ "$" ++ (if null args then "" else "(" ++ intercalate "," args ++ ")")
  in head ++ body

-- Compile data constructor
compileConstructor :: String -> CT -> Int -> JSM String
compileConstructor var CZer _ = set var "{$:\"Zer\"}"
compileConstructor var (CSuc n) dep = do
  nName <- fresh
  nStmt <- ctToJS' False nName n dep
  setStmt <- set var $ "{$:\"Suc\", pred:" ++ nName ++ "}"
  return $ nStmt ++ setStmt
compileConstructor var CBt0 _ = set var "false"
compileConstructor var CBt1 _ = set var "true"
compileConstructor var COne _ = set var "null"
compileConstructor var CNil _ = set var "{$:\"Nil\"}"
compileConstructor var (CCon h t) dep = do
  hName <- fresh
  hStmt <- ctToJS' False hName h dep
  tName <- fresh
  tStmt <- ctToJS' False tName t dep
  setStmt <- set var $ "{$:\"Con\", head:" ++ hName ++ ", tail:" ++ tName ++ "}"
  return $ concat [hStmt, tStmt, setStmt]
compileConstructor var (CSym s) _ = set var $ "\"" ++ s ++ "\""
compileConstructor var (CTup a b) dep = do
  aName <- fresh
  aStmt <- ctToJS' False aName a dep
  bName <- fresh
  bStmt <- ctToJS' False bName b dep
  setStmt <- set var $ "[" ++ aName ++ ", " ++ bName ++ "]"
  return $ concat [aStmt, bStmt, setStmt]
compileConstructor _ _ _ = error "compileConstructor: not a constructor"

-- Compile numeric value
compileNumeric :: String -> NVal -> JSM String
compileNumeric var (U64_V n) = set var $ show n ++ "n"
compileNumeric var (I64_V n) = set var $ show n ++ "n"
compileNumeric var (F64_V n) = set var $ show n
compileNumeric var (CHR_V c) = set var $ show (fromEnum c)

-- Compile binary operation
compileBinOp :: String -> NOp2 -> CT -> CT -> Int -> JSM String
compileBinOp var op a b dep = do
  aName <- fresh
  aStmt <- ctToJS' False aName a dep
  bName <- fresh
  bStmt <- ctToJS' False bName b dep
  retStmt <- set var $ "(" ++ aName ++ " " ++ operToJS op ++ " " ++ bName ++ ")"
  return $ concat [aStmt, bStmt, retStmt]

-- Compile unary operation
compileUnOp :: String -> NOp1 -> CT -> Int -> JSM String
compileUnOp var NOT a dep = do
  aName <- fresh
  aStmt <- ctToJS' False aName a dep
  retStmt <- set var $ "~" ++ aName
  return $ aStmt ++ retStmt
compileUnOp var NEG a dep = do
  aName <- fresh
  aStmt <- ctToJS' False aName a dep
  retStmt <- set var $ "-" ++ aName
  return $ aStmt ++ retStmt

-- Compile lambda
compileLambda :: String -> CT -> Int -> JSM String
compileLambda var lam dep = do
  let (names, bodyTerm, newDep) = collectLambdas lam dep
  bodyName <- fresh
  bodyStmt <- ctToJS' False bodyName bodyTerm newDep
  set var $ "(" ++ intercalate " => " names ++ " => {" ++ bodyStmt ++ "return " ++ bodyName ++ ";})"
  where
    collectLambdas :: CT -> Int -> ([String], CT, Int)
    collectLambdas (CLam n b) d =
      let uid = n
          (names, term, finalDep) = collectLambdas (b (CVar uid d)) (d + 1)
      in (uid : names, term, finalDep)
    collectLambdas term d = ([], term, d)

-- Compile switch elimination
compileSwi :: CTBook -> String -> [String] -> Bool -> String -> CT -> CT -> CT -> Int -> JSM String
compileSwi book fnName fnArgs isTail var z s val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  let switch = "switch (" ++ valName ++ ".$) { "
  
  -- Zero case
  zStmt <- ctToJS book fnName fnArgs isTail var z dep
  let zCase = "case \"Zer\": { " ++ zStmt ++ " break; }"
  
  -- Successor case with inlining and proper binding
  sCase <- case s of
    CLam param f -> do
      let predVar = valName ++ ".pred"
      let paramName = param
      succStmt <- ctToJS book fnName fnArgs isTail var (f (CVar paramName dep)) dep
      return $ "case \"Suc\": { var " ++ paramName ++ " = " ++ predVar ++ "; " ++ succStmt ++ " break; }"
    _ -> do
      sName <- fresh
      sStmt <- ctToJS' False sName s dep
      appStmt <- ctToJS book fnName fnArgs isTail var (CApp (CVar sName dep) (CVar (valName ++ ".pred") dep)) dep
      return $ "case \"Suc\": { " ++ sStmt ++ appStmt ++ " break; }"
  
  return $ valStmt ++ switch ++ zCase ++ " " ++ sCase ++ " }"

-- Compile match elimination
compileMat :: CTBook -> String -> [String] -> Bool -> String -> CT -> CT -> CT -> Int -> JSM String
compileMat book fnName fnArgs isTail var n c val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  let switch = "switch (" ++ valName ++ ".$) { "
  
  -- Nil case
  nStmt <- ctToJS book fnName fnArgs isTail var n dep
  let nCase = "case \"Nil\": { " ++ nStmt ++ " break; }"
  
  -- Cons case with inlining and proper binding
  cCase <- case c of
    CLam hParam f1 -> case f1 (CVar hParam dep) of
      CLam tParam f2 -> do
        let headVar = valName ++ ".head"
        let tailVar = valName ++ ".tail"
        let hParamName = hParam
        let tParamName = tParam
        consStmt <- ctToJS book fnName fnArgs isTail var (f2 (CVar tParamName (dep + 1))) (dep + 2)
        return $ "case \"Con\": { var " ++ hParamName ++ " = " ++ headVar ++ "; var " ++ tParamName ++ " = " ++ tailVar ++ "; " ++ consStmt ++ " break; }"
      _ -> compileDefaultCons valName
    _ -> compileDefaultCons valName
  
  return $ valStmt ++ switch ++ nCase ++ " " ++ cCase ++ " }"
  where
    compileDefaultCons valName = do
      cName <- fresh
      cStmt <- ctToJS' False cName c dep
      let app1 = CApp (CVar cName dep) (CVar (valName ++ ".head") dep)
      let app2 = CApp app1 (CVar (valName ++ ".tail") dep)
      appStmt <- ctToJS book fnName fnArgs isTail var app2 dep
      return $ "case \"Con\": { " ++ cStmt ++ appStmt ++ " break; }"

-- Compile get (pair elimination)
compileGet :: CTBook -> String -> [String] -> Bool -> String -> CT -> CT -> Int -> JSM String
compileGet book fnName fnArgs isTail var f val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  
  case f of
    CLam aParam f1 -> case f1 (CVar aParam dep) of
      CLam bParam f2 -> do
        let fstVar = valName ++ "[0]"
        let sndVar = valName ++ "[1]"
        let aParamName = aParam
        let bParamName = bParam
        appStmt <- ctToJS book fnName fnArgs isTail var (f2 (CVar bParamName (dep + 1))) (dep + 2)
        return $ valStmt ++ "var " ++ aParamName ++ " = " ++ fstVar ++ "; var " ++ bParamName ++ " = " ++ sndVar ++ "; " ++ appStmt
      _ -> compileDefaultGet valName valStmt
    _ -> compileDefaultGet valName valStmt
  where
    compileDefaultGet valName valStmt = do
      fName <- fresh
      fStmt <- ctToJS' False fName f dep
      let app1 = CApp (CVar fName dep) (CVar (valName ++ "[0]") dep)
      let app2 = CApp app1 (CVar (valName ++ "[1]") dep)
      appStmt <- ctToJS book fnName fnArgs isTail var app2 dep
      return $ concat [valStmt, fStmt, appStmt]

-- Compile application
compileApp :: CTBook -> String -> [String] -> Bool -> String -> CT -> Int -> JSM String
compileApp book fnName fnArgs isTail var app dep = do
  let (appFun, appArgs) = getAppChain app
  
  -- Tail recursive call
  if isTail && isRecCall fnName (length fnArgs) appFun appArgs then
    compileTailCall fnArgs appArgs dep
  -- Eliminator applications
  else case appFun of
    CSwi z s | length appArgs == 1 -> 
      compileSwi book fnName fnArgs isTail var z s (head appArgs) dep
    CBif f t | length appArgs == 1 -> 
      compileBif book fnName fnArgs isTail var f t (head appArgs) dep
    CMat n c | length appArgs == 1 -> 
      compileMat book fnName fnArgs isTail var n c (head appArgs) dep
    CCse c d | length appArgs == 1 -> 
      compileCse book fnName fnArgs isTail var c d (head appArgs) dep
    CGet f | length appArgs == 1 -> 
      compileGet book fnName fnArgs isTail var f (head appArgs) dep
    CUse f | length appArgs == 1 -> 
      compileUse book fnName fnArgs isTail var f (head appArgs) dep
    CEql f | length appArgs == 1 -> 
      compileUse book fnName fnArgs isTail var f (head appArgs) dep
    _ | isSatCall book appFun appArgs -> 
      compileSaturatedCall appFun appArgs var dep
    _ -> 
      compileNormalApp var appFun appArgs dep

-- Compile tail call
compileTailCall :: [String] -> [CT] -> Int -> JSM String
compileTailCall fnArgs appArgs dep = do
  argDefs <- forM (zip fnArgs appArgs) $ \(paramName, appArg) -> do
    argName <- fresh
    argStmt <- ctToJS' False argName appArg dep
    return (argStmt, paramName ++ " = " ++ argName ++ ";")
  let (argStmts, paramDefs) = unzip argDefs
  return $ concat argStmts ++ concat paramDefs ++ "/*TCO*/continue;"

-- Compile saturated call
compileSaturatedCall :: CT -> [CT] -> String -> Int -> JSM String
compileSaturatedCall (CRef funName) appArgs var dep = do
  argNamesStmts <- forM appArgs $ \arg -> do
    argName <- fresh
    argStmt <- ctToJS' False argName arg dep
    return (argName, argStmt)
  retStmt <- set var $ nameToJS funName ++ "$(" ++ intercalate ", " (map fst argNamesStmts) ++ ")"
  return $ concat (map snd argNamesStmts ++ [retStmt])
compileSaturatedCall _ _ _ _ = error "Saturated call with non-reference"

-- Compile normal application
compileNormalApp :: String -> CT -> [CT] -> Int -> JSM String
compileNormalApp var fun [] _ = ctToJS' False var fun 0
compileNormalApp var fun (arg:args) dep = do
  funName <- fresh
  funStmt <- ctToJS' False funName fun dep
  argName <- fresh
  argStmt <- ctToJS' False argName arg dep
  if null args then do
    retStmt <- set var $ "(" ++ funName ++ ")(" ++ argName ++ ")"
    return $ concat [funStmt, argStmt, retStmt]
  else
    let partialApp = CApp (CVar funName dep) (CVar argName dep)
    in do
      partStmts <- concat <$> sequence [return funStmt, return argStmt]
      restStmt <- compileNormalApp var partialApp args dep
      return $ partStmts ++ restStmt

-- Helper for other eliminators
compileBif :: CTBook -> String -> [String] -> Bool -> String -> CT -> CT -> CT -> Int -> JSM String
compileBif book fnName fnArgs isTail var f t val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  fStmt <- ctToJS book fnName fnArgs isTail var f dep
  tStmt <- ctToJS book fnName fnArgs isTail var t dep
  return $ valStmt ++ "if (" ++ valName ++ ") { " ++ tStmt ++ " } else { " ++ fStmt ++ " }"

-- compileCse :: CTBook -> String -> [String] -> Bool -> String -> [(String, CT)] -> CT -> Int -> JSM String
-- compileCse book fnName fnArgs isTail var cases val dep = do
  -- valName <- fresh
  -- valStmt <- ctToJS' False valName val dep
  -- casesCode <- forM cases $ \(s, t) -> do
    -- tStmt <- ctToJS book fnName fnArgs isTail var t dep
    -- return $ "if (" ++ valName ++ " === \"" ++ s ++ "\") { " ++ tStmt ++ " }"
  -- let joined = intercalate " else " casesCode
  -- return $ valStmt ++ joined

compileCse :: CTBook -> String -> [String] -> Bool -> String -> [(String, CT)] -> CT -> CT -> Int -> JSM String
compileCse book fnName fnArgs isTail var cases d val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  casesCode <- forM cases $ \(s, t) -> do
    tStmt <- ctToJS book fnName fnArgs isTail var t dep
    return $ "if (" ++ valName ++ " === \"" ++ s ++ "\") { " ++ tStmt ++ " }"
  -- Handle default case - apply d to val
  dName <- fresh
  dStmt <- ctToJS' False dName d dep
  defaultStmt <- ctToJS book fnName fnArgs isTail var (CApp (CVar dName dep) (CVar valName dep)) dep
  let defaultCase = "{ " ++ dStmt ++ defaultStmt ++ " }"
  let joined = if null casesCode
               then defaultCase
               else intercalate " else " casesCode ++ " else " ++ defaultCase
  return $ valStmt ++ joined

compileUse :: CTBook -> String -> [String] -> Bool -> String -> CT -> CT -> Int -> JSM String
compileUse book fnName fnArgs isTail var f val dep = do
  valName <- fresh
  valStmt <- ctToJS' False valName val dep
  fStmt <- ctToJS book fnName fnArgs isTail var f dep
  return $ valStmt ++ fStmt

-- Main CT to JS compiler
ctToJS :: CTBook -> String -> [String] -> Bool -> String -> CT -> Int -> JSM String
ctToJS book fnName fnArgs isTail var term dep = case term of
  CVar k _    -> set var k
  CRef k      -> set var $ nameToJS k
  CSuc _      -> compileConstructor var term dep
  CCon _ _    -> compileConstructor var term dep
  CTup _ _    -> compileConstructor var term dep
  CVal v      -> compileNumeric var v
  COp2 op a b -> compileBinOp var op a b dep
  COp1 op a   -> compileUnOp var op a dep
  CLam _ _    -> compileLambda var term dep
  CApp _ _    -> compileApp book fnName fnArgs isTail var term dep
  CLet v f    -> compileLet var v f dep
  CFix k f    -> compileFix var k f dep
  CZer        -> set var "{$:\"Zer\"}"
  CBt0        -> set var "false"
  CBt1        -> set var "true"
  COne        -> set var "null"
  CNil        -> set var "{$:\"Nil\"}"
  CSym s      -> set var $ "\"" ++ s ++ "\""
  CSwi _ _    -> set var "(x => null)"
  CBif _ _    -> set var "(x => null)"
  CMat _ _    -> set var "(x => null)"
  CCse _ _    -> set var "(x => null)"
  CGet _      -> set var "(x => null)"
  CUse _      -> set var "(x => null)"
  CEql _      -> set var "(x => null)"
  CEra        -> set var "null"
  CSup _ _ _  -> error "Superpositions not supported in JavaScript backend"
  CSupM _ _ _ -> error "Superpositions not supported in JavaScript backend"
  CFrk _ _ _  -> error "Superpositions not supported in JavaScript backend"
  CPri p      -> compilePri p
  where

    compilePri p = case p of
      U64_TO_CHAR -> set var "(x => String.fromCharCode(Number(x)))"
      CHAR_TO_U64 -> set var "(x => BigInt(x.charCodeAt(0)))"
      HVM_INC     -> set var "(x => x)"
      HVM_DEC     -> set var "(x => x)"

    compileLet var v f dep = do
      vName <- fresh
      vStmt <- ctToJS' False vName v dep
      retStmt <- ctToJS book fnName fnArgs isTail var (f (CVar vName dep)) (dep + 1)
      return $ vStmt ++ retStmt

    compileFix var k f dep = do
      let fixName = k
      bodyStmt <- ctToJS book fnName fnArgs isTail var (f (CVar fixName dep)) (dep + 1)
      return $ "var " ++ fixName ++ " = () => { " ++ bodyStmt ++ " }; " ++ bodyStmt

-- Helper for non-tail calls
ctToJS' :: Bool -> String -> CT -> Int -> JSM String
ctToJS' = ctToJS M.empty "" []

-- Generate JavaScript for a definition
generateJS :: CTBook -> (String, CT) -> String
generateJS book (name, ct) = ST.evalState (fnToJS book name ct) 0 ++ "\n"

-- Prelude
prelude :: String
prelude = unlines [
  "// Bend to JavaScript Compiler Output",
  ""
  ]

-- Compile book to JavaScript
compile :: Book -> String
compile (Book defs names) =
  let ctDefs = map (\(name, (_, term, _)) -> (name, termToCT (Book defs names) term 0)) (M.toList defs)
      ctBook = M.fromList ctDefs
      jsFns = concatMap (generateJS ctBook) ctDefs
  in prelude ++ jsFns
