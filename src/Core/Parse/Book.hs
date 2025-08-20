{-./../Type.hs-}

module Core.Parse.Book 
  ( parseBook
  , doParseBook
  , doReadBook
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (intercalate)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Map.Strict as M
import qualified Text.Megaparsec.Char.Lexer as L

import Debug.Trace

import Core.Adjust.Adjust
import Core.Parse.Parse
import Core.Parse.Term (parseTerm, parseTermBefore)
import Core.Type
import Core.Show

-- | Book parsing

-- | Syntax: def name : Type = term | type Name<T>(i) -> Type: cases | name : Type = term | try name : Type | assert A == B : T
parseDefinition :: Parser (Name, Defn)
parseDefinition = do
  (name, defn) <- choice [ parseType , parseDef , parseTry , parseAssert ]
  return $ (name, defn)

-- | Syntax: def name : Type = term | def name(x: T1, y: T2) -> RetType: body
parseDef :: Parser (Name, Defn)
parseDef = do
  _ <- symbol "def"
  f <- name
  choice
    [ parseDefFunction f
    , parseDefSimple f ]

-- | Syntax: def name : Type = term
parseDefSimple :: Name -> Parser (Name, Defn)
parseDefSimple defName = do
  _ <- symbol ":"
  t <- parseTermBefore "="
  _ <- symbol "="
  x <- expectBody ("'=' for '" ++ defName ++ "'") parseTerm
  return (defName, (False, x, t))

-- | Syntax: def name(x: Type1, y: Type2) -> ReturnType: body
--           def name<A, B>(x: Type1, y: Type2) -> ReturnType: body
parseDefFunction :: Name -> Parser (Name, Defn)
parseDefFunction f = label "function definition" $ do
  -- Parse optional generic type parameters <A, B, ...>
  typeParams <- option [] $ angles $ sepEndBy name (symbol ",")
  -- Convert type params to arguments with type Set
  let typeArgs = [(tp, Set) | tp <- typeParams]
  -- Parse regular arguments
  regularArgs <- parens $ sepEndBy (parseArg False) (symbol ",")
  -- Combine type params (as Set-typed args) with regular args
  let args = typeArgs ++ regularArgs
  _ <- symbol "->"
  returnType <- parseTermBefore ":"
  _ <- symbol ":"
  body <- expectBody ("type signature for '" ++ f ++ "()'") parseTerm
  let (typ, bod) = foldr nestTypeBod (returnType, body) args
  return (f, (False, bod, typ))
  where
    -- parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)
    -- TODO: refactor parseArg to use a do-block instead. DO IT BELOW:
    nestTypeBod (argName, argType) (currType, currBod) = (All argType (Lam argName (Just argType) (\v -> currType)), Lam argName (Just argType) (\v -> currBod))

-- | Parse a module path like Path/To/Lib
parseModulePath :: Parser String
parseModulePath = do
  firstPart <- name
  restParts <- many (try $ char '/' >> name)
  skip -- consume whitespace after path
  return $ intercalate "/" (firstPart : restParts)

-- | Add an import mapping to the parser state
addImportMapping :: String -> String -> Parser ()
addImportMapping alias path = do
  st <- get
  let aliasKey = alias ++ "/"
      pathValue = path ++ "/"
      newImports = M.insert aliasKey pathValue (imports st)
  put st { imports = newImports }

-- | Syntax: import Path/To/Lib as Lib
parseImport :: Parser ()
parseImport = do
  _ <- symbol "import"
  path <- parseModulePath
  _ <- symbol "as"
  alias <- name
  addImportMapping alias path

-- | Syntax: import statements followed by definitions
parseBook :: Parser Book
parseBook = do
  -- Parse all import statements first
  _ <- many (try parseImport)
  -- Then parse definitions
  defs <- many parseDefinition
  let names = map fst defs
  return $ Book (M.fromList defs) names

-- | Syntax: type Name<T, U>(i: Nat) -> Type: case @Tag1: field1: T1 case @Tag2: field2: T2
parseType :: Parser (Name, Defn)
parseType = label "datatype declaration" $ do
  _       <- symbol "type"
  tName   <- name
  params  <- option [] $ angles (sepEndBy (parseArg True) (symbol ","))
  indices <- option [] $ parens (sepEndBy (parseArg False) (symbol ","))
  args    <- return $ params ++ indices
  retTy   <- option Set (symbol "->" *> parseTerm)
  _       <- symbol ":"
  cases   <- many parseTypeCase
  when (null cases) $ fail "datatype must have at least one constructor case"
  let tags = map fst cases
      mkFields :: [(Name, Term)] -> Term
      mkFields []             = Uni
      mkFields ((fn,ft):rest) = Sig ft (Lam fn (Just ft) (\_ -> mkFields rest))
      --   match ctr: case @Tag: …
      branches v = Pat [v] [] [([Sym tag], mkFields flds) | (tag, flds) <- cases]
      -- The body of the definition (see docstring).
      body0 = Sig (Enu tags) (Lam "ctr" (Just $ Enu tags) (\v -> branches v))
      -- Wrap the body with lambdas for the parameters.
      nest (n, ty) (tyAcc, bdAcc) = (All ty  (Lam n (Just ty) (\_ -> tyAcc)) , Lam n (Just ty) (\_ -> bdAcc))
      (fullTy, fullBody) = foldr nest (retTy, body0) args
      term = fullBody
  return (tName, (True, term, fullTy))

-- | Syntax: case @Tag: field1: Type1 field2: Type2
parseTypeCase :: Parser (String, [(Name, Term)])
parseTypeCase = label "datatype constructor" $ do
  _    <- symbol "case"
  _    <- symbol "@"
  tag  <- some (satisfy isNameChar)
  _    <- symbol ":"
  flds <- many parseField
  return (tag, flds)
  where
    -- Parse a field declaration  name : Type
    parseField :: Parser (Name, Term)
    parseField = do
      -- Stop if next token is 'case' (start of next constructor) or 'def'/'data'
      notFollowedBy (symbol "case")
      n <- try $ do
        n <- name
        _ <- symbol ":"
        return n
      t <- parseTerm
      -- Optional semicolon or newline is already handled by lexeme
      return (n,t)

parseArg :: Bool -> Parser (Name, Term)
parseArg expr = do
  k <- name
  _ <- symbol ":"
  t <- if expr then parseTerm else parseTerm
  return (k, t)

-- | Syntax: try name : Type { t1, t2, ... } | try name(x: Type1, y: Type2) -> Type { t1, t2, ... }
parseTry :: Parser (Name, Defn)
parseTry = do
  -- Insert a Loc span for text replacement in bendgen
  (sp, (f, x, t)) <- withSpan $ do
    _ <- symbol "try"
    f <- name
    (x, t) <- choice [parseTryFunction f, parseTrySimple f]
    return (f, x, t)
  return (f, (False, Loc sp x, t))

parseTrySimple :: Name -> Parser (Term, Type)
parseTrySimple nam = do
  _   <- symbol ":"
  typ <- parseTerm
  ctx <- option [] $ braces $ sepEndBy parseTerm (symbol ",")
  return (Met nam typ ctx, typ)

parseTryFunction :: Name -> Parser (Term, Type)
parseTryFunction nam = label "try definition" $ do
  tyParams <- option [] $ angles $ sepEndBy name (symbol ",")
  regularArgs <- parens $ sepEndBy (parseArg False) (symbol ",")
  let args = [(tp, Set) | tp <- tyParams] ++ regularArgs
  _        <- symbol "->"
  retTyp   <- parseTerm
  let typ  = foldr (\(nm,ty) acc -> All ty (Lam nm Nothing (\_ -> acc))) retTyp args
  ctx      <- option [] $ braces $ sepEndBy parseTerm (symbol ",")
  return (Met nam typ ctx, typ)

-- | Syntax: assert A == B : T
-- Desugars to: def EN : T{A == B} = {==} where N is an incrementing counter
parseAssert :: Parser (Name, Defn)
parseAssert = do
  _ <- keyword "assert"
  a <- parseTermBefore "=="
  _ <- symbol "=="
  b <- parseTermBefore ":"
  _ <- symbol ":"
  t <- parseTerm
  -- Get and increment the assert counter
  st <- get
  let counter = assertCounter st
  put st { assertCounter = counter + 1 }
  -- Generate the assert name EN
  let assertName = "E" ++ show counter
  -- Create the equality type: T{A == B}
  let eqType = Eql t a b
  -- Create the reflexivity proof: {==}
  let eqProof = Rfl
  return (assertName, (False, eqProof, eqType))

-- | Main entry points

-- | Parse a book from a string, returning an error message on failure
doParseBook :: FilePath -> String -> Either String Book
doParseBook file input =
  case evalState (runParserT p file input) (ParserState True input [] M.empty 0) of
    Left err  -> Left (formatError input err)
    Right res -> Right res
      -- in Right (trace (show book) book)
  where
    p = do
      skip
      book <- parseBook
      skip
      eof
      return book

-- | Parse a book from a string, crashing on failure
doReadBook :: String -> Book
doReadBook input =
  case doParseBook "<input>" input of
    Left err  -> error err
    Right res -> res
