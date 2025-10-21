{-./../Type.hs-}

module Core.Parse.Book
  ( parseBook
  , doParseBook
  , doReadBook
  ) where

import Control.Monad (when)
import Control.Monad.State.Strict (State, get, put, evalState, runState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit, isAlphaNum)
import Data.List (intercalate)
import Data.List.Split (splitOn)
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

-- | Syntax: def name : Type = term | type Name<T>(i) -> Type: cases | name : Type = term | gen name : Type | assert A == B : T
parseDefinition :: Parser (Name, Defn)
parseDefinition = do
  (name, defn) <- choice [ parseType , parseDef , parseGen , parseAssert ]
  return $ (name, defn)

-- | Syntax: def name : Type = term | def name(x: T1, y: T2) -> RetType: body
parseDef :: Parser (Name, Defn)
parseDef = do
  _ <- symbol "def"
  f <- definitionName
  qualifiedName <- qualifyName f
  choice
    [ parseDefFunction qualifiedName
    , parseDefSimple qualifiedName ]

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

addImport :: Import -> Parser ()
addImport imp = do
  st <- get
  put st { parsedImports = imp : parsedImports st }

-- | Syntax: import <target> as <alias>
parseImport :: Parser ()
parseImport = do
  (sp, (target, alias)) <- withSpan $ do
    _ <- symbol "import"
    tgt <- parseImportTarget
    _ <- symbol "as"
    als <- name
    pure (tgt, als)
  addImport (ImportAlias target alias sp)

-- | Parse the import target, allowing both path-only and FQN forms.
parseImportTarget :: Parser String
parseImportTarget = lexeme $ do
  pathParts <- sepBy1 parseSegment (char '/')
  pure $ intercalate "/" pathParts
  where
    parseSegment :: Parser String
    parseSegment = some (satisfy isSegmentChar <?> "path character")

    isSegmentChar :: Char -> Bool
    isSegmentChar c =
      isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '@' || c == '-' || c == '=' || c == '$'


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
  tName   <- definitionName
  qualifiedTypeName <- qualifyName tName
  params  <- option [] $ angles (sepEndBy (parseArg True) (symbol ","))
  indices <- option [] $ parens (sepEndBy (parseArg False) (symbol ","))
  args    <- return $ params ++ indices
  retTy   <- option Set (symbol "->" *> parseTerm)
  _       <- symbol ":"
  cases   <- many (parseTypeCase qualifiedTypeName)
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
  return (qualifiedTypeName, (True, term, fullTy))

-- | Syntax: case @Tag: field1: Type1 field2: Type2
parseTypeCase :: String -> Parser (String, [(Name, Term)])
parseTypeCase typeName = label "datatype enum" $ do
  _    <- symbol "case"
  _    <- symbol "@"
  tag  <- some (satisfy isNameChar)
  _    <- symbol ":"
  flds <- many parseField
  -- Return the fully qualified enum name
  let qualifiedTag = typeName ++ "::" ++ tag
  return (qualifiedTag, flds)
  where
    -- Parse a field declaration  name : Type
    parseField :: Parser (Name, Term)
    parseField = do
      -- Stop if next token is 'case' (start of next enum) or 'def'/'data'
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

-- | Syntax: gen name : Type { t1, t2, ... } | gen name(x: Type1, y: Type2) -> Type { t1, t2, ... }
parseGen :: Parser (Name, Defn)
parseGen = do
  -- Insert a Loc span for text replacement in bendgen
  (sp, (f, x, t)) <- withSpan $ do
    _ <- symbol "gen"
    f <- definitionName
    qualifiedName <- qualifyName f
    (x, t) <- choice [parseGenFunction qualifiedName, parseGenSimple qualifiedName]
    return (qualifiedName, x, t)
  return (f, (False, Loc sp x, t))

parseGenSimple :: Name -> Parser (Term, Type)
parseGenSimple nam = do
  _   <- symbol ":"
  typ <- parseTerm
  ctx <- option [] $ braces $ sepEndBy parseTerm (symbol ",")
  return (Met nam typ ctx, typ)

parseGenFunction :: Name -> Parser (Term, Type)
parseGenFunction nam = label "gen definition" $ do
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

-- | Parse a book from a string, returning both the book and the import information
doParseBook :: FilePath -> String -> Either String (Book, ParserState)
doParseBook file input =
  case runState (runParserT p file input) (ParserState True input [] [] 0 file) of
    (Left err, _)    -> Left (formatError input err)
    (Right res, st)  -> Right (res, st)
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
    Right (book, _) -> book
