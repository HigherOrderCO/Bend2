{-./../Type.hs-}
{-./../Parse.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Parse.Term 
  ( parseTerm
  , parseTermBefore
  , doParseTerm
  , doReadTerm
  ) where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
import Data.List (intercalate)
import Data.Void
import Data.Word (Word64)
import Text.Megaparsec
import Text.Megaparsec (anySingle, manyTill, lookAhead)
import Text.Megaparsec.Char
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import qualified Text.Megaparsec.Char.Lexer as L

import Debug.Trace

import Core.Adjust.Adjust
import Core.Parse.Parse
import Core.Type
import Core.Show

-- | Parse a "core" form
parseTermIni :: Parser Term
parseTermIni = choice
  [ parseFix
  , parseLam
  , parseLamMatch
  , parseBifIf
  , parsePat
  , parseRewrite
  , parseAbsurd
  , parseFrk
  , parseTrust
  , parseLog
  , parseAll
  , parseSig
  , parseTildeExpr
  , parseOne
  , parseEra
  , parseSup
  , parseReturn
  , parseNat
  , parseNatLit
  , parseNumLit
  , parseNumUna
  , parseCharLit
  , parseStringLit
  , parseLstLit
  , parseNil
  , parseRfl
  , parseEnu
  , parseSym
  , parseTupApp
  , parseView
  , parseVar
  ]

-- | Parse a "tight" postfix: f(...) | f[] | f{x == y} ...
parseTermArg :: Term -> Parser Term
parseTermArg t = do
  st <- get
  guard (tight st)
  mb <- optional $ choice
    [ parsePol t   -- f<...>
    , parseCal t   -- f(...)
    , parseEql t   -- f{x == y}
    , parseLst t ] -- f[]
  maybe (pure t) parseTermArg mb
  <|> pure t

-- | Parse a "loose" postfix: f + x | f <> x | ...
parseTermOpr :: Term -> Parser Term
parseTermOpr t = choice
  [ parseCon t   -- <>
  , parseFun t   -- ->
  , parseAnd t   -- &
  , parseChk t   -- ::
  , parseAdd t   -- +
  , parseNumOp t -- <, >, ==, etc.
  , parseAss t   -- =
  , return t ]

-- | A helper that conditionally applies a postfix/infix parser to a term.
-- The parser is only applied if the next token is not in the 'blocked' list.
-- This is the core of the operator-blocking mechanism that allows for context-
-- sensitive parsing, preventing ambiguity in expressions like `~ term { ... }`.
-- | A helper that conditionally applies a postfix/infix parser to a term.
-- The parser is only applied if the next token is not in the 'blocked' list.
-- This is the core of the operator-blocking mechanism that allows for context-
-- sensitive parsing, preventing ambiguity in expressions like `if ...:` or
-- `~ term { ... }`, where certain trailing operators must not be parsed.
withOperatorParsing :: Term -> (Term -> Parser Term) -> Parser Term
withOperatorParsing term operatorParser = do
  st <- get
  -- If the blocked list is empty, we can always parse the operator.
  if null (blocked st)
    then operatorParser term
    else do
      -- Peek ahead to see if the next token is a blocked operator.
      -- `lookAhead` does this without consuming input. `symbol` handles whitespace.
      isBlocked <- optional . lookAhead . choice . map (try . symbol) $ blocked st
      case isBlocked of
        -- The next token is blocked, so we must not parse it as an operator.
        -- We return the term as-is, without applying the operator parser.
        Just _  -> return term
        -- The next token is not blocked, so we proceed with the operator parser.
        Nothing -> operatorParser term

-- | Top-level entry point for parsing a term.
-- It parses in three stages:
-- 1. An initial, "atomic" term (`parseTermIni`).
-- 2. A chain of "tight" postfix operators like application `f(x)` (`parseTermArg`).
-- 3. A "loose" infix operator like `+` or `->` (`parseTermOpr`).
-- The `withOperatorParsing` helper ensures that stages 2 and 3 are skipped
-- if a "blocked" operator is encountered, resolving grammatical ambiguities.
parseTerm :: Parser Term
parseTerm = located $ do
  t0 <- parseTermIni
  t1 <- withOperatorParsing t0 parseTermArg
  t2 <- withOperatorParsing t1 parseTermOpr
  return t2

-- | Parses a term, temporarily blocking a given operator.
-- This is useful for parsing expressions where an operator might be ambiguous
-- in the grammar, e.g., `~ term { ... }` where `term` should not be an
-- infix expression that includes `{`.
parseTermBefore :: String -> Parser Term
parseTermBefore op = do
  st <- get
  let wasBlocked = blocked st
  let newBlocked = op : wasBlocked
  put st { blocked = newBlocked }
  -- Use observing to catch parse failures and ensure cleanup
  termResult <- observing parseTerm
  case termResult of
    Left err -> do
      -- Restore blocked state before re-throwing the error
      st' <- get
      put st' { blocked = wasBlocked }
      parseError err
    Right term -> do
      -- Normal restoration path
      st' <- get
      put st' { blocked = wasBlocked }
      return term


-- | Syntax: x, foo, bar_123, Type<A,B>, Nat/add
parseVar :: Parser Term
parseVar = label "variable" $ do
  n <- name
  -- Check for qualified reference (module::name)
  qualified <- option n $ try $ do
    _ <- symbol "::"
    qualifiedName <- name
    return $ n ++ "::" ++ qualifiedName
  case qualified of
    "Set"         -> return Set
    "Empty"       -> return Emp
    "Unit"        -> return Uni
    "Bool"        -> return Bit
    "False"       -> return Bt0
    "True"        -> return Bt1
    "Nat"         -> return Nat
    "U64"         -> return (Num U64_T)
    "I64"         -> return (Num I64_T)
    "F64"         -> return (Num F64_T)
    "Char"        -> return (Num CHR_T)
    "U64_TO_CHAR" -> return (Pri U64_TO_CHAR)
    "CHAR_TO_U64" -> return (Pri CHAR_TO_U64)
    "HVM_INC"     -> return (Pri HVM_INC)
    "HVM_DEC"     -> return (Pri HVM_DEC)
    _             -> return $ Var qualified 0

-- | Syntax: ()
parseOne :: Parser Term
parseOne = label "unit value (())" $ symbol "()" >> return One

-- | Syntax: *
parseEra :: Parser Term
parseEra = label "Eraser" $ symbol "*" >> return Era

-- | Syntax: &L{a,b}
parseSup :: Parser Term
parseSup = label "superposition" $ do
  l <- try $ do
    _ <- symbol "&"
    l <- parseTermBefore "{"
    _ <- symbol "{"
    return $ l
  a <- parseTerm
  _ <- symbol ","
  b <- parseTerm
  _ <- symbol "}"
  return $ Sup l a b

-- | Syntax: if condition: trueCase else: falseCase
parseBifIf :: Parser Term
parseBifIf = label "if clause" $ do
  _ <- try $ keyword "if"
  -- Block ':' so it can't be parsed as a trailing operator
  -- on the scrutinee by downstream postfix/infix parsers.
  condition <- parseTermBefore ":"
  _ <- symbol ":"
  -- Block operator parsing when we hit 'else' to avoid
  -- consuming into the else-branch accidentally.
  trueCase <- parseTermBefore "else"
  _ <- symbol "else"
  _ <- symbol ":"
  falseCase <- parseTerm
  return $ App (BitM falseCase trueCase) condition

-- | Syntax: Σ x: Type. body | any x: Type. body | Σ Type. Type | any Type. Type
parseSig :: Parser Term
parseSig = label "dependent pair type" $ do
  _ <- try $ choice [symbol "Σ", keyword "any"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseSigSimple
    _  -> do
      _ <- symbol "."
      b <- parseTerm
      return $ foldr (\(x, t) acc -> Sig t (Lam x (Just t) (\v -> acc))) b bindings
  where
    parseBinding = try $ do
      x <- name
      _ <- symbol ":"
      t <- parseTerm
      return (x, t)

-- | Syntax: Type . Type
-- Simplified form of dependent pair without binding
parseSigSimple :: Parser Term
parseSigSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (Sig a b)

-- | Syntax: ∀ x: Type. body | all x: Type. body | ∀ Type. Type | all Type. Type
parseAll :: Parser Term
parseAll = label "dependent function type" $ do
  _ <- try $ choice [symbol "∀", keyword "all"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseAllSimple
    _  -> do
      _ <- symbol "."
      b <- parseTerm
      return $ foldr (\(x, t) acc -> All t (Lam x (Just t) (\v -> acc))) b bindings
  where
    parseBinding = try $ do
      x <- name
      _ <- symbol ":"
      t <- parseTerm
      return (x, t)

-- | Syntax: Type . Type
-- Simplified form of dependent function without binding
parseAllSimple :: Parser Term
parseAllSimple = do
  a <- parseTerm
  _ <- symbol "."
  b <- parseTerm
  return (All a b)

-- Enum Type Parsers
-- -----------------

-- | Syntax: &{tag1, tag2, tag3}
parseEnu :: Parser Term
parseEnu = label "enum type" $ do
  _ <- try $ do
    _ <- symbol "enum"
    _ <- symbol "{"
    return ()
  s <- sepBy parseSymbolName (symbol ",")
  _ <- symbol "}"
  return (Enu s)

-- | Syntax: &name
-- Helper for parsing enum tag names
parseSymbolName :: Parser String
parseSymbolName = do
  _ <- symbol "&"
  n <- some (satisfy isNameChar)
  return n

-- | Syntax: @tag | @tag{field1, field2} | &tag
parseSym :: Parser Term
parseSym = label "enum symbol / constructor" $ try $ do
  choice
    [ parseConstructor  -- @tag{...} -> (&tag,(fields...))
    , parseNewSymbol    -- &tag
    , parseOldSymbol    -- @tag -> (&tag,())
    ]
  where
    -- Parse constructor name with optional FQN (e.g., Module::Type::Ctor)
    parseConstructorName = do
      parts <- sepBy1 (some (satisfy isNameChar)) (string "::")
      return $ intercalate "::" parts
    -- Parse @tag{...} constructor syntax with precise location propagation
    -- We capture two spans:
    -- - spTag: the span of "@tag" (for the &tag symbol)
    -- - spCtor: the span of the whole constructor "@tag{...}" (for the trailing ())
    parseConstructor = try $ do
      (spCtor, (spTag, tag, fields)) <- withSpan $ do
        (spTag, tag) <- withSpan $ do
          _ <- symbol "@"
          -- Parse constructor name, potentially with :: for FQN
          parseConstructorName
        _ <- symbol "{"
        fs <- sepEndBy parseTerm (symbol ",")
        _ <- symbol "}"
        pure (spTag, tag, fs)
      return $ buildCtorWithSpans spTag spCtor tag fields
    
    -- Parse new &tag bare symbol syntax  
    parseNewSymbol = try $ do
      _ <- char '&'
      notFollowedBy (char '{')  -- make sure we are not &{...} enum type
      n <- some (satisfy isNameChar)
      skip
      return $ Sym n
    
    -- Parse old @tag bare symbol syntax and desugar to (&tag,()) with location on both
    parseOldSymbol = try $ do
      (spTag, tag) <- withSpan $ do
        _ <- symbol "@"
        notFollowedBy (char '{')  -- make sure we are not @{...} or @tag{...}
        -- Parse constructor name, potentially with :: for FQN
        lexeme $ parseConstructorName
      -- Desugar @Foo to (&Foo,()) and attach the span to both the symbol and the unit
      let sym = Loc spTag (Sym tag)
      let one = Loc spTag One
      return $ Tup sym one
    
    -- Build (&tag, (f1, (f2, ... , Loc spCtor ())))
    buildCtorWithSpans :: Span -> Span -> String -> [Term] -> Term
    buildCtorWithSpans spTag spCtor tag fs =
      let end  = Loc spCtor One
          tup  = foldr Tup end fs
          sym  = Loc spTag (Sym tag)
      in Tup sym tup

-- | Syntax: match expr: case pat: body | match expr { case pat: body }
parsePat :: Parser Term
parsePat = label "pattern match" $ do
  srcPos  <- getSourcePos
  _       <- try $ keyword "match"
  scruts  <- some $ parseTermBefore ":"
  delim   <- choice [ ':' <$ symbol ":", '{' <$ symbol "{" ]
  moves   <- concat <$> many parseWith
  clauses <- case delim of
    ':' -> parseIndentClauses (unPos (sourceColumn srcPos)) (length scruts)
    '{' -> parseBraceClauses  (length scruts)
    _   -> fail "unreachable"
  when (delim == '{') (void $ symbol "}")
  _ <- optional (symbol ";")
  let pat = (Pat scruts moves clauses)
  pure pat
  where
    -- Parse 'with' statements
    parseWith = do
      _ <- try $ symbol "with"
      many (do
        x <- try name
        v <- option (Var x 0) (try (symbol "=" >> parseTerm))
        return (x, v))

-- | Syntax: case pattern1 pattern2: body
-- Indentation-sensitive clause list (stops when out-dented)
parseIndentClauses :: Int -> Int -> Parser [Case]
parseIndentClauses col arity = many clause where
    clause = label "case clause" $ do
      pos <- try $ do
        skip
        pos  <- getSourcePos
        guard (unPos (sourceColumn pos) >= col)
        _    <- symbol "case"
        return pos
      pats <- replicateM arity (parseTermBefore ":")
      _    <- symbol ":"
      body <- parseTerm
      pure (pats, body)

-- | Syntax: case pattern1 pattern2: body
-- Braced clause list (runs until the closing '}')
parseBraceClauses :: Int -> Parser [Case]
parseBraceClauses arity = manyTill singleClause (lookAhead (symbol "}")) where
  singleClause = label "case clause" $ do
    _    <- symbol "case"
    pats <- replicateM arity (parseTermBefore ":")
    _    <- symbol ":"
    body <- parseTerm
    pure (pats, body)

-- | Syntax: fork L:a else:b
--   or: fork L:a elif:b elif:c ... else:d
parseFrk :: Parser Term
parseFrk = label "fork" $ do
  _ <- try $ symbol "fork"
  -- Block ':' so it can't be parsed as a trailing operator
  -- on the scrutinee by downstream postfix/infix parsers.
  l <- parseTermBefore ":"
  _ <- symbol ":"
  -- Parse first branch; prevent it from consuming the following 'else'.
  a <- parseTermBefore "else"
  elifs <- many parseElif
  _ <- symbol "else"
  _ <- symbol ":"
  elseBranch <- parseTerm
  return $ buildForkChain l a elifs elseBranch
  where
    parseElif :: Parser Term
    parseElif = do
      _ <- keyword "elif"
      _ <- symbol ":"
      -- Parse elif branch; avoid consuming the subsequent 'else'.
      parseTermBefore "else"
    
    buildForkChain :: Term -> Term -> [Term] -> Term -> Term
    buildForkChain l firstBranch [] elseBranch = Frk l firstBranch elseBranch
    buildForkChain l firstBranch (elif:elifs) elseBranch = 
      Frk l firstBranch (buildForkChain l elif elifs elseBranch)

-- | Syntax: log string expr
parseLog :: Parser Term
parseLog = label "log" $ do
  _ <- try $ keyword "log"
  s <- parseTerm
  x <- parseTerm
  return $ Log s x

-- | Syntax: trust term
parseTrust :: Parser Term
parseTrust = label "trust" $ do
  _ <- try $ keyword "trust"
  t <- parseTerm
  return $ Tst t

-- | Syntax: view(functionName)
parseView :: Parser Term
parseView = label "view" $ do
  try $ do
    _ <- symbol "view"
    _ <- symbol "("
    return ()
  nam <- name
  _ <- symbol ")"
  return $ Var (nam ++ "$") 0

-- | Syntax: []
parseNil :: Parser Term
parseNil = label "empty list ([])" $ symbol "[]" >> return Nil

-- | Syntax: Nat
parseNat :: Parser Term
parseNat = label "natural number type (Nat)" $ try $ do
  _ <- symbol "Nat"
  notFollowedBy (satisfy isNameChar)
  return Nat

-- | Syntax: 1n, 2n, 3n, 42n, 123n
parseNatLit :: Parser Term
parseNatLit = label "natural number literal" $ try $ do
  -- Parse digits manually to avoid L.decimal consuming too much
  digits <- some digitChar
  _ <- char 'n'
  skip  -- consume whitespace after 'n'
  let n = read digits :: Integer
      build 0 = Zer
      build k = Suc (build (k - 1))
  return (build n)

-- | Parse numeric literals:
-- | 123    -> U64 (unsigned)
-- | +123   -> I64 (signed positive)
-- | -123   -> I64 (signed negative)  
-- | 123.0  -> F64 (floating point)
parseNumLit :: Parser Term
parseNumLit = label "numeric literal" $ choice
  [ try parseFloatLit    -- Try float first (because 123.0 starts like 123)
  , try parseSignedLit   -- Try signed next (because +123 starts with a sign)
  , parseUnsignedLit     -- Finally unsigned
  ]

-- | Parse floating point: 123.0, -45.67, +3.14, 0xFF.0, 0b101.0
parseFloatLit :: Parser Term
parseFloatLit = do
  sign <- optional (char '+' <|> char '-')
  intPart <- parseUnsignedNumber
  _ <- char '.'
  fracPart <- some digitChar
  skip
  let signStr = maybe "" (:[]) sign
      floatStr = signStr ++ show intPart ++ "." ++ fracPart
      floatVal = read floatStr :: Double
  return $ Val (F64_V floatVal)

-- | Parse signed integer: +123, -456, +0x123, -0xABC, +0b101, -0b110
parseSignedLit :: Parser Term
parseSignedLit = do
  sign <- char '+' <|> char '-'
  n <- parseUnsignedNumber
  skip
  let value = if sign == '-' then -(fromIntegral n) else fromIntegral n
  return $ Val (I64_V value)

-- | Parse a raw unsigned number (decimal, hex, or binary)
parseUnsignedNumber :: Parser Word64
parseUnsignedNumber = choice
  [ try $ string "0x" >> L.hexadecimal
  , try $ do
      _ <- string "0b"
      digits <- some (char '0' <|> char '1')
      return $ foldl (\acc d -> acc * 2 + if d == '1' then 1 else 0) 0 digits
  , L.decimal
  ]

-- | Parse unsigned integer: 123, 0x123, 0b101
parseUnsignedLit :: Parser Term
parseUnsignedLit = lexeme $ do
  n <- parseUnsignedNumber
  -- Make sure we don't have 'n' suffix (that would be a Nat literal)
  notFollowedBy (char 'n')
  return $ Val (U64_V n)

-- | Parse character literal: 'x', '\n', '\t', etc.
parseCharLit :: Parser Term
parseCharLit = label "character literal" $ lexeme $ do
  _ <- char '\''
  c <- parseChar
  _ <- char '\''
  return $ Val (CHR_V c)
  where
    parseChar = choice
      [ parseEscaped
      , satisfy (\c -> c /= '\'' && c /= '\\')
      ]
    
    parseEscaped = do
      _ <- char '\\'
      choice
        [ char 'n'  >> return '\n'
        , char 't'  >> return '\t'
        , char 'r'  >> return '\r'
        , char '0'  >> return '\0'
        , char '\\' >> return '\\'
        , char '\'' >> return '\''
        , char '"'  >> return '"'
        , parseUnicodeEscape
        ]
    
    parseUnicodeEscape = do
      _ <- char 'u'
      digits <- replicateM 4 (satisfy (\c -> isDigit c || c `elem` "abcdefABCDEF"))
      let code = read ("0x" ++ digits) :: Int
      return $ toEnum code

-- | Parse string literal: "hello\nworld"
-- Desugars to: 'h' <> 'e' <> 'l' <> 'l' <> 'o' <> '\n' <> 'w' <> 'o' <> 'r' <> 'l' <> 'd' <> []
parseStringLit :: Parser Term
parseStringLit = label "string literal" $ lexeme $ do
  _ <- char '"'
  chars <- many parseStringChar
  _ <- char '"'
  return $ foldr (\c acc -> Con (Val (CHR_V c)) acc) Nil chars
  where
    parseStringChar = choice
      [ parseStringEscaped
      , satisfy (\c -> c /= '"' && c /= '\\')
      ]
    
    parseStringEscaped = do
      _ <- char '\\'
      choice
        [ char 'n'  >> return '\n'
        , char 't'  >> return '\t'
        , char 'r'  >> return '\r'
        , char '0'  >> return '\0'
        , char '\\' >> return '\\'
        , char '\'' >> return '\''
        , char '"'  >> return '"'
        , parseStringUnicodeEscape
        ]
    
    parseStringUnicodeEscape = do
      _ <- char 'u'
      digits <- replicateM 4 (satisfy (\c -> isDigit c || c `elem` "abcdefABCDEF"))
      let code = read ("0x" ++ digits) :: Int
      return $ toEnum code

-- | Parse numeric unary operations: not x, -x
parseNumUna :: Parser Term
parseNumUna = label "numeric unary operation" $ do
  op <- choice
    [ try $ keyword "not" >> return NOT
    , try $ symbol "-" >> return NEG
    ]
  arg <- parseTerm
  return $ Op1 op arg

-- | Syntax: [term1, term2, term3]
parseLstLit :: Parser Term
parseLstLit = label "list literal" $ do
  _ <- try $ symbol "["
  terms <- sepEndBy parseTerm (symbol ",")
  _ <- symbol "]"
  return $ foldr Con Nil terms

-- | Syntax: return term
parseReturn :: Parser Term
parseReturn = label "return statement" $ do
  _ <- try $ keyword "return"
  t <- parseTerm
  return t

-- | Syntax: {==} | finally
parseRfl :: Parser Term
parseRfl = label "reflexivity ({==} or finally)" $ choice
  [ parseBraces
  , parseFinally
  ]
  where
    parseBraces = do
      _ <- try $ do
        _ <- symbol "{"
        _ <- symbol "=="
        return ()
      _ <- symbol "}"
      return Rfl
    
    parseFinally = do
      _ <- try $ keyword "finally"
      return Rfl

-- | Syntax: rewrite expr body
parseRewrite :: Parser Term
parseRewrite = label "rewrite" $ do
  _ <- try $ keyword "rewrite"
  e <- parseTerm
  f <- parseTerm
  return (Rwt e f)

-- | Syntax: absurd expr
-- Desugars to: match expr {}
parseAbsurd :: Parser Term
parseAbsurd = label "absurd" $ do
  _ <- try $ keyword "absurd"
  scrut <- parseTerm
  return (Pat [scrut] [] [])

-- | Syntax: (term1, term2) | (f arg1 arg2)
-- Disambiguates between tuples and applications
parseTupApp :: Parser Term
parseTupApp = do
  _ <- try $ symbol "("
  choice [ parseTup , parseApp ]

-- | Syntax: (function arg1 arg2 arg3)
parseApp :: Parser Term
parseApp = label "application" $ do
  f  <- parseTerm
  xs <- many parseTerm
  _ <- symbol ")"
  return (foldl App f xs)

-- | Syntax: function<arg1, arg2, arg3>
parsePol :: Term -> Parser Term
parsePol f = label "polymorphic application" $ try $ do
  _ <- try $ do
    _ <- symbol "<"
    notFollowedBy (char '>')
  args <- sepEndBy parseTerm (symbol ",")
  _    <- symbol ">"
  return $ foldl App f args

-- | Syntax: function(arg1, arg2, arg3)
parseCal :: Term -> Parser Term
parseCal f = label "function application" $ try $ do
  _    <- symbol "("
  args <- sepEndBy parseTerm (symbol ",")
  _    <- symbol ")"
  return $ foldl App f args

-- | trailing‐operator parsers

-- | Syntax: (term1, term2) | (term1, term2, term3)
parseTup :: Parser Term
parseTup = label "pair" $ try $ do
  terms <- try $ do
    first <- parseTerm
    _ <- symbol ","
    rest <- sepBy1 parseTerm (symbol ",")
    return (first : rest)
  _ <- symbol ")"
  case terms of
    []     -> fail "empty tuple"
    [x]    -> fail "single element tuple"
    xs     -> return $ foldr1 (\x acc -> Tup x acc) xs

-- | Syntax: head <> tail
parseCon :: Term -> Parser Term
parseCon t = label "list cons" $ do
  s <- get
  _ <- try $ symbol "<>"
  u <- parseTerm
  return (Con t u)

-- | Syntax: InputType -> OutputType
parseFun :: Term -> Parser Term
parseFun t = label "function type" $ do
  _ <- try $ symbol "->"
  u <- parseTerm
  return (All t (Lam "_" (Just t) (\_ -> u)))

-- | Syntax: Type1 & Type2
parseAnd :: Term -> Parser Term
parseAnd t = label "product type" $ do
  _ <- try $ symbol "&"
  u <- parseTerm
  return (Sig t (Lam "_" (Just t) (\_ -> u)))

-- | Syntax: term :: Type
parseChk :: Term -> Parser Term
parseChk x = label "type check" $ do
  _ <- try $ symbol "::"
  t <- parseTerm
  return $ (Chk x t)

-- | Syntax: ElementType[]
parseLst :: Term -> Parser Term
parseLst t = label "list type" $ do
  _ <- try $ symbol "[]"
  return (Lst t)

-- | Syntax: Type{term1 == term2} or Type{term1 != term2}
parseEql :: Term -> Parser Term
parseEql t = label "equality type" $ do
  _ <- try $ symbol "{"
  a <- parseTerm
  op <- choice
    [ symbol "==" >> return True
    , symbol "!=" >> return False
    ]
  b <- parseTerm
  _ <- symbol "}"
  let eql = Eql t a b
  return $ if op then eql else App (Ref "Not" 1) eql

-- | Parse numeric binary operations
parseNumOp :: Term -> Parser Term
parseNumOp lhs = label "numeric operation" $ do
  st <- get
  op <- choice $ concat
    [ guard (not (tight st)) >> 
      [ try $ symbol "<=" >> return LEQ
      , try $ symbol ">=" >> return GEQ
      , try $ symbol "<<" >> return SHL
      , try $ symbol ">>" >> return SHR
      , try $ symbol ">"  >> return GRT
      , try $ do
          _ <- symbol "<"
          notFollowedBy (char '>')
          return LST
      ]
    , [ try $ symbol "==="  >> return EQL
      , try $ symbol "!=="  >> return NEQ
      , try $ keyword "and" >> return AND
      , try $ keyword "or"  >> return OR
      , try $ keyword "xor" >> return XOR
      , try $ symbol "**"   >> return POW
      , try $ symbol "-"    >> return SUB
      , try $ symbol "*"    >> return MUL
      , try $ symbol "/"    >> return DIV
      , try $ symbol "%"    >> return MOD
      , try $ symbol "^"    >> return XOR
      ]
    ]
  rhs <- parseTerm
  return $ Op2 op lhs rhs

-- | Syntax: 3n + x (Nat successor) or x + y (numeric addition)
parseAdd :: Term -> Parser Term
parseAdd t = label "addition" $ do
  _ <- try $ symbol "+"
  b <- parseTerm
  case cut t of
    -- If LHS is a Nat literal, interpret as successor(s)
    n | isNatLit n -> return (applySuccessors (countSuccessors n) b)
    -- Otherwise, it's numeric addition
    _              -> return (Op2 ADD t b)
  where
    isNatLit :: Term -> Bool
    isNatLit Zer       = True
    isNatLit (Suc n)   = isNatLit n
    isNatLit (Loc _ t) = isNatLit t
    isNatLit _         = False
    
    -- Count number of successors
    countSuccessors :: Term -> Int
    countSuccessors Zer       = 0
    countSuccessors (Suc n)   = 1 + countSuccessors n
    countSuccessors (Loc _ t) = countSuccessors t
    countSuccessors _         = 0
    
    applySuccessors :: Int -> Term -> Term
    applySuccessors 0 t = t
    applySuccessors n t = Suc (applySuccessors (n-1) t)

-- | Syntax: var = value; body | pattern = value; body
-- Interprets as let if t is a variable, otherwise as pattern match
parseAss :: Term -> Parser Term
parseAss t = label "location binding" $ do
  mtyp <- try $ do
    mtyp <- optional $ do
      _ <- symbol ":"
      parseTermBefore "="
    _ <- symbol "="
    notFollowedBy (char '=')
    return mtyp
  -- Check for invalid assignment patterns after confirming it's an assignment
  case cut t of
    Bit     -> fail "Cannot assign a value to `Bool` native type"
    Nat     -> fail "Cannot assign a value to `Nat` native type"
    Set     -> fail "Cannot assign a value to `Set` native type"
    Emp     -> fail "Cannot assign a value to `Empty` native type"
    Uni     -> fail "Cannot assign a value to `Unit` native type"
    Bt0     -> fail "Cannot assign a value to `False` boolean literal"
    Bt1     -> fail "Cannot assign a value to `True` boolean literal"
    Zer     -> fail "Cannot assign a value to `0n` nat literal"
    Suc _   -> fail "Cannot assign a value to nat literal"
    Num nt  -> fail $ "Cannot assign a value to `" ++ show (Num nt) ++ "` numeric type"
    Val v   -> fail $ "Cannot assign a value to `" ++ show (Val v) ++ "` literal"
    One     -> fail "Cannot assign a value to `()` unit literal"
    Nil     -> fail "Cannot assign a value to `[]` list literal"
    Rfl     -> fail "Cannot assign a value to `{==}` reflexivity literal"
    Era     -> fail "Cannot assign a value to `*` eraser"
    Var x _ -> do
      v <- parseTerm
      _ <- parseSemi
      b <- expectBody "assignment" parseTerm
      return $ Let x mtyp v (\_ -> b)
    _       -> do
      v <- parseTerm
      _ <- parseSemi
      b <- expectBody "assignment" parseTerm
      return $ Pat [v] [] [([t], b)]

-- | HOAS‐style binders

-- | Syntax: λ x y z. body | lam x y z. body | λ (x,y) z. body
parseLam :: Parser Term
parseLam = label "lambda abstraction" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", keyword "lambda"]
    notFollowedBy (symbol "{")
    return ()
  -- Parse terms instead of just names to support patterns
  -- pats <- some parseTerm
  binders <- some $ do
    pat <- parseTermBefore ":"
    mtyp <- optional $ do
      _ <- symbol ":"
      parseTerm
    return (pat, mtyp)
  _  <- symbol "."
  body  <- parseTerm
  -- Desugar pattern lambdas
  return $ foldr desugarLamPat body (zip [0..] binders)
  where
    desugarLamPat :: (Int, (Term, Maybe Term)) -> Term -> Term
    desugarLamPat (_  , (cut -> (Var x _), mtyp)) acc = Lam x mtyp (\_ -> acc)
    desugarLamPat (idx, (pat,mtyp))               acc = 
      -- Generate a fresh variable name using index
      let freshVar = "_" ++ show idx
      in Lam freshVar mtyp (\_ -> Pat [Var freshVar 0] [] [([pat], acc)])

-- | Syntax: μ f. body
parseFix :: Parser Term
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  f <- parseTerm
  return (Fix k (\v -> f))

-- | Parse λ-match forms: λ{...}
parseLamMatch :: Parser Term
parseLamMatch = label "lambda match" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", keyword "lambda"]
    _ <- symbol "{"
    return ()
  -- Check for empty match first
  mb_close <- optional (lookAhead (symbol "}"))
  case mb_close of
    Just _ -> do
      _ <- symbol "}"
      return EmpM
    Nothing -> do
      term <- choice
        [ parseUniMForm
        , parseBitMForm
        , parseNatMForm
        , parseLstMForm
        , parseSigMForm
        , parseEnuMForm
        , parseSupMForm
        ]
      _ <- symbol "}"
      return term
  where
    -- λ{(): term}
    parseUniMForm = do
      _ <- try $ do
        _ <- symbol "()"
        _ <- symbol ":"
        return ()
      f <- parseTerm
      _ <- parseSemi
      return (UniM f)

    -- λ{False: term; True: term}
    parseBitMForm = do
      _ <- try $ do
        _ <- symbol "False"
        _ <- symbol ":"
        return ()
      f <- parseTerm
      _ <- parseSemi
      _ <- symbol "True"
      _ <- symbol ":"
      t <- parseTerm
      _ <- parseSemi
      return (BitM f t)

    -- λ{0n: term; 1n+: term}
    parseNatMForm = do
      _ <- try $ do
        _ <- symbol "0n"
        _ <- symbol ":"
        return ()
      z <- parseTerm
      _ <- parseSemi
      _ <- symbol "1n+"
      _ <- symbol ":"
      s <- parseTerm
      _ <- parseSemi
      return (NatM z s)

    -- λ{[]: term; <>: term}
    parseLstMForm = do
      _ <- try $ do
        _ <- symbol "[]"
        _ <- symbol ":"
        return ()
      n <- parseTerm
      _ <- parseSemi
      _ <- symbol "<>"
      _ <- symbol ":"
      c <- parseTerm
      _ <- parseSemi
      return (LstM n c)

    -- λ{(,): term}
    parseSigMForm = do
      _ <- try $ do
        _ <- symbol "(,)"
        _ <- symbol ":"
        return ()
      f <- parseTerm
      _ <- parseSemi
      return (SigM f)


    -- λ{&tag1: term1; &tag2: term2; ...; default}
    parseEnuMForm = do
      _ <- try (lookAhead (choice [symbol "@", symbol "&"]))
      cases <- many $ try $ do
        _ <- choice [symbol "@", symbol "&"]
        s <- some (satisfy isNameChar)
        _ <- symbol ":"
        t <- parseTerm
        _ <- parseSemi
        return (s, t)
      def <- option One $ try $ do
        notFollowedBy (symbol "}")
        notFollowedBy (symbol "@")
        notFollowedBy (symbol "&")
        term <- parseTerm
        _ <- parseSemi
        return term
      return (EnuM cases def)

    -- λ{&L{,}: term}
    parseSupMForm = do
      l <- try $ do
        _ <- symbol "&"
        l <- parseTermBefore "{"
        _ <- symbol "{"
        _ <- symbol ","
        _ <- symbol "}"
        _ <- symbol ":"
        return l
      f <- parseTerm
      _ <- parseSemi
      return (SupM l f)

-- | Syntax: ~{term} | ~term | ~ term { cases... }
parseTildeExpr :: Parser Term
parseTildeExpr = label "tilde expression (induction or match)" $ do
  _ <- try $ symbol "~"
  choice
    [ -- ~ term [{...}]
      do
        scrut <- parseTermBefore "{"
        is_match <- optional (lookAhead (symbol "{"))
        case is_match of
          Just _ -> do -- It's a match expression
            _ <- symbol "{"
            -- Check for empty pattern match first
            mb_close <- optional (lookAhead (symbol "}"))
            case mb_close of
              Just _ -> do
                _ <- symbol "}"
                return (App EmpM scrut)
              Nothing -> do
                term <- choice
                  [ parseUniMCases scrut
                  , parseBitMCases scrut
                  , parseNatMCases scrut
                  , parseLstMCases scrut
                  , parseSigMCases scrut
                  , parseEnuMCases scrut
                  , parseSupMCases scrut
                  ]
                _ <- symbol "}"
                return term
          Nothing -> fail "Expected match expression after ~"
    ]

-- Case parsers for expression-based matches
-- -----------------------------------------

-- | Syntax: (): term;
parseUniMCases :: Term -> Parser Term
parseUniMCases scrut = do
  _ <- try $ do
    _ <- symbol "()"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  return (App (UniM f) scrut)

-- | Syntax: False: term; True: term;
parseBitMCases :: Term -> Parser Term
parseBitMCases scrut = do
  _ <- try $ do
    _ <- symbol "False"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  _ <- symbol "True"
  _ <- symbol ":"
  t <- parseTerm
  _ <- parseSemi
  return (App (BitM f t) scrut)

-- | Syntax: 0n: term; 1n+: term;
parseNatMCases :: Term -> Parser Term
parseNatMCases scrut = do
  _ <- try $ do
    _ <- symbol "0n"
    _ <- symbol ":"
    return ()
  z <- parseTerm
  _ <- parseSemi
  _ <- symbol "1n+"
  _ <- symbol ":"
  s <- parseTerm
  _ <- parseSemi
  return (App (NatM z s) scrut)

-- | Syntax: []: term; <>: term;
parseLstMCases :: Term -> Parser Term
parseLstMCases scrut = do
  _ <- try $ do
    _ <- symbol "[]"
    _ <- symbol ":"
    return ()
  n <- parseTerm
  _ <- parseSemi
  _ <- symbol "<>"
  _ <- symbol ":"
  c <- parseTerm
  _ <- parseSemi
  return (App (LstM n c) scrut)

-- | Syntax: (,): term;
parseSigMCases :: Term -> Parser Term
parseSigMCases scrut = do
  _ <- try $ do
    _ <- symbol "(,)"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  return (App (SigM f) scrut)


-- | Syntax: &tag1: term1; &tag2: term2; ...; default; (also accepts @tag for compatibility)
parseEnuMCases :: Term -> Parser Term
parseEnuMCases scrut = do
  _ <- try (lookAhead (choice [symbol "@", symbol "&"]))
  cases <- many $ try $ do
    _ <- choice [symbol "@", symbol "&"]
    s <- some (satisfy isNameChar)
    _ <- symbol ":"
    t <- parseTerm
    _ <- parseSemi
    return (s, t)
  def <- option One $ try $ do
    notFollowedBy (symbol "}")
    notFollowedBy (symbol "@")
    notFollowedBy (symbol "&")
    term <- parseTerm
    _ <- parseSemi
    return term
  return (App (EnuM cases def) scrut)

-- | Syntax: &L{,}: term;
parseSupMCases :: Term -> Parser Term
parseSupMCases scrut = do
  l <- try $ do
    _ <- symbol "&"
    l <- parseTermBefore "{"
    _ <- symbol "{"
    _ <- symbol ","
    _ <- symbol "}"
    _ <- symbol ":"
    return l
  f <- parseTerm
  _ <- parseSemi
  return (App (SupM l f) scrut)

-- | Main entry points

-- | Parse a term from a string, returning an error message on failure
doParseTerm :: FilePath -> String -> Either String Term
doParseTerm file input =
  case evalState (runParserT p file input) (ParserState True input [] M.empty [] 0 file) of
    Left err  -> Left (formatError input err)
    Right res -> Right (adjust (Book M.empty []) res)
  where
    p = do
      skip
      t <- parseTerm
      skip
      eof
      return t

-- | Parse a term from a string, crashing on failure
doReadTerm :: String -> Term
doReadTerm input =
  case doParseTerm "<input>" input of
    Left err  -> error err
    Right res -> res
