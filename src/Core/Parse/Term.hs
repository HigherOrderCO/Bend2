{-./../Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Parse.Term 
  ( parseTerm
  , parseExpr
  , doParseTerm
  , doReadTerm
  ) where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit)
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

import Core.Adjust
import Core.Parse
import Core.Type

-- | Parse a "core" form
parseTermIni :: Parser Term
parseTermIni = choice
  [ parseLet
  , parseGen
  , parseTst
  , parseFix
  , parseLam
  , parseBifIf
  , parsePat
  , parseRewrite
  , parseAbsurd
  , parseAll
  , parseSig
  , parseTildeExpr
  , parseOne
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

-- | Parses a core term and a tight posfix (no operators)
parseExpr :: Parser Term
parseExpr = do
  ini <- parseTermIni
  val <- parseTermArg ini
  return $ val

-- | Top‐level entry point
parseTerm :: Parser Term
parseTerm = located $ do
  exp <- parseExpr
  val <- parseTermOpr exp
  return val

-- atomic terms

-- | Syntax: x, foo, bar_123, Type<A,B>, Nat/add
parseVar :: Parser Term
parseVar = label "variable" $ do
  n <- name
  case n of
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
    _             -> return $ Var n 0


-- | Syntax: ()
parseOne :: Parser Term
parseOne = label "unit value (())" $ symbol "()" >> return One

-- | Syntax: if condition: trueCase else: falseCase
parseBifIf :: Parser Term
parseBifIf = label "if clause" $ do
  _ <- try $ symbol "if"
  condition <- parseTerm
  _ <- symbol ":"
  trueCase <- parseTerm
  _ <- symbol "else"
  _ <- symbol ":"
  falseCase <- parseTerm
  return $ BitM condition falseCase trueCase

-- | Syntax: Σ x: Type. body | any x: Type. body | Σ Type. Type | any Type. Type
parseSig :: Parser Term
parseSig = label "dependent pair type" $ do
  _ <- try $ choice [symbol "Σ", symbol "any"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseSigSimple
    _  -> do
      _ <- symbol "."
      b <- parseExpr
      return $ foldr (\(x, t) acc -> Sig t (Lam x (\v -> acc))) b bindings
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
  b <- parseExpr
  return (Sig a b)

-- | Syntax: ∀ x: Type. body | all x: Type. body | ∀ Type. Type | all Type. Type
parseAll :: Parser Term
parseAll = label "dependent function type" $ do
  _ <- try $ choice [symbol "∀", symbol "all"]
  bindings <- many parseBinding
  case bindings of
    [] -> parseAllSimple
    _  -> do
      _ <- symbol "."
      b <- parseExpr
      return $ foldr (\(x, t) acc -> All t (Lam x (\v -> acc))) b bindings
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
  b <- parseExpr
  return (All a b)

-- Enum Type Parsers
-- -----------------

-- | Syntax: &{tag1, tag2, tag3}
parseEnu :: Parser Term
parseEnu = label "enum type" $ do
  _ <- try $ symbol "&{"
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
    -- Parse @tag{...} constructor syntax (unchanged)
    parseConstructor = try $ do
      _ <- symbol "@"
      n <- some (satisfy isNameChar)
      _ <- symbol "{"
      f <- sepEndBy parseTerm (symbol ",")
      _ <- symbol "}"
      return $ buildCtor n f
    
    -- Parse new &tag bare symbol syntax  
    parseNewSymbol = try $ do
      _ <- char '&'
      notFollowedBy (char '{')  -- make sure we are not &{...} enum type
      n <- some (satisfy isNameChar)
      skip
      return $ Sym n
    
    -- Parse old @tag bare symbol syntax and desugar to (&tag,())
    parseOldSymbol = try $ do
      _ <- symbol "@"
      notFollowedBy (char '{')  -- make sure we are not @{...} or @tag{...}
      n <- lexeme $ some (satisfy isNameChar)
      -- Desugar @Foo to (&Foo,())
      return $ Tup (Sym n) One
    
    buildCtor :: String -> [Term] -> Term
    buildCtor tag fs =
      let tup = foldr Tup One fs       -- Build (f1,(f2,(...,()))
      in  Tup (Sym tag) tup            -- (&Tag,(f1,(f2,(...,()))))

-- | Syntax: match expr: case pat: body | match expr { case pat: body }
parsePat :: Parser Term
parsePat = label "pattern match" $ do
  srcPos  <- getSourcePos
  _       <- symbol "match"
  scruts  <- some parseTerm
  delim   <- choice [ ':' <$ symbol ":", '{' <$ symbol "{" ]
  moves   <- many parseWith
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
    parseWith = try $ do
      _ <- symbol "with"
      x <- name
      v <- option (Var x 0) (try (symbol "=" >> parseTerm))
      return (x, v)

-- | Syntax: case pattern1 pattern2: body
-- Indentation-sensitive clause list (stops when out-dented)
parseIndentClauses :: Int -> Int -> Parser [Case]
parseIndentClauses col arity = many clause where

    clause = label "case clause" . try $ do
      skip                               -- eat leading ws / newlines
      pos  <- getSourcePos
      guard (unPos (sourceColumn pos) >= col)
      _    <- symbol "case"
      pats <- replicateM arity parseTerm
      _    <- symbol ":"
      body <- parseTerm
      pure (pats, body)

-- | Syntax: case pattern1 pattern2: body
-- Braced clause list (runs until the closing '}')
parseBraceClauses :: Int -> Parser [Case]
parseBraceClauses arity = manyTill singleClause (lookAhead (symbol "}")) where
  singleClause = label "case clause" $ do
    _    <- symbol "case"
    pats <- replicateM arity parseTerm
    _    <- symbol ":"
    body <- parseTerm
    pure (pats, body)

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

-- | Parse numeric unary operations: !x, -x
parseNumUna :: Parser Term
parseNumUna = label "numeric unary operation" $ do
  op <- choice
    [ try $ symbol "!" >> return NOT
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
  _ <- try $ symbol "return"
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
      _ <- symbol "finally"
      return Rfl

-- | Syntax: rewrite expr body
-- Desugars to: match expr: case {==}: body
parseRewrite :: Parser Term
parseRewrite = label "rewrite" $ do
  srcPos <- getSourcePos
  _ <- symbol "rewrite"
  scrut <- parseTerm
  body <- parseTerm
  return (Pat [scrut] [] [([Rfl], body)])

-- | Syntax: absurd expr
-- Desugars to: match expr {}
parseAbsurd :: Parser Term
parseAbsurd = label "absurd" $ do
  _ <- symbol "absurd"
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
  _    <- symbol "<"
  args <- sepEndBy parseExpr (symbol ",")
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
  guard (not (tight s))
  _ <- try $ symbol "<>"
  u <- parseTerm
  return (Con t u)

-- | Syntax: InputType -> OutputType
parseFun :: Term -> Parser Term
parseFun t = label "function type" $ do
  _ <- try $ symbol "->"
  u <- parseTerm
  return (All t (Lam "_" (\_ -> u)))

-- | Syntax: Type1 & Type2
parseAnd :: Term -> Parser Term
parseAnd t = label "product type" $ do
  _ <- try $ symbol "&"
  notFollowedBy (satisfy isNameChar)
  u <- parseTerm
  return (Sig t (Lam "_" (\_ -> u)))

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
  a <- parseExpr
  op <- choice
    [ symbol "==" >> return True
    , symbol "!=" >> return False
    ]
  b <- parseExpr
  _ <- symbol "}"
  let eql = Eql t a b
  return $ if op then eql else App (Ref "Not") eql

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
      , try $ symbol "<"  >> return LST
      , try $ symbol ">"  >> return GRT
      ]
    , [ try $ symbol "===" >> return EQL
      , try $ symbol "!=" >> return NEQ
      , try $ symbol "&&" >> return AND
      , try $ symbol "||" >> return OR
      , try $ symbol "**" >> return POW
      , try $ symbol "-"  >> return SUB
      , try $ symbol "*"  >> return MUL
      , try $ symbol "/"  >> return DIV
      , try $ symbol "%"  >> return MOD
      , try $ symbol "^"  >> return XOR
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
  _ <- try $ do
    _ <- symbol "="
    notFollowedBy (char '=')
  v <- parseTerm
  _ <- parseSemi
  b <- parseTerm
  case t of
    Var x _ -> return $ Let v (Lam x (\_ -> b))
    _       -> return $ Pat [v] [] [([t], b)]

-- | HOAS‐style binders

-- | Syntax: λ x y z. body | lam x y z. body | λ (x,y) z. body
parseLam :: Parser Term
parseLam = label "lambda abstraction" $ do
  _ <- try $ do
    _ <- choice [symbol "λ", symbol "lambda"]
    notFollowedBy (symbol "{")
    return ()
  -- Parse terms instead of just names to support patterns
  pats <- some parseTerm
  _  <- symbol "."
  body  <- parseTerm
  -- Desugar pattern lambdas
  return $ foldr desugarLamPat body (zip [0..] pats)
  where
    desugarLamPat :: (Int, Term) -> Term -> Term
    desugarLamPat (_  , cut -> (Var x _)) acc = Lam x (\_ -> acc)
    desugarLamPat (idx, pat)              acc = 
      -- Generate a fresh variable name using index
      let freshVar = "_" ++ show idx
      in Lam freshVar (\_ -> Pat [Var freshVar 0] [] [([pat], acc)])

-- | Syntax: μ f. body
parseFix :: Parser Term
parseFix = label "fixed point" $ do
  _ <- try $ symbol "μ"
  k <- name
  _ <- symbol "."
  f <- parseTerm
  return (Fix k (\v -> f))

-- | Syntax: let x = value; body | let x : Type = value; body
parseLet :: Parser Term
parseLet = label "let binding" $ do
  _ <- try $ symbol "let"
  x <- name
  choice [ parseLetTyped x , parseLetUntyped x ]

-- | Syntax: = value; body
-- Parses the untyped part of a 'let' binding
parseLetUntyped :: Name -> Parser Term
parseLetUntyped x = do
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let v (Lam x (\_ -> f)))

-- | Syntax: : Type = value; body
-- Parses the typed part of a 'let' binding
parseLetTyped :: Name -> Parser Term
parseLetTyped x = do
  _ <- try $ symbol ":"
  t <- parseTerm
  _ <- symbol "="
  v <- parseTerm
  _ <- parseSemi
  f <- parseTerm
  return $ (Let (Chk v t) (Lam x (\_ -> f)))

-- | Syntax: gen name(x: Type1, y: Type2) -> RetType { context } body
parseGen :: Parser Term
parseGen = label "generation" $ do
  _    <- try $ symbol "gen"
  f    <- name
  args <- parens $ sepEndBy parseArg (symbol ",")
  _    <- symbol "->"
  retT <- parseTerm
  ctx  <- option [] parseContext
  body <- parseTerm
  let metT = foldr nestType retT args
  return $ Let (Chk (Met 1 metT ctx) metT) (Lam f (\_ -> body))
  where
    parseArg = (,) <$> name <*> (symbol ":" *> parseTerm)
    nestType (argName, argType) currType = All argType $ Lam argName (\v -> currType)

-- | Syntax: test term1 == term2 : Type ...
parseTst :: Parser Term
parseTst = label "test statement" $ do
  _ <- try $ symbol "test"
  a <- parseTerm
  _ <- symbol "=="
  b <- parseTerm
  skip -- FIXME: do NOT use skip outside of 'lexeme'
  _ <- symbol ":"
  t <- parseTerm
  skip
  nxt <- choice [ parseEnd , parseTst ]
  return (Let (Eql t a b) (Lam "_" (\_ -> nxt)))

-- | Syntax: end term
parseEnd :: Parser Term
parseEnd = label "end gen statement" $ do
  _ <- try $ symbol "end"
  c <- parseTerm
  return c

-- | Syntax: ~{term} | ~term | ~ term { cases... }
parseTildeExpr :: Parser Term
parseTildeExpr = label "tilde expression (induction or match)" $ do
  _ <- try $ symbol "~"
  choice
    [ -- ~{term}
      try $ do
        _ <- symbol "{"
        t <- parseTerm
        _ <- symbol "}"
        return (Ind t)
    , -- ~ term [{...}]
      do
        scrut <- parseExpr
        is_match <- optional (lookAhead (symbol "{"))
        case is_match of
          Just _ -> do -- It's a match expression
            _ <- symbol "{"
            -- Check for empty pattern match first
            mb_close <- optional (lookAhead (symbol "}"))
            case mb_close of
              Just _ -> do
                _ <- symbol "}"
                return (EmpM scrut)
              Nothing -> do
                term <- choice
                  [ parseUniMCases scrut
                  , parseBitMCases scrut
                  , parseNatMCases scrut
                  , parseLstMCases scrut
                  , parseSigMCases scrut
                  , parseEqlMCases scrut
                  , parseEnuMCases scrut
                  ]
                _ <- symbol "}"
                return term
          Nothing -> return (Ind scrut) -- It's an Ind expression
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
  return (UniM scrut f)

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
  return (BitM scrut f t)

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
  return (NatM scrut z s)

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
  return (LstM scrut n c)

-- | Syntax: (,): term;
parseSigMCases :: Term -> Parser Term
parseSigMCases scrut = do
  _ <- try $ do
    _ <- symbol "(,)"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  return (SigM scrut f)

-- | Syntax: {==}: term;
parseEqlMCases :: Term -> Parser Term
parseEqlMCases scrut = do
  _ <- try $ do
    _ <- symbol "{"
    _ <- symbol "=="
    _ <- symbol "}"
    _ <- symbol ":"
    return ()
  f <- parseTerm
  _ <- parseSemi
  return (EqlM scrut f)

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
  return (EnuM scrut cases def)

-- | Syntax: {term1, term2, term3}
-- Helper for parsing context in gen statements
parseContext :: Parser [Term]
parseContext = braces $ sepEndBy parseTerm (symbol ",")

-- | Main entry points

-- | Parse a term from a string, returning an error message on failure
doParseTerm :: FilePath -> String -> Either String Term
doParseTerm file input =
  case evalState (runParserT p file input) (ParserState True input M.empty) of
    Left err  -> Left (formatError input err)
    Right res -> Right (adjust (Book M.empty) res)
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
    
