{-# LANGUAGE FlexibleContexts #-}

module Core.Parse
  ( -- * Types
    Parser
  , ParserState(..)

  -- * Basic parsers
  , skip
  , lexeme
  , lexemeNoSpace
  , symbol
  , parens
  , angles
  , braces
  , brackets
  , name
  , reserved
  , parseSemi

  -- * Character predicates
  , isNameInit
  , isNameChar

  -- * Name parsing helpers
  , parseRawName
  , checkReserved
  , resolveImports
  , applyImportMappings

  -- * Location tracking
  , withSpan
  , located

  -- * Error formatting
  , formatError
  ) where

import Control.Monad (when, replicateM, void, guard)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Char (isAsciiLower, isAsciiUpper, isDigit, isSpace)
import Data.Void
import Debug.Trace
import Highlight (highlightError)
import Text.Megaparsec
import Text.Megaparsec (anySingle, manyTill, lookAhead)
import Text.Megaparsec.Char
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set        as S
import qualified Text.Megaparsec.Char.Lexer as L

import Core.Bind
import Core.Flatten
import Core.Type

-- Parser state
data ParserState = ParserState
  { tight  :: Bool                   -- ^ tracks whether previous token ended with no trailing space
  , source :: String                 -- ^ original file source, for error reporting
  , imports :: M.Map String String   -- ^ import mappings: "Lib/" => "Path/To/Lib/"
  }

type Parser = ParsecT Void String (Control.Monad.State.Strict.State ParserState)

-- | Skip spaces and comments
skip :: Parser ()
skip = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "{-" "-}")

-- | Lexeme that consumes trailing whitespace and tracks tightness
lexeme :: Parser a -> Parser a
lexeme p = do
  skip
  x  <- p
  o1 <- getOffset
  skip
  o2 <- getOffset
  st <- get
  put st { tight = o1 == o2 }
  pure x

-- | Lexeme that doesn't consume trailing whitespace (precise spans)
lexemeNoSpace :: Parser a -> Parser a
lexemeNoSpace p = do
  skip  -- Still consume leading whitespace
  p     -- But don't consume trailing

symbol :: String -> Parser String
symbol s = lexeme (string s)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

isNameInit :: Char -> Bool
isNameInit c = isAsciiLower c || isAsciiUpper c || c == '_'

isNameChar :: Char -> Bool
isNameChar c = isAsciiLower c || isAsciiUpper c || isDigit c || c == '_' || c == '/'

reserved :: [Name]
reserved = ["match","case","else","if","end","all","any","finally","import","as"]

-- | Parse a raw name without import resolution
parseRawName :: Parser Name
parseRawName = do
  h <- satisfy isNameInit <?> "letter or underscore"
  t <- many (satisfy isNameChar <?> "letter, digit, or underscore")
  return (h : t)

-- | Check if a name is reserved
checkReserved :: Name -> Parser ()
checkReserved n = when (n `elem` reserved) $
  fail ("reserved keyword '" ++ n ++ "'")

-- | Apply import mappings to a name
resolveImports :: Name -> Parser Name
resolveImports n = do
  st <- get
  return $ applyImportMappings (imports st) n

-- | Apply all import mappings to a name
applyImportMappings :: M.Map String String -> Name -> Name
applyImportMappings mappings n
  = foldr tryApplyMapping n (M.toList mappings) where
    tryApplyMapping :: (String, String) -> String -> String
    tryApplyMapping (prefix, replacement) name =
      if take (length prefix) name == prefix
      then replacement ++ drop (length prefix) name
      else name

-- | Parse a name with import resolution
name :: Parser Name
name = lexeme $ do
  n <- parseRawName
  checkReserved n
  resolveImports n

-- Parses an Optional semicolon
parseSemi :: Parser ()
parseSemi = optional (symbol ";") >> return ()

-- | Clean withSpan impl using lexemeNoSpace
withSpan :: Parser a -> Parser (Span, a)
withSpan p = do
  begPos <- getSourcePos
  x      <- lexemeNoSpace p
  endPos <- getSourcePos
  st     <- get
  
  let begLine = unPos (sourceLine begPos)
      begCol  = unPos (sourceColumn begPos)
      endLine = unPos (sourceLine endPos)
      endCol  = unPos (sourceColumn endPos)
      src     = source st
  
  return (Span (begLine, begCol) (endLine, endCol) src, x)

located :: Parser Term -> Parser Term
located p = do
  (sp, t) <- withSpan p
  return (Loc sp t)

formatError :: String -> ParseErrorBundle String Void -> String
formatError input bundle = do
  let errorPos = NE.head $ fst $ attachSourcePos errorOffset (bundleErrors bundle) (bundlePosState bundle)
  let err = fst errorPos
  let pos = snd errorPos
  let lin = unPos $ sourceLine pos
  let col = unPos $ sourceColumn pos
  let msg = parseErrorTextPretty err
  let highlighted = highlightError (lin, col) (lin, col+1) input
  "\nPARSE_ERROR\n" ++ msg
    ++ "\nAt line " ++ show lin ++ ", column " ++ show col ++ ":\n"
    ++ highlighted
