module Target.HVM.Parse
  ( parseGeneratedTerms
  ) where

import Target.HVM.HVM (HCore(..))

import Control.Applicative (empty, (<|>))
import Data.Functor (($>))
import Data.List (foldl')
import Data.Void (Void)
import Text.Megaparsec
  ( Parsec
  , between
  , choice
  , eof
  , many
  , optional
  , runParser
  , sepBy
  , sepBy1
  , try
  , errorBundlePretty
  )
import Text.Megaparsec.Char
  ( alphaNumChar
  , char
  , letterChar
  , space1
  , string
  )
import qualified Text.Megaparsec.Char.Lexer as L

-------------------------------------------------------------------------------
-- Public API
-------------------------------------------------------------------------------

parseGeneratedTerms :: String -> Either String [HCore]
parseGeneratedTerms input =
  case runParser (sc *> generatedP <* eof) "<hvm4>" input of
    Left err  -> Left (errorBundlePretty err)
    Right res -> Right res

-------------------------------------------------------------------------------
-- Parser basics
-------------------------------------------------------------------------------

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "//") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

identifier :: Parser String
identifier = lexeme $ do
  start <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_' <|> char '\'')
  pure (start : rest)

-------------------------------------------------------------------------------
-- Terms
-------------------------------------------------------------------------------

termP :: Parser HCore
termP = choice
  [ try matchLamP
  , try rewriteP
  , lambdaP
  , consExprP
  ]

generatedP :: Parser [HCore]
generatedP = listP <|> fmap pure termP
  where
    listP = do
      _ <- symbol "["
      terms <- termP `sepBy` symbol ","
      _ <- symbol "]"
      pure terms

lambdaP :: Parser HCore
lambdaP = do
  _ <- symbol "λ"
  name <- identifier
  _ <- symbol "."
  body <- termP
  pure (HLam name body)

matchLamP :: Parser HCore
matchLamP = try $ do
  _ <- symbol "λ"
  _ <- symbol "{"
  branches <- branchP `sepBy1` symbol ";"
  _ <- symbol "}"
  case branches of
    [] -> pure HErf
    [(PatUnit, body)]       -> pure (HUse body)
    [(PatPair, body)]       -> pure (HGet body)
    [(PatZero, z), (PatSucc, s)] -> pure (HNif z s)
    [(PatNil, n), (PatCons, c)]  -> pure (HMat n c)
    [(PatFalse, f), (PatTrue, t)] -> pure (HBif f t)
    [(PatUZero, z), (PatUSucc, s)] -> pure (HUif z s)
    _  -> fail "unsupported match lambda shape"

rewriteP :: Parser HCore
rewriteP = do
  _ <- symbol "~"
  evidence <- rewriteAtom
  _ <- symbol ":"
  proof <- rewriteAtom
  _ <- symbol ";"
  body <- termP
  pure (HRwt evidence proof body)
  where
    rewriteAtom = parens termP <|> atomP

consExprP :: Parser HCore
consExprP = do
  headTerm <- appTermP
  rest <- many (symbol "<>" *> appTermP)
  pure (foldl' HCon headTerm rest)

appTermP :: Parser HCore
appTermP = atomP

-------------------------------------------------------------------------------
-- Atoms and suffixes
-------------------------------------------------------------------------------

atomP :: Parser HCore
atomP = do
  base <- atomPrimaryP
  extend base
  where
    extend term = do
      next <- optional (choice [try callSuffix, try listSuffix, equalitySuffix])
      case next of
        Nothing -> pure term
        Just f  -> extend (f term)

    callSuffix = do
      args <- between (symbol "(") (symbol ")") (termP `sepBy1` symbol ",")
      pure (\fn -> foldl' HApp fn args)

    listSuffix = symbol "[]" $> (\t -> HLst t)

    equalitySuffix = do
      _ <- symbol "{"
      lhs <- termP
      _ <- symbol "=="
      rhs <- termP
      _ <- symbol "}"
      pure (\typ -> HEql typ lhs rhs)

atomPrimaryP :: Parser HCore
atomPrimaryP = choice
  [ parens termP
  , tupleP
  , listLiteralP
  , unitTermP
  , boolTermP
  , try natSuccP
  , natLiteralP
  , try u32LiteralP
  , incTermP
  , refP
  , typeRefP
  , setP
  , natTypeP
  , boolTypeP
  , pairTypeP
  , u32TypeP
  , rflTermP
  , zeroTermP
  , nilTermP
  , varP
  ]

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

tupleP :: Parser HCore
tupleP = do
  _ <- symbol "#("
  a <- termP
  _ <- symbol ","
  b <- termP
  _ <- symbol ")"
  pure (HTup a b)

listLiteralP :: Parser HCore
listLiteralP = do
  _ <- symbol "["
  elems <- termP `sepBy` symbol ","
  _ <- symbol "]"
  pure (foldr HCon HNil elems)

unitTermP :: Parser HCore
unitTermP = symbol "()" $> HNull

boolTermP :: Parser HCore
boolTermP = choice
  [ symbol "#0" $> HBt0
  , symbol "#1" $> HBt1
  ]

natSuccP :: Parser HCore
natSuccP = do
  n <- lexeme L.decimal
  _ <- symbol "n+"
  body <- atomP
  pure (iterate HSuc body !! n)

natLiteralP :: Parser HCore
natLiteralP = do
  n <- lexeme L.decimal
  _ <- symbol "n"
  pure (buildNat n)

u32LiteralP :: Parser HCore
u32LiteralP = do
  n <- lexeme (L.decimal :: Parser Integer)
  pure (HUva (fromIntegral n))

buildNat :: Int -> HCore
buildNat n = iterate HSuc HZer !! n

incTermP :: Parser HCore
incTermP = do
  _ <- symbol "↑"
  body <- atomP
  pure (HInc body)

refP :: Parser HCore
refP = do
  _ <- char '@'
  name <- identifier
  pure (HRef name)

typeRefP :: Parser HCore
typeRefP = do
  _ <- string "@:"
  name <- identifier
  pure (HTyp name)

setP :: Parser HCore
setP = symbol "*" $> HSet

natTypeP :: Parser HCore
natTypeP = symbol "ℕ" $> HNat

boolTypeP :: Parser HCore
boolTypeP = symbol "𝔹" $> HBit

pairTypeP :: Parser HCore
pairTypeP = do
  _ <- symbol "Σ"
  t1 <- atomP
  _ <- symbol "."
  t2 <- atomP
  pure (HSig t1 t2)

u32TypeP :: Parser HCore
u32TypeP = symbol "U32" $> HU32

rflTermP :: Parser HCore
rflTermP = symbol "{==}" $> HRfl

zeroTermP :: Parser HCore
zeroTermP = symbol "0n" $> HZer

nilTermP :: Parser HCore
nilTermP = symbol "[]" $> HNil

varP :: Parser HCore
varP = do
  name <- identifier
  sub <- optional (char '₀' <|> char '₁')
  pure $ case sub of
    Just '₀' -> HDP0 "" name
    Just '₁' -> HDP1 "" name
    _        -> HVar name

-------------------------------------------------------------------------------
-- Match branches
-------------------------------------------------------------------------------

data Pattern
  = PatZero
  | PatSucc
  | PatNil
  | PatCons
  | PatFalse
  | PatTrue
  | PatPair
  | PatUnit
  | PatUZero
  | PatUSucc

branchP :: Parser (Pattern, HCore)
branchP = do
  pat <- patternP
  _ <- symbol ":"
  body <- termP
  pure (pat, body)

patternP :: Parser Pattern
patternP = choice
  [ symbol "0n" $> PatZero
  , symbol "1n+" $> PatSucc
  , symbol "[]" $> PatNil
  , symbol "<>" $> PatCons
  , symbol "#0" $> PatFalse
  , symbol "#1" $> PatTrue
  , symbol "#(,)" $> PatPair
  , symbol "()" $> PatUnit
  , symbol "0" $> PatUZero
  , symbol "1+" $> PatUSucc
  ]
