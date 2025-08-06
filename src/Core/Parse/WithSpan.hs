{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

-- -- This is a contrived solution to extract the withSpan function into its own module.
-- -- FIXME: Simplify this module structure when a better approach is found.

module Core.Parse.WithSpan where

import Control.Monad.State.Strict (MonadState, get)
import Data.Char (isSpace)
import Data.Void
import Text.Megaparsec
import qualified Data.Vector as V

import Core.Type (Span(..))

-- | Location tracking helpers
-- This uses a polymorphic approach to avoid importing Parser/ParserState from Core.Parse
withSpan :: forall s m a. (MonadParsec Void String m, MonadState s m) 
         => (s -> String)  -- ^ Extract source from state
         -> m a -> m (Span, a)
withSpan getSource p = do
  -- Record the starting position and absolute offset *before* running the
  -- parser.  The offset is necessary because the location returned by
  -- @getSourcePos@ after the parser has finished may already include trailing
  -- whitespace and comments that @lexeme@ consumed.  We want error spans to
  -- cover only the syntactic construct itself, so we post-process the end
  -- offset to drop such trivia.
  begPos    <- getSourcePos
  begOff    <- getOffset
  x         <- p
  endPosRaw <- getSourcePos  -- position *after* trailing space/comment
  endOffRaw <- getOffset
  st        <- get

  let src = getSource st
      pth = sourceName begPos
      -- Convert to Vector for O(1) indexing
      srcVec = V.fromList src

      -- | Skip backwards over whitespace and line comments.  We treat any line
      -- starting with a hash ("# …") as a comment.  The returned offset is the
      -- first position *after* the last non-trivia character (i.e. still
      -- exclusive).
      -- | Compute the new (exclusive) end offset by removing any
      -- trailing
      --   • whitespace (spaces, tabs, new-lines, …)
      --   • whole line comments that start with '#'
      --
      -- The algorithm walks backwards from the original end offset until it
      -- finds the last non-trivia character.  For line comments we must drop
      -- the entire line, not just the hash symbol itself.
      -- Optimized trimEnd using Vector for O(1) access
      trimEnd :: Int -> Int -> Int
      trimEnd b e = step (e - 1)
        where
          -- Walk backwards while we are in whitespace or a comment line.
          step i
            | i < b              = b                    -- fell past start
            | isSpace (srcVec V.! i) = step (i - 1)     -- skip whitespace  
            | isInCommentLine i  = step (startOfLine i - 1) -- skip comment line
            | otherwise          = i + 1                -- exclusive end

          -- Detect if the character at position @i@ lies within a line whose
          -- first non-space character is '#'.  Such a line is considered a
          -- (single-line) comment in Bend.
          isInCommentLine :: Int -> Bool
          isInCommentLine i =
            case firstNonSpace (startOfLine i) of
              Just '#' -> True
              _        -> False
            where
              -- Return the first non-space character between indices @s@ and
              -- the end of the current line (inclusive).  If the line is
              -- empty or contains only spaces it returns @Nothing@.
              firstNonSpace :: Int -> Maybe Char
              firstNonSpace j
                | j >= V.length srcVec   = Nothing
                | srcVec V.! j == '\n'   = Nothing
                | isSpace (srcVec V.! j) = firstNonSpace (j + 1)
                | otherwise              = Just (srcVec V.! j)

          -- Find the index of the first character of the current line that
          -- contains index @i@.
          startOfLine :: Int -> Int
          startOfLine j
            | j <= 0                     = 0
            | srcVec V.! (j - 1) == '\n' = j
            | otherwise                  = startOfLine (j - 1)

      trimmedEndOff = trimEnd begOff endOffRaw

      -- Convert absolute index back to a (line, column) pair (both 1-based).
      indexToPos :: String -> Int -> (Int, Int)
      indexToPos s target = go 0 1 1 s
        where
          go idx line col [] = (line, col)
          go idx line col (c:cs)
            | idx == target = (line, col)
            | otherwise =
                let (line', col') = if c == '\n' then (line + 1, 1)
                                     else (line, col + 1)
                in go (idx + 1) line' col' cs

      (begLine, begCol) = (unPos (sourceLine begPos), unPos (sourceColumn begPos))
      (endLine, endCol) = indexToPos src trimmedEndOff

  return (Span (begLine, begCol) (endLine, endCol) pth src, x)
