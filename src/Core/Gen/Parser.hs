module Core.Gen.Parser
  ( parseGeneratedTerms
  ) where

import Core.Parse.Term (doParseTerm)
import Core.Type

import Data.Char (isSpace)
import Data.List (dropWhileEnd)

parseGeneratedTerms :: String -> Either String [Term]
parseGeneratedTerms output =
  traverse parseOne (filter (not . null) (map cleanupTerm (lines output)))
  where
    parseOne txt =
      case doParseTerm "<generated>" txt of
        Left err  -> Left $ "Failed to parse generated term: " ++ err
        Right term -> Right term

    cleanupTerm = trimTrailingSemicolon . trimSpaces

    trimSpaces = dropWhile isSpace . dropWhileEnd isSpace

    trimTrailingSemicolon s =
      let stripped = dropWhileEnd isSpace s
      in if not (null stripped) && last stripped == ';'
           then dropWhileEnd isSpace (init stripped)
           else stripped
