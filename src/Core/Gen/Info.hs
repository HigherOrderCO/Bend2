module Core.Gen.Info
  ( GenInfo(..)
  , collectGenInfos
  , extractSimpleName
  ) where

import Core.Type

import qualified Data.Map as M
import Data.List (isPrefixOf)
import Data.Maybe (mapMaybe)

data GenInfo = GenInfo
  { giFullName   :: Name
  , giSimpleName :: String
  , giSpan       :: Span
  , giMetTerm    :: Term
  , giType       :: Type
  , giCtxTerms   :: [Term]
  }

collectGenInfos :: FilePath -> Book -> [GenInfo]
collectGenInfos file (Book defs names) =
  mapMaybe lookupGen names
  where
    lookupGen name = do
      (_, term, typ) <- M.lookup name defs
      case term of
        Loc sp inner
          | spanPth sp == file ->
              case stripLoc inner of
                met@(Met _ metType metCtx) ->
                  let simple = extractSimpleName name
                  in Just (GenInfo name simple sp met metType metCtx)
                _ -> Nothing
        _ -> Nothing

    stripLoc t = case t of
      Loc _ inner -> stripLoc inner
      other       -> other

extractSimpleName :: Name -> String
extractSimpleName name =
  case reverse (splitOnSep "::" name) of
    (simple:_) -> simple
    []         -> name

splitOnSep :: String -> String -> [String]
splitOnSep sep str = go str
  where
    go [] = [""]
    go s =
      case breakOnSep s of
        (chunk, Nothing)    -> [chunk]
        (chunk, Just rest') -> chunk : go rest'
    breakOnSep s =
      if sep `isPrefixOf` s
        then ("", Just (drop (length sep) s))
        else case s of
               []     -> ("", Nothing)
               (c:cs) ->
                 let (chunk, rest) = breakOnSep cs
                 in (c:chunk, rest)
