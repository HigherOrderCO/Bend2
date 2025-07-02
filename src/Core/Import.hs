{-./Type.hs-}

module Core.Import 
  ( autoImport
  , collectRefs
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath (takeDirectory, (</>))
import System.Exit (exitFailure)

import Core.Type
import Core.Parse.Book (doParseBook)
import Core.Bind (bindBook)

-- Auto-import unbound references in a Book
autoImport :: FilePath -> Book -> IO Book
autoImport _ book = do
  let unboundRefs = collectUnboundRefs book
  result <- autoImportRefs book unboundRefs S.empty
  case result of
    Left err -> do
      putStrLn $ "Error: " ++ err
      exitFailure
    Right book' -> return book'

-- Collect all unbound references from a Book
collectUnboundRefs :: Book -> S.Set Name
collectUnboundRefs (Book defs) = S.unions $ map collectRefsFromDefn (M.elems defs) where
  collectRefsFromDefn (_, term, typ) = S.union (collectRefs term) (collectRefs typ)

-- Collect all Ref terms from a Term
collectRefs :: Term -> S.Set Name
collectRefs term = case term of
  Ref name    -> S.singleton name
  Var _ _     -> S.empty
  Sub t       -> collectRefs t
  Fix _ f     -> collectRefs (f (Var "dummy" 0))
  Let v f     -> S.union (collectRefs v) (collectRefs f)
  Set         -> S.empty
  Chk x t     -> S.union (collectRefs x) (collectRefs t)
  Emp         -> S.empty
  EmpM x      -> collectRefs x
  Uni         -> S.empty
  One         -> S.empty
  UniM x f    -> S.union (collectRefs x) (collectRefs f)
  Bit         -> S.empty
  Bt0         -> S.empty
  Bt1         -> S.empty
  BitM x f t  -> S.unions [collectRefs x, collectRefs f, collectRefs t]
  Nat         -> S.empty
  Zer         -> S.empty
  Suc n       -> collectRefs n
  NatM x z s  -> S.unions [collectRefs x, collectRefs z, collectRefs s]
  Lst t       -> collectRefs t
  Nil         -> S.empty
  Con h t     -> S.union (collectRefs h) (collectRefs t)
  LstM x n c  -> S.unions [collectRefs x, collectRefs n, collectRefs c]
  Enu _       -> S.empty
  Sym _       -> S.empty
  EnuM x c d  -> S.unions [collectRefs x, S.unions (map (collectRefs . snd) c), collectRefs d]
  Sig a b     -> S.union (collectRefs a) (collectRefs b)
  Tup a b     -> S.union (collectRefs a) (collectRefs b)
  SigM x f    -> S.union (collectRefs x) (collectRefs f)
  All a b     -> S.union (collectRefs a) (collectRefs b)
  Lam _ f     -> collectRefs (f (Var "dummy" 0))
  App f x     -> S.union (collectRefs f) (collectRefs x)
  Eql t a b   -> S.unions [collectRefs t, collectRefs a, collectRefs b]
  Rfl         -> S.empty
  EqlM x f    -> S.union (collectRefs x) (collectRefs f)
  Met _ t ctx -> S.unions (collectRefs t : map collectRefs ctx)
  Ind t       -> collectRefs t
  Frz t       -> collectRefs t
  Loc _ t     -> collectRefs t
  Rwt a b x   -> S.unions [collectRefs a, collectRefs b, collectRefs x]
  Era         -> S.empty
  Sup _ a b   -> S.union (collectRefs a) (collectRefs b)
  Num _       -> S.empty
  Val _       -> S.empty
  Op2 _ a b   -> S.union (collectRefs a) (collectRefs b)
  Op1 _ a     -> collectRefs a
  Pri _       -> S.empty
  Pat s m c   -> S.unions $ map collectRefs s ++ map (collectRefs . snd) m ++ concatMap (\ (p, b) -> collectRefs b : map collectRefs p) c

-- Auto-import references with cycle detection
autoImportRefs :: Book -> S.Set Name -> S.Set FilePath -> IO (Either String Book)
autoImportRefs book refs _ | S.null refs = return (Right book)
autoImportRefs book refs visited = do
  result <- foldM (autoImportRef visited) (Right (book, S.empty)) (S.toList refs)
  case result of
    Left err -> return (Left err)
    Right (book', newRefs) ->
      if S.null newRefs
        then return (Right book')
        else autoImportRefs book' newRefs visited

-- Auto-import a single reference
-- FIXME: simplify this ugly code
autoImportRef :: S.Set FilePath -> Either String (Book, S.Set Name) -> Name -> IO (Either String (Book, S.Set Name))
autoImportRef _ (Left err) _ = return (Left err)
autoImportRef visited (Right (book@(Book defs), newRefs)) refName = do
  -- Check if the reference already exists in the book
  if M.member refName defs
    then return (Right (book, newRefs))
    else do
      let filePath = refName ++ ".bend"
      let pyFilePath = refName ++ ".bend.py"
      let altFilePath = refName </> "_.bend"
      let altPyFilePath = refName </> "_.bend.py"
      fileExists <- doesFileExist filePath
      pyFileExists <- doesFileExist pyFilePath
      altFileExists <- doesFileExist altFilePath
      altPyFileExists <- doesFileExist altPyFilePath
      -- Try the direct file first, then the Python file, then the alternative paths
      let (actualPath, pathExists) = if fileExists then (filePath, True)
                                      else if pyFileExists then (pyFilePath, True)
                                      else if altFileExists then (altFilePath, True)
                                      else if altPyFileExists then (altPyFilePath, True)
                                      else (filePath, False)
      if pathExists && not (actualPath `S.member` visited)
        then do
          content <- readFile actualPath
          case doParseBook actualPath content of
            Left err -> return (Left $ "Failed to parse " ++ actualPath ++ ": " ++ err)
            Right importedBook -> do
              -- Recursively auto-import the imported book
              let visited' = S.insert actualPath visited
              importResult <- autoImportRefs importedBook 
                                           (collectUnboundRefs importedBook) visited'
              case importResult of
                Left err -> return (Left err)
                Right importedBook' -> do
                  -- Merge the imported book into the current book
                  let mergedBook = mergeBooks book importedBook'
                  let additionalRefs = collectUnboundRefs importedBook'
                  return (Right (mergedBook, S.union newRefs additionalRefs))
        else
          return (Left $ "Definition '" ++ refName ++ "' not found. Expected file at: " ++ filePath ++ 
                        ", " ++ pyFilePath ++ ", " ++ altFilePath ++ " or " ++ altPyFilePath)

-- Merge two books, preferring definitions from the first book
mergeBooks :: Book -> Book -> Book
mergeBooks (Book defs1) (Book defs2) = Book (M.union defs1 defs2)
