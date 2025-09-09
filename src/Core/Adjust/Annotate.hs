module Core.Adjust.Annotate where

import Control.Monad (unless, forM_)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromJust)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Control.Exception (catch, IOException)
import System.IO (hPutStrLn, stderr)

import Debug.Trace
import Control.Monad (unless, foldM)

import Core.Bind
import Core.BigCheck
import Core.Type
import Core.Show

annotateBook :: Book -> IO Book
annotateBook book@(Book defs names) = do
  let orderedDefs = [(name, fromJust (M.lookup name defs)) | name <- names]
  annotatedDefs <- traverse checkDef orderedDefs
  return $ Book (M.fromList annotatedDefs) names
  where
    checkDef (name, (inj, term, typ)) = do
      let checkResult = do 
            typ'  <- check 0 noSpan book (Ctx []) typ Set
            term' <- check 0 noSpan book (Ctx []) term typ'
            traceM $ "chec: " ++ show term'
            return (inj, term', typ')
      case checkResult of
        Done (inj', term', typ') -> do
          putStrLn $ "\x1b[32m✓ " ++ name ++ "\x1b[0m"
          return (name, (inj', term', typ'))
        Fail e -> do
          hPutStrLn stderr $ "\x1b[31m✗ " ++ name ++ "\x1b[0m"
          hPutStrLn stderr $ show e
          -- Keep original term when check fails
          return (name, (inj, term, typ))
