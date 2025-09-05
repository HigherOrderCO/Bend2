-- Converts a term to "Case-Tree" form. It has 3 main steps:
-- - FlattenPats : patterns become non-nested and single-scrutinee
-- - ElaboratePats : patterns become native λ-matches
-- 
-- This file will also elaborate forks into sups and dups. See ElaborateForks.hs.

module Core.Adjust.Elaborate where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

import Debug.Trace

import Core.Adjust.DesugarFrks
import Core.Adjust.FlattenPats
import Core.Adjust.ReduceEtas
import Core.Adjust.SplitMatch
import Core.Bind
import Core.Deps
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF
import Core.BigCheck

-- | Elaborates a single term, simplifying pattern matching and other constructs.
-- It uses a book of already-elaborateed definitions for context during flattening.
-- Note: This does NOT check for free variables, as it may be called during
-- book elaboratement where recursive references aren't available yet.

elaborate :: Book -> Term -> Term
elaborate book term =
  trace ("term: " ++ show term) $
  trace ("splt: " ++ show splt) $
  trace ("etas: " ++ show etas) $
  etas
  where
    splt = split 0 0 term
    etas = reduceEtas 0 splt

-- | Elaborates a term. simplifying patterns but leaving terms as Pats.
elaborateWithPats :: Book -> Term -> (Maybe Term) -> Term
elaborateWithPats book term typ =
  ret
  where 
    ret = bind (desugarFrks book 0 (flattenPats 0 noSpan book term))

-- The state for the elaboratement process. It holds:
-- 1. The book of already-elaborateed definitions.
-- 2. A set of names that have been processed to avoid redundant work (memoization).
type ElaborateState = (Book, S.Set Name)

-- | Elaborates an entire book of definitions, respecting dependencies.
-- It performs a topological sort of the definitions based on their references
-- and elaborates them in order. This ensures that when a definition is elaborateed,
-- all definitions it depends on have already been elaborateed.
-- This is crucial for functions like `flatten` which may look up references.
-- After elaborateing all definitions, it checks for free variables.
elaborateBook :: Book -> Book
elaborateBook book@(Book defs names) =
  let elaborateedBook = fst $ execState (mapM_ (elaborateDef book S.empty elaborate) (M.keys defs)) (Book M.empty names, S.empty)
  in elaborateedBook -- checkFreeVarsInBook disabled: not in main branch

-- -- | Elaborates the entire book, simplifying patterns but without removing Pat terms.
-- elaborateBookWithPats :: Book -> Book
-- elaborateBookWithPats book@(Book defs names) =
--   let elaborateedBook = fst $ execState (mapM_ (elaborateDef book S.empty elaborateWithPats) (M.keys defs)) (Book M.empty names, S.empty)
--   in elaborateedBook -- checkFreeVarsInBook disabled: not in main branch

-- | Checks all definitions in a book for free variables.
-- This should be called after all elaboratements are complete.
checkFreeVarsInBook :: Book -> Book
checkFreeVarsInBook book@(Book defs names) =
  case [ (name, frees) | 
         (name, (_, term, typ)) <- M.toList defs,
         let freeInTerm = freeVars S.empty term,
         let freeInType = freeVars S.empty typ,
         let frees = S.union freeInTerm freeInType,
         not (S.null frees) ] of
    [] -> book
    ((name, frees):_) -> 
      let freeName = S.elemAt 0 frees
      in error $ "Unbound variable '" ++ freeName ++ "' in definition '" ++ name ++ "'."

-- | The recursive worker function that elaborates a single definition.
-- It takes a set of names currently in the recursion stack to detect cycles.
elaborateDef :: Book -> S.Set Name -> (Book -> Term -> Term) -> Name -> State ElaborateState ()
elaborateDef book visiting elaborateFn name = do
  (_, elaborateedSet) <- get

  -- Process the definition only if it's not in the current recursion path (to avoid cycles)
  -- and has not been elaborateed yet (for memoization).
  if name `S.member` visiting || name `S.member` elaborateedSet
    then return ()
    else case getDefn book name of
      -- This case should not be reachable if `name` comes from `M.keys defs`.
      Nothing -> return ()
      Just (inj, term, typ) -> do
        -- 1. Collect all dependencies (references) from the term and its type.
        -- We use a custom collector that correctly handles variable scope and
        -- treats function heads in patterns as dependencies.
        let deps = S.union (getDeps term) (getDeps typ)

        -- 2. Recursively elaborate all dependencies.
        -- The current name is added to the `visiting` set for cycle detection.
        let newVisiting = S.insert name visiting
        mapM_ (elaborateDef book newVisiting elaborateFn) (S.toList deps)

        -- 3. After dependencies are elaborateed, elaborate the current definition.
        -- We need to get the latest version of the elaborateed book from the state,
        -- as it has been updated by the recursive calls.
        (partialAdjBook@(Book defs n), _) <- get

        let adjType = elaborateFn partialAdjBook typ
        let adjTerm = elaborateFn partialAdjBook term

        -- 4. Update the state with the newly elaborateed definition.
        -- The name is added to the `elaborateedSet` to mark it as complete.
        modify $ \(Book adjMap names, doneSet) ->
          let newAdjMap  = M.insert name (inj, adjTerm, adjType) adjMap
              newDoneSet = S.insert name doneSet
          in (Book newAdjMap names, newDoneSet)
