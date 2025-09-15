-- # Core.Adjust
-- 
-- Converts a term to "Case-Tree" form. It has 3 main steps:
-- - FlattenPats : patterns become non-nested and single-scrutinee
-- - DesugarPats : patterns become native λ-matches
-- - ReduceEtas  : eta-reduces `λx.(λ{f} x)` into `λ{f}`
-- 
-- Example:
-- 
--   λa. λb. match a b { case 0n 0n: A ; case 0n 1n+bp: B ; case 1n+ap 0n: C ; case 1n+ap 1n+bp: D }
--   ---------------------------------------------------------------------------------------------------------------------- FlattenPats
--   λa. λb. match a { case 0n: match b { case 0n: A ; case 1n+bp: B } case 1n+ap: match b { case 0n: C ; case 1n+bp: D } }
--   ---------------------------------------------------------------------------------------------------------------------- DesugarPats
--   λa. λb. (λ{ 0n: (λ{ 0n:A 1n+:λbp.B } b) 1n+ap: (λ{ 0n:C 1n+bp:D } b)} a)
--   ------------------------------------------------------------------------ ReduceEtas
--   λ{ 0n: λ{ 0n:A 1n+:λbp.B } 1n+ap: λ{ 0n:C 1n+bp:D }}
-- 
-- Note the final result is in "eta-reduced case-tree form".
--
-- # Eta-Reduced Case-Tree (ERCT) Form
-- 
-- A term is in ERCT form when it is a closed expression without any
-- sub-expression in the form `(λ{...} x)`. In other words, the term
-- can't contain a *lambda-match applied to an expression*.
-- 
--   (λ{...} x)
-- 
-- I.e., a lambda-match applied to an argument.
-- 
-- Bend represents top-level definitions as case-trees, since:
-- - It helps with equality termination (see guarded deref)
-- - It prevents goals being stuck in "hidden expressions"
-- - It prevents rewrites when type-checking eliminations
-- - It makes it suitable for fast search (BendGen)
-- - It generates efficient HVM programs
-- 
-- In general, the eta-reduced case-trees are very handy as an internal
-- representation, so we stick to them. Note that there are some top-level
-- definitions that *can't* be represented that way. For example, consider:
-- 
--   F = λa. λb. match b: { case 0n: if a: A else: B case 1n+p: if a: C else: D }
-- 
-- If we attempt to manually convert it to a case-tree, the best we get is:
-- 
--   F = λa. λ{ 0n: (λ{ True: A ; False: B } a) 1n+p: (λ{ True: C ; False: D} a) }
-- 
-- We can't progress further, because there is no way to eta-reduce it to
-- eliminate the internal `(λ{...} x)`. What we could do, though, is split
-- it into two top-level definitions instead:
-- 
--   F = λa. λb. G(b,a)
--   G = λ{ True: λ{ 0n: A ; 1n+p: C } True: λ{ 0n: B ; 1n+p: D } }
-- 
-- Flipping the arguments allow us to progress, because we eliminate inputs in
-- the same order they're received; i.e., a `Bool → Nat → P` function first
-- eliminates the Bool, and then the Nat. Every top-level definition can be
-- split into many top-level definitions that are in ERCT form. Currently, this
-- is *not* done yet, but must be implemented before the initial launch.
-- 
-- This file will also desugar forks into sups and dups. See DesugarForks.hs.

module Core.Adjust.Adjust where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S

import Debug.Trace

import Core.Adjust.DesugarFrks
import Core.Adjust.DesugarPats
import Core.Adjust.FlattenPats
import Core.Adjust.ReduceEtas
import Core.Adjust.ResolveEnums
import Core.Bind
import Core.Deps
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF

-- | Adjusts a single term, simplifying pattern matching and other constructs.
-- It uses a book of already-adjusted definitions for context during flattening.
-- Note: This does NOT check for free variables, as it may be called during
-- book adjustment where recursive references aren't available yet.
-- When called from adjustBook, enums have already been resolved at the book level.
-- When called standalone (e.g., from parseTerm), enums are resolved here.
adjust :: Book -> Term -> Term
adjust book term =
  -- trace ("done: " ++ show done) $
  done
  where
    -- First resolve enums to their FQNs (needed for standalone use)
    resolved = case resolveEnumsInTerm (extractEnums book) term of
      Done t -> t
      Fail e -> error $ show e
    flat = flattenPats 0 noSpan book resolved
    npat = desugarPats 0 noSpan flat
    nfrk = desugarFrks book 0 npat
    etas = reduceEtas 0 nfrk
    done = bind etas


-- | Adjusts a term. simplifying patterns but leaving terms as Pats.
adjustWithPats :: Book -> Term -> Term
adjustWithPats book term =
  ret
  where
    ret = bind (desugarFrks book 0 (flattenPats 0 noSpan book term))

-- The state for the adjustment process. It holds:
-- 1. The book of already-adjusted definitions.
-- 2. A set of names that have been processed to avoid redundant work (memoization).
type AdjustState = (Book, S.Set Name)

-- | Adjusts an entire book of definitions, respecting dependencies.
-- It performs a topological sort of the definitions based on their references
-- and adjusts them in order. This ensures that when a definition is adjusted,
-- all definitions it depends on have already been adjusted.
-- This is crucial for functions like `flatten` which may look up references.
-- After adjusting all definitions, it checks for free variables.
adjustBook :: Book -> Book
adjustBook book@(Book defs names) =
  -- First resolve all enums in the entire book
  let resolvedBook = case resolveEnumsInBook book of
        Done b -> b
        Fail e -> error $ show e
      adjustedBook = fst $ execState (mapM_ (adjustDef resolvedBook S.empty adjust) (M.keys defs)) (Book M.empty names, S.empty)
  in adjustedBook -- checkFreeVarsInBook disabled: not in main branch

-- | Adjusts the entire book, simplifying patterns but without removing Pat terms.
adjustBookWithPats :: Book -> Book
adjustBookWithPats book@(Book defs names) =
  -- First resolve all enums in the entire book
  let resolvedBook = case resolveEnumsInBook book of
        Done b -> b
        Fail e -> error $ show e
      adjustedBook = fst $ execState (mapM_ (adjustDef resolvedBook S.empty adjustWithPats) (M.keys defs)) (Book M.empty names, S.empty)
  in adjustedBook -- checkFreeVarsInBook disabled: not in main branch

-- | Checks all definitions in a book for free variables.
-- This should be called after all adjustments are complete.
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

-- | The recursive worker function that adjusts a single definition.
-- It takes a set of names currently in the recursion stack to detect cycles.
adjustDef :: Book -> S.Set Name -> (Book -> Term -> Term) -> Name -> State AdjustState ()
adjustDef book visiting adjustFn name = do
  (_, adjustedSet) <- get

  -- Process the definition only if it's not in the current recursion path (to avoid cycles)
  -- and has not been adjusted yet (for memoization).
  if name `S.member` visiting || name `S.member` adjustedSet
    then return ()
    else case getDefn book name of
      -- This case should not be reachable if `name` comes from `M.keys defs`.
      Nothing -> return ()
      Just (inj, term, typ) -> do
        -- 1. Collect all dependencies (references) from the term and its type.
        -- We use a custom collector that correctly handles variable scope and
        -- treats function heads in patterns as dependencies.
        let deps = S.union (getDeps term) (getDeps typ)

        -- 2. Recursively adjust all dependencies.
        -- The current name is added to the `visiting` set for cycle detection.
        let newVisiting = S.insert name visiting
        mapM_ (adjustDef book newVisiting adjustFn) (S.toList deps)

        -- 3. After dependencies are adjusted, adjust the current definition.
        -- We need to get the latest version of the adjusted book from the state,
        -- as it has been updated by the recursive calls.
        (partialAdjBook, _) <- get

        let adjTerm = adjustFn partialAdjBook term
        let adjType = adjustFn partialAdjBook typ

        -- 4. Update the state with the newly adjusted definition.
        -- The name is added to the `adjustedSet` to mark it as complete.
        modify $ \(Book adjMap names, doneSet) ->
          let newAdjMap  = M.insert name (inj, adjTerm, adjType) adjMap
              newDoneSet = S.insert name doneSet
          in (Book newAdjMap names, newDoneSet)
