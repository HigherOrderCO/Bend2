-- Converts a term to "Case-Tree" form. It has 3 main steps:
-- - FlattenPats : patterns become non-nested and single-scrutinee
-- - DesugarPats : patterns become native λ-matches
-- 
-- This file will also desugar forks into sups and dups. See DesugarForks.hs.

module Core.Adjust.Desugar where

import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

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
import Core.BigCheck

-- | Desugars a single term, simplifying pattern matching and other constructs.
-- It uses a book of already-desugared definitions for context during flattening.
-- Note: This does NOT check for free variables, as it may be called during
-- book desugarment where recursive references aren't available yet.

desugar :: Book -> Term -> Term
desugar book term =
  -- trace ("term: " ++ show term) $
  -- trace ("reso: " ++ show resolved) $
  -- trace ("flat: " ++ show flat) $
  -- trace ("npat: " ++ show npat) $
  -- trace ("nfrk: " ++ show nfrk) $
  -- trace ("hoas: " ++ show hoas) $
  -- trace ("etas: " ++ show etas) $
  -- hoas 
  etas
  where
    -- First resolve enums to their FQNs (needed for standalone use)
    resolved = case resolveEnumsInTerm (extractEnums book) term of
      Done t -> t
      Fail e -> error $ show e
    flat = flattenPats 0 noSpan book resolved
    npat = desugarPats 0 noSpan flat
    nfrk = desugarFrks book 0 npat
    hoas = bind nfrk
    etas = reduceEtas 0 hoas

-- | Desugars a term. simplifying patterns but leaving terms as Pats.
desugarWithPats :: Book -> Term -> Term
desugarWithPats book term =
  ret
  where 
    ret = bind (desugarFrks book 0 (flattenPats 0 noSpan book term))

-- The state for the desugarment process. It holds:
-- 1. The book of already-desugared definitions.
-- 2. A set of names that have been processed to avoid redundant work (memoization).
type DesugarState = (Book, S.Set Name)

-- | Desugars an entire book of definitions, respecting dependencies.
-- It performs a topological sort of the definitions based on their references
-- and desugars them in order. This ensures that when a definition is desugared,
-- all definitions it depends on have already been desugared.
-- This is crucial for functions like `flatten` which may look up references.
-- After desugaring all definitions, it checks for free variables.
desugarBook :: Book -> Book
desugarBook book@(Book defs names) =
  -- First resolve all enums in the entire book
  let resolvedBook = case resolveEnumsInBook book of
        Done b -> b
        Fail e -> error $ show e
      desugaredBook = fst $ execState (mapM_ (desugarDef resolvedBook S.empty desugar) (M.keys defs)) (Book M.empty names, S.empty)
  in desugaredBook -- checkFreeVarsInBook disabled: not in main branch
  -- let desugaredBook = fst $ execState (mapM_ (desugarDef book S.empty desugar) (M.keys defs)) (Book M.empty names, S.empty)
  -- in desugaredBook -- checkFreeVarsInBook disabled: not in main branch

-- | Desugars the entire book, simplifying patterns but without removing Pat terms.
desugarBookWithPats :: Book -> Book
desugarBookWithPats book@(Book defs names) =
  let desugaredBook = fst $ execState (mapM_ (desugarDef book S.empty desugarWithPats) (M.keys defs)) (Book M.empty names, S.empty)
  in desugaredBook -- checkFreeVarsInBook disabled: not in main branch

-- | Checks all definitions in a book for free variables.
-- This should be called after all desugarments are complete.
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

-- | The recursive worker function that desugars a single definition.
-- It takes a set of names currently in the recursion stack to detect cycles.
desugarDef :: Book -> S.Set Name -> (Book -> Term -> Term) -> Name -> State DesugarState ()
desugarDef book visiting desugarFn name = do
  (_, desugaredSet) <- get

  -- Process the definition only if it's not in the current recursion path (to avoid cycles)
  -- and has not been desugared yet (for memoization).
  if name `S.member` visiting || name `S.member` desugaredSet
    then return ()
    else case getDefn book name of
      -- This case should not be reachable if `name` comes from `M.keys defs`.
      Nothing -> return ()
      Just (inj, term, typ) -> do
        -- 1. Collect all dependencies (references) from the term and its type.
        -- We use a custom collector that correctly handles variable scope and
        -- treats function heads in patterns as dependencies.
        let deps = S.union (getDeps term) (getDeps typ)

        -- 2. Recursively desugar all dependencies.
        -- The current name is added to the `visiting` set for cycle detection.
        let newVisiting = S.insert name visiting
        mapM_ (desugarDef book newVisiting desugarFn) (S.toList deps)

        -- 3. After dependencies are desugared, desugar the current definition.
        -- We need to get the latest version of the desugared book from the state,
        -- as it has been updated by the recursive calls.
        (partialAdjBook@(Book defs n), _) <- get

        let adjType = desugarFn partialAdjBook typ
        let adjTerm = desugarFn partialAdjBook term

        -- 4. Update the state with the newly desugared definition.
        -- The name is added to the `desugaredSet` to mark it as complete.
        modify $ \(Book adjMap names, doneSet) ->
          let newAdjMap  = M.insert name (inj, adjTerm, adjType) adjMap
              newDoneSet = S.insert name doneSet
          in (Book newAdjMap names, newDoneSet)




--
--
-- addFix :: Name -> Term -> Term
-- addFix name term = 
--   if name `elem` getDeps term
--   then Fix name (\f -> go name term [f] M.empty)
--   else Set
--     where
--     go :: Name -> Term -> [Term] -> M.Map Name Term -> Term
--     go lv term ctx@[fn] vars = case term of
--       Var k i     -> Var k i
--       Ref k i     -> if k == name then k i
--       Sub t       -> t
--       Let k t v f -> Let k (fmap (\u -> go lv u ctx vars) t) (go lv v ctx vars) (\x -> go lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
--       Use k v f   -> Use k (go lv v ctx vars) (\x -> go lv (f (Sub x)) (ctx++[x]) (M.insert k x vars))
--       Fix k f     -> Fix k (\x -> go (lv) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
--       Set         -> Set
--       Chk x t     -> Chk (go lv x ctx vars) (go lv t ctx vars)
--       Tst x       -> Tst (go lv x ctx vars)
--       Emp         -> Emp
--       EmpM        -> EmpM
--       Uni         -> Uni
--       One         -> One
--       UniM f      -> UniM (go lv f ctx vars)
--       Bit         -> Bit
--       Bt0         -> Bt0
--       Bt1         -> Bt1
--       BitM f t    -> BitM (go lv f ctx vars) (go lv t ctx vars)
--       Nat         -> Nat
--       Zer         -> Zer
--       Suc n       -> Suc (go lv n ctx vars)
--       NatM z s    -> NatM (go lv z ctx vars) (go lv s ctx vars)
--       Lst t       -> Lst (go lv t ctx vars)
--       Nil         -> Nil
--       Con h t     -> Con (go lv h ctx vars) (go lv t ctx vars)
--       LstM n c    -> LstM (go lv n ctx vars) (go lv c ctx vars)
--       Enu s       -> Enu s
--       Sym s       -> Sym s
--       EnuM c e    -> EnuM (map (\(s, t) -> (s, go lv t ctx vars)) c) (go lv e ctx vars)
--       Sig a b     -> Sig (go lv a ctx vars) (go lv b ctx vars)
--       Tup a b     -> Tup (go lv a ctx vars) (go lv b ctx vars)
--       SigM f      -> SigM (go lv f ctx vars)
--       All a b     -> All (go lv a ctx vars) (go lv b ctx vars)
--       Lam k t f   -> Lam k (fmap (\t -> go lv t ctx vars) t) (\x -> go (lv+1) (f (Sub x)) (ctx++[x]) (M.insert k x vars))
--       App f x     -> App (go lv f ctx vars) (go lv x ctx vars)
--       Eql t a b   -> Eql (go lv t ctx vars) (go lv a ctx vars) (go lv b ctx vars)
--       Rfl         -> Rfl
--       EqlM f      -> EqlM (go lv f ctx vars)
--       Rwt e f     -> Rwt (go lv e ctx vars) (go lv f ctx vars)
--       Loc s t     -> Loc s (go lv t ctx vars)
--       Era         -> Era
--       Sup l a b   -> Sup (go lv l ctx vars) (go lv a ctx vars) (go lv b ctx vars)
--       SupM l f    -> SupM (go lv l ctx vars) (go lv f ctx vars)
--       Frk l a b   -> Frk (go lv l ctx vars) (go lv a ctx vars) (go lv b ctx vars)
--       Num t       -> Num t
--       Val v       -> Val v
--       Op2 o a b   -> Op2 o (go lv a ctx vars) (go lv b ctx vars)
--       Op1 o a     -> Op1 o (go lv a ctx vars)
--       Pri p       -> Pri p
--       Log s x     -> Log (go lv s ctx vars) (go lv x ctx vars)
--       Met k t c   -> Met k (go lv t ctx vars) (map (\x -> go lv x ctx vars) c)
--       Pat s m c   ->
--         -- Since Pat doesn't bind with HOAS, keep as Var
--         let s'     = map (\x -> go lv x ctx vars) s
--             m'     = map (\(k,x) -> (k, go lv x ctx vars)) m
--             c'     = map (\(p,x) -> (p, go lv x (ctx ++ map v mvar ++ map v (pvar p)) (M.union (M.fromList (map kv (mvar ++ pvar p))) vars))) c
--             mvar   = map fst m
--             pvar p = S.toList (S.unions (map (freeVars S.empty) p))
--             kv nam = (nam, Var nam 0)
--             v nam  = Var nam 0
--         in Pat s' m' c'
--     go lv term ctx vars = undefined
--
--
--
--
--
