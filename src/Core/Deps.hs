{-./Type.hs-}

module Core.Deps where 

import qualified Data.Set as S
import qualified Data.Map as M

import Core.Type

getDeps :: Term -> S.Set Name
getDeps = collectDeps S.empty

getBookDeps :: Book -> S.Set Name
getBookDeps (Book defs) = S.unions $ map getDefnDeps (M.toList defs) where
  getDefnDeps :: (Name, Defn) -> S.Set Name
  getDefnDeps (name, (_, term, typ)) = S.union (getDeps term) (getDeps typ)

-- | Collects all external references from a term, handling variable binding.
-- This is a specialized version of `collectRefs` that also handles `Pat` constructors
-- by treating the head of a pattern application as a reference.
collectDeps :: S.Set Name -> Term -> S.Set Name
collectDeps bound term = case term of
  Var k _     -> if k `S.member` bound then S.empty else S.singleton k
  Ref k       -> S.singleton k
  Sub t       -> collectDeps bound t
  Fix k f     -> collectDeps (S.insert k bound) (f (Var k 0))
  Let v f     -> S.union (collectDeps bound v) (collectDeps bound f)
  Chk x t     -> S.union (collectDeps bound x) (collectDeps bound t)
  EmpM x      -> collectDeps bound x
  UniM x f    -> S.union (collectDeps bound x) (collectDeps bound f)
  BitM x f t  -> S.unions [collectDeps bound x, collectDeps bound f, collectDeps bound t]
  Suc n       -> collectDeps bound n
  NatM x z s  -> S.unions [collectDeps bound x, collectDeps bound z, collectDeps bound s]
  Lst t       -> collectDeps bound t
  Con h t     -> S.union (collectDeps bound h) (collectDeps bound t)
  LstM x n c  -> S.unions [collectDeps bound x, collectDeps bound n, collectDeps bound c]
  EnuM x cs d -> S.unions [collectDeps bound x, S.unions (map (collectDeps bound . snd) cs), collectDeps bound d]
  Sig a b     -> S.union (collectDeps bound a) (collectDeps bound b)
  Tup a b     -> S.union (collectDeps bound a) (collectDeps bound b)
  SigM x f    -> S.union (collectDeps bound x) (collectDeps bound f)
  All a b     -> S.union (collectDeps bound a) (collectDeps bound b)
  Lam k f     -> collectDeps (S.insert k bound) (f (Var k 0))
  App f x     -> S.union (collectDeps bound f) (collectDeps bound x)
  Eql t a b   -> S.unions [collectDeps bound t, collectDeps bound a, collectDeps bound b]
  EqlM x f    -> S.union (collectDeps bound x) (collectDeps bound f)
  Met _ t ctx -> S.unions (collectDeps bound t : map (collectDeps bound) ctx)
  Ind t       -> collectDeps bound t
  Frz t       -> collectDeps bound t
  Loc _ t     -> collectDeps bound t
  Rwt a b x   -> S.unions [collectDeps bound a, collectDeps bound b, collectDeps bound x]
  Sup _ a b   -> S.union (collectDeps bound a) (collectDeps bound b)
  Op2 _ a b   -> S.union (collectDeps bound a) (collectDeps bound b)
  Op1 _ a     -> collectDeps bound a
  Pat s m c   -> S.unions $ map (collectDeps bound) s ++ map (collectDeps bound . snd) m ++ concatMap (collectCaseDeps bound) c
  _           -> S.empty

-- | Helper for `collectDeps` to handle dependencies in pattern-match cases.
collectCaseDeps :: S.Set Name -> Case -> [S.Set Name]
collectCaseDeps bound (patterns, body) =
  let binders = S.unions (map collectPatternVars patterns)
      newBound = S.union bound binders
  in collectDeps newBound body : map (getPatternDeps bound) patterns

-- | Helper for `collectDeps` to extract dependencies from a single pattern.
-- In a pattern `f(x,y)`, `f` is a dependency, but `x` and `y` are binders.
getPatternDeps :: S.Set Name -> Term -> S.Set Name
getPatternDeps bound term = case cut term of
  Ref k     -> S.singleton k
  -- For an application in a pattern, only the function part can be a dependency.
  -- The arguments are binders, not expressions to be evaluated.
  App f _   -> collectDeps bound f
  Tup a b   -> S.union (getPatternDeps bound a) (getPatternDeps bound b)
  Con h t   -> S.union (getPatternDeps bound h) (getPatternDeps bound t)
  Suc n     -> getPatternDeps bound n
  Chk p _   -> getPatternDeps bound p
  -- Constructors that don't contain further dependencies
  _         -> S.empty

-- | Collects all variable names bound by a pattern.
collectPatternVars :: Term -> S.Set Name
collectPatternVars term = case cut term of
  Var k _   -> S.singleton k
  App _ _   -> let (_, args) = collectApps term [] in S.unions (map collectPatternVars args)
  Tup a b   -> S.union (collectPatternVars a) (collectPatternVars b)
  Con h t   -> S.union (collectPatternVars h) (collectPatternVars t)
  Suc n     -> collectPatternVars n
  Chk p _   -> collectPatternVars p
  _         -> S.empty
