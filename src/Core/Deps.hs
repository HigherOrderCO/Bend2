{-./Type.hs-}

module Core.Deps where

import qualified Data.Set as S
import qualified Data.Map as M

import Core.Type

getBookDepOrigins :: Book -> M.Map Name Span
getBookDepOrigins (Book defs _ _) = foldr collectDefs M.empty (M.toList defs)
  where
    collectDefs :: (Name, Defn) -> M.Map Name Span -> M.Map Name Span
    collectDefs (_, (_, term, typ)) acc =
      let termDeps = collectDepSpans S.empty Nothing term
          typDeps  = collectDepSpans S.empty Nothing typ
      in M.union termDeps (M.union typDeps acc)

getDeps :: Term -> S.Set Name
getDeps = collectDeps S.empty

getBookDeps :: Book -> S.Set Name
getBookDeps (Book defs _ _) = S.unions $ map getDefnDeps (M.toList defs) where
  getDefnDeps :: (Name, Defn) -> S.Set Name
  getDefnDeps (name, (_, term, typ)) = S.union (getDeps term) (getDeps typ)

-- -- | Collects all external references from a term, handling variable binding.
-- -- This is a specialized version of `collectRefs` that also handles `Pat` constructors
-- -- by treating the head of a pattern application as a reference.
collectDeps :: S.Set Name -> Term -> S.Set Name
collectDeps bound term = case term of
  Var k _     -> if k `S.member` bound then S.empty else S.singleton k
  Ref k i     -> S.singleton k
  Sub t       -> collectDeps bound t
  Fix k f     -> collectDeps (S.insert k bound) (f (Var k 0))
  Let k t v f -> S.unions [foldMap (collectDeps bound) t ,collectDeps bound v, collectDeps (S.insert k bound) (f (Var k 0))]
  Use k v f   -> S.union (collectDeps bound v) (collectDeps (S.insert k bound) (f (Var k 0)))
  Set         -> S.empty
  Chk x t     -> S.union (collectDeps bound x) (collectDeps bound t)
  Tst x       -> collectDeps bound x
  Emp         -> S.empty
  EmpM        -> S.empty
  Uni         -> S.empty
  One         -> S.empty
  UniM f      -> collectDeps bound f
  Bit         -> S.empty
  Bt0         -> S.empty
  Bt1         -> S.empty
  BitM f t    -> S.union (collectDeps bound f) (collectDeps bound t)
  Nat         -> S.empty
  Zer         -> S.empty
  Suc n       -> collectDeps bound n
  NatM z s    -> S.union (collectDeps bound z) (collectDeps bound s)
  Lst t       -> collectDeps bound t
  IO t        -> collectDeps bound t
  Nil         -> S.empty
  Con h t     -> S.union (collectDeps bound h) (collectDeps bound t)
  LstM n c    -> S.union (collectDeps bound n) (collectDeps bound c)
  Enu _       -> S.empty
  Sym _       -> S.empty
  EnuM cs d   -> S.union (S.unions (map (collectDeps bound . snd) cs)) (collectDeps bound d)
  Num _       -> S.empty
  Val _       -> S.empty
  Op2 _ a b   -> S.union (collectDeps bound a) (collectDeps bound b)
  Op1 _ a     -> collectDeps bound a
  Sig a b     -> S.union (collectDeps bound a) (case b of
                    Lam k _ f -> collectDeps (S.insert k bound) (f (Var k 0))
                    _ -> collectDeps bound b)
  Tup a b     -> S.union (collectDeps bound a) (collectDeps bound b)
  SigM f      -> collectDeps bound f
  All a b     -> S.union (collectDeps bound a) (case b of
                    Lam k _ f -> collectDeps (S.insert k bound) (f (Var k 0))
                    _ -> collectDeps bound b)
  Lam k t f   -> S.union (collectDeps (S.insert k bound) (f (Var k 0))) (foldMap (collectDeps bound) t)
  App f x     -> S.union (collectDeps bound f) (collectDeps bound x)
  Eql t a b   -> S.unions [collectDeps bound t, collectDeps bound a, collectDeps bound b]
  Rfl         -> S.empty
  EqlM f      -> collectDeps bound f
  Met _ t ctx -> S.unions (collectDeps bound t : map (collectDeps bound) ctx)
  Era         -> S.empty
  Sup _ a b   -> S.union (collectDeps bound a) (collectDeps bound b)
  SupM l f    -> S.union (collectDeps bound l) (collectDeps bound f)
  Loc _ t     -> collectDeps bound t
  Log s x     -> S.union (collectDeps bound s) (collectDeps bound x)
  Pri _       -> S.empty
  Rwt e f     -> S.union (collectDeps bound e) (collectDeps bound f)
  Pat s m c   -> S.unions $ map (collectDeps bound) s ++ map (collectDeps bound . snd) m ++ concatMap (collectCaseDeps bound) c
  Frk l a b   -> S.unions [collectDeps bound l, collectDeps bound a, collectDeps bound b]

-- | Helper for `collectDeps` to handle dependencies in pattern-match cases.
collectCaseDeps :: S.Set Name -> Case -> [S.Set Name]
collectCaseDeps bound (patterns, body) =
  let binders = S.unions (map collectPatternVars patterns)
      newBound = S.union bound binders
  in collectDeps newBound body : map (getPatternDeps bound) patterns
  where

  -- | Helper for `collectDeps` to extract dependencies from a single pattern.
  -- In a pattern `f(x,y)`, `f` is a dependency, but `x` and `y` are binders.
  getPatternDeps :: S.Set Name -> Term -> S.Set Name
  getPatternDeps bound term = case cut term of
    Ref k i   -> S.singleton k
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

collectDepSpans :: S.Set Name -> Maybe Span -> Term -> M.Map Name Span
collectDepSpans bound currentSpan term =
  case term of
    Loc sp t     -> collectDepSpans bound (Just sp) t
    Var k _      -> if k `S.member` bound then M.empty else spanEntry currentSpan k
    Ref k _      -> spanEntry currentSpan k
    Sub t        -> collectDepSpans bound currentSpan t
    Fix k f      -> collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
    Let k t v f  -> unions
      [ maybe M.empty (collectDepSpans bound currentSpan) t
      , collectDepSpans bound currentSpan v
      , collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
      ]
    Use k v f    -> unions
      [ collectDepSpans bound currentSpan v
      , collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
      ]
    Set          -> M.empty
    Chk x t      -> unions [collectDepSpans bound currentSpan x, collectDepSpans bound currentSpan t]
    Tst x        -> collectDepSpans bound currentSpan x
    Emp          -> M.empty
    EmpM         -> M.empty
    Uni          -> M.empty
    One          -> M.empty
    UniM f       -> collectDepSpans bound currentSpan f
    Bit          -> M.empty
    Bt0          -> M.empty
    Bt1          -> M.empty
    BitM f t     -> unions [collectDepSpans bound currentSpan f, collectDepSpans bound currentSpan t]
    Nat          -> M.empty
    Zer          -> M.empty
    Suc n        -> collectDepSpans bound currentSpan n
    NatM z s     -> unions [collectDepSpans bound currentSpan z, collectDepSpans bound currentSpan s]
    Lst t        -> collectDepSpans bound currentSpan t
    IO t         -> collectDepSpans bound currentSpan t
    Nil          -> M.empty
    Con h t      -> unions [collectDepSpans bound currentSpan h, collectDepSpans bound currentSpan t]
    LstM n c     -> unions [collectDepSpans bound currentSpan n, collectDepSpans bound currentSpan c]
    Enu _        -> M.empty
    Sym _        -> M.empty
    EnuM cs d    -> unions (collectDepSpans bound currentSpan d : map (collectDepSpans bound currentSpan . snd) cs)
    Num _        -> M.empty
    Val _        -> M.empty
    Op2 _ a b    -> unions [collectDepSpans bound currentSpan a, collectDepSpans bound currentSpan b]
    Op1 _ a      -> collectDepSpans bound currentSpan a
    Sig a b      -> unions
      [ collectDepSpans bound currentSpan a
      , case b of
          Lam k _ f -> collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
          other     -> collectDepSpans bound currentSpan other
      ]
    Tup a b      -> unions [collectDepSpans bound currentSpan a, collectDepSpans bound currentSpan b]
    SigM f       -> collectDepSpans bound currentSpan f
    All a b      -> unions
      [ collectDepSpans bound currentSpan a
      , case b of
          Lam k _ f -> collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
          other     -> collectDepSpans bound currentSpan other
      ]
    Lam k t f    -> unions
      [ maybe M.empty (collectDepSpans bound currentSpan) t
      , collectDepSpans (S.insert k bound) currentSpan (f (Var k 0))
      ]
    App f x      -> unions [collectDepSpans bound currentSpan f, collectDepSpans bound currentSpan x]
    Eql t a b    -> unions [collectDepSpans bound currentSpan t, collectDepSpans bound currentSpan a, collectDepSpans bound currentSpan b]
    Rfl          -> M.empty
    EqlM f       -> collectDepSpans bound currentSpan f
    Met _ t ctx  -> unions (collectDepSpans bound currentSpan t : map (collectDepSpans bound currentSpan) ctx)
    Era          -> M.empty
    Sup _ a b    -> unions [collectDepSpans bound currentSpan a, collectDepSpans bound currentSpan b]
    SupM l f     -> unions [collectDepSpans bound currentSpan l, collectDepSpans bound currentSpan f]
    Log s x      -> unions [collectDepSpans bound currentSpan s, collectDepSpans bound currentSpan x]
    Pri _        -> M.empty
    Rwt e f      -> unions [collectDepSpans bound currentSpan e, collectDepSpans bound currentSpan f]
    Pat s m c    ->
      let matches   = map (collectDepSpans bound currentSpan) s
          rewrites  = map (collectDepSpans bound currentSpan . snd) m
          caseDeps  = concatMap (collectCaseSpanDeps bound currentSpan) c
      in unions (matches ++ rewrites ++ caseDeps)
    Frk l a b    -> unions [collectDepSpans bound currentSpan l, collectDepSpans bound currentSpan a, collectDepSpans bound currentSpan b]

  where
    unions :: [M.Map Name Span] -> M.Map Name Span
    unions = foldr (M.unionWith keepExisting) M.empty

    keepExisting :: Span -> Span -> Span
    keepExisting existing _ = existing

    spanEntry :: Maybe Span -> Name -> M.Map Name Span
    spanEntry maybeSpan name = case maybeSpan of
      Just sp -> M.singleton name sp
      Nothing -> M.empty

    collectCaseSpanDeps :: S.Set Name -> Maybe Span -> Case -> [M.Map Name Span]
    collectCaseSpanDeps bound' spanCtx (patterns, body) =
      let binders = S.unions (map collectPatternVars patterns)
          newBound = S.union bound' binders
          bodyDeps = collectDepSpans newBound spanCtx body
          patDeps  = map (getPatternDeps bound' spanCtx) patterns
      in bodyDeps : patDeps
      where
        getPatternDeps :: S.Set Name -> Maybe Span -> Term -> M.Map Name Span
        getPatternDeps scope spanInfo term' = case cut term' of
          Ref k _ -> spanEntry spanInfo k
          App f _ -> collectDepSpans scope spanInfo f
          Tup a b -> unions [getPatternDeps scope spanInfo a, getPatternDeps scope spanInfo b]
          Con h t -> unions [getPatternDeps scope spanInfo h, getPatternDeps scope spanInfo t]
          Suc n   -> getPatternDeps scope spanInfo n
          Chk p _ -> getPatternDeps scope spanInfo p
          _       -> M.empty

        collectPatternVars :: Term -> S.Set Name
        collectPatternVars term' = case cut term' of
          Var k _ -> S.singleton k
          App _ _ ->
            let (_, args) = collectApps term' []
            in S.unions (map collectPatternVars args)
          Tup a b -> S.union (collectPatternVars a) (collectPatternVars b)
          Con h t -> S.union (collectPatternVars h) (collectPatternVars t)
          Suc n   -> collectPatternVars n
          Chk p _ -> collectPatternVars p
          _       -> S.empty
