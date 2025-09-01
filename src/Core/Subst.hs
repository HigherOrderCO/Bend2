{-./../Type.hs-}

module Core.Subst 
  ( substituteRefs
  , SubstMap
  , substituteRefsInBook
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Core.Type
import Core.Show ()

type SubstMap = M.Map Name Name

-- | Apply a substitution map to all Ref terms in a term
substituteRefs :: SubstMap -> Term -> Term
substituteRefs subst = go S.empty
  where
    go bound term = case term of
      Ref k i -> 
        case M.lookup k subst of
          Just newName -> Ref newName i
          Nothing -> Ref k i
      
      -- Handle binding constructs  
      Var k i -> 
        if k `S.member` bound 
        then Var k i  -- It's a bound variable, don't substitute
        else case M.lookup k subst of
          Just newName -> Var newName i  -- It's a free variable, substitute it
          Nothing -> Var k i
      Sub t -> Sub (go bound t)
      Fix k f -> Fix k (\v -> go (S.insert k bound) (f v))
      Let k t v f -> Let k (fmap (go bound) t) (go bound v) (\u -> go (S.insert k bound) (f u))
      Use k v f -> Use k (go bound v) (\u -> go (S.insert k bound) (f u))
      
      -- Simple recursive cases
      Set -> Set
      Chk x t -> Chk (go bound x) (go bound t)
      Tst x -> Tst (go bound x)
      Emp -> Emp
      EmpM -> EmpM
      Uni -> Uni
      One -> One
      UniM f -> UniM (go bound f)
      Bit -> Bit
      Bt0 -> Bt0
      Bt1 -> Bt1
      BitM f t -> BitM (go bound f) (go bound t)
      Nat -> Nat
      Zer -> Zer
      Suc n -> Suc (go bound n)
      NatM z s -> NatM (go bound z) (go bound s)
      Lst t -> Lst (go bound t)
      Nil -> Nil
      Con h t -> Con (go bound h) (go bound t)
      LstM n c -> LstM (go bound n) (go bound c)
      Enu cs -> Enu cs
      Sym s -> Sym s
      EnuM cs d -> EnuM (map (\(s, t) -> (s, go bound t)) cs) (go bound d)
      Num n -> Num n
      Val v -> Val v
      Op2 op a b -> Op2 op (go bound a) (go bound b)
      Op1 op a -> Op1 op (go bound a)
      Sig a b -> Sig (go bound a) (go bound b)
      Tup a b -> Tup (go bound a) (go bound b)
      SigM f -> SigM (go bound f)
      All a b -> All (go bound a) (go bound b)
      Lam k t f -> Lam k (fmap (go bound) t) (\u -> go (S.insert k bound) (f u))
      App f x -> 
        let newF = go bound f
            newX = go bound x
            result = App newF newX
        in result
      Eql t a b -> Eql (go bound t) (go bound a) (go bound b)
      Rfl -> Rfl
      EqlM f -> EqlM (go bound f)
      Met n t ctx -> Met n (go bound t) (map (go bound) ctx)
      Era -> Era
      Sup n a b -> Sup n (go bound a) (go bound b)
      SupM l f -> SupM (go bound l) (go bound f)
      Loc sp t -> Loc sp (go bound t)
      Log s x -> Log (go bound s) (go bound x)
      Pri p -> Pri p
      Rwt e f -> Rwt (go bound e) (go bound f)
      Pat s m c -> Pat (map (go bound) s) 
                      (map (\(n, t) -> (n, go bound t)) m) 
                      (map (\(ps, b) -> (map (go bound) ps, go bound b)) c)
      Frk l a b -> Frk (go bound l) (go bound a) (go bound b)

-- | Apply substitution to a book
substituteRefsInBook :: SubstMap -> Book -> Book
substituteRefsInBook subst (Book defs names) = 
  Book (M.map (substituteRefsInDefn subst) defs) names
  where
    substituteRefsInDefn :: SubstMap -> Defn -> Defn
    substituteRefsInDefn s (inj, term, typ) = 
      let newTerm = substituteRefs s term
          newTyp = substituteRefs s typ
      in (inj, newTerm, newTyp)
