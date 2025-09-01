{-# LANGUAGE ViewPatterns #-}

module Core.Adjust.SplitMatch where

import Core.Bind
import Core.BigCheck
import Core.FreeVars
import Core.Show
import Core.Type
import Core.WHNF
import qualified Data.Set as S
import Debug.Trace (trace)

-- split :: Int -> Span -> Book -> Ctx -> Term -> Term -> Term
-- split d span book ctx (Loc l t) goal =
--   Loc l (split d span book ctx t goal)
-- split d span book ctx term      goal =
--   case (term, force book goal) of
--     (Tst x, _) ->
--       term
--     (Era, _) ->
--       term
--     (Let k (Just t) v f, _) ->
--                   Let k (Just $ split d span book ctx t Set)
--                         (split d span book ctx t goal)
--                         (\x -> bindVarByName k x $ split (d+1) span book (extend ctx k (Var k d) t) (f (Var k d)) goal)
--     (Let k Nothing v f, _) ->
--         case infer d span book ctx v of
--         Done t -> Let k (Just $ split d span book ctx t Set)
--                         (split d span book ctx t goal)
--                         (\x -> bindVarByName k x $ split (d+1) span book (extend ctx k (Var k d) t) (f (Var k d)) goal)
--         _ -> term
--     (Use k v f, _) -> Use k v (\x -> bindVarByName k x $ split d span book ctx (f v) goal)
--     (One, Uni) -> term
--     (Bt0, Bit) -> term
--     (Bt1, Bit) -> term
--     (Zer, Nat) -> term
--     (Suc n, Nat) -> Suc (split d span book ctx n Nat)
--     (Suc n, Eql t (force book -> Suc a) (force book -> Suc b)) -> Suc (split d span book ctx n (Eql t a b))
--     (Nil, Lst t) -> term
--     (Nil, goal) -> term
--     (Con h t, Lst tT) ->
--       Con (split d span book ctx h tT) (split d span book ctx t (Lst tT))
--     (Con h t, Eql (force book -> Lst tT) (force book -> Con h1 t1) (force book -> Con h2 t2)) ->
--       Con (split d span book ctx h (Eql tT h1 h2)) (split d span book ctx t (Eql (Lst tT) t1 t2))
--     (Lam k t f, All a b) -> Lam k (fmap (\x -> split d span book ctx x Set) t)
--                                   (\x -> bindVarByName k x $ split d span book (extend ctx k (Var k d) a) (f (Var k d)) (App b (Var k d)))
--     (EmpM, All (force book -> Eql t (force book -> Zer) (force book -> Suc y)) rT) -> term
--     (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Zer)) rT) -> term
--     (EmpM, All (force book -> Eql t (force book -> Suc x) (force book -> Suc y)) rT) -> term
--     (EmpM, All (force book -> Emp) rT) -> term
--     (EmpM, _) -> term
--     (UniM f, All (force book -> Eql (force book -> Uni) (force book -> One) (force book -> One)) rT) -> UniM (split d span book ctx f (App rT Rfl))
--     (UniM f, All (force book -> Uni) rT) -> UniM (split d span book ctx f (App rT One))
--     (UniM f, _) -> term
--     (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt0)) rT) ->
--       BitM (split d span book ctx f (App rT Rfl)) t
--     (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt1)) rT) ->
--       BitM f (split d span book ctx t (App rT Rfl))
--     (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt0) (force book -> Bt1)) rT) ->
--       term
--     (BitM f t, All (force book -> Eql (force book -> Bit) (force book -> Bt1) (force book -> Bt0)) rT) -> 
--       term
--     (BitM f t, All (force book -> Bit) rT) ->
--       BitM (split d span book ctx f (App rT Bt0)) (split d span book ctx t (App rT Bt1))
--     (BitM f t, _) ->
--       term
--     (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Zer)) rT) ->
--       NatM (split d span book ctx z (App rT Rfl)) s
--     (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc a) (force book -> Suc b)) rT) ->
--       NatM z (split d span book ctx s (All (Eql Nat a b) (Lam "p" Nothing (\p -> App rT (Suc p)))))
--     (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Zer) (force book -> Suc _)) rT) ->
--       term
--     (NatM z s, All (force book -> Eql (force book -> Nat) (force book -> Suc _) (force book -> Zer)) rT) ->
--       term
--     (NatM z s, All (force book -> Nat) rT) ->
--       NatM (split d span book ctx z (App rT Zer)) (split d span book ctx s (All Nat (Lam "p" Nothing (\p -> App rT (Suc p)))))
--     (NatM z s, _) ->
--       term
--     (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Nil)) rT) ->
--       LstM (split d span book ctx n (App rT Rfl)) c
--     (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con h1 t1) (force book -> Con h2 t2)) rT) ->
--       LstM n (split d span book ctx c (All (Eql a h1 h2) (Lam "hp" Nothing (\hp -> 
--         All (Eql (Lst a) t1 t2) (Lam "tp" Nothing (\tp -> 
--           App rT (Con hp tp)))))))
--     (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Nil) (force book -> Con _ _)) rT) ->
--       term
--     (LstM n c, All (force book -> Eql (force book -> Lst a) (force book -> Con _ _) (force book -> Nil)) rT) ->
--       term
--     (LstM n c, All (force book -> Lst a) rT) -> do
--       LstM (split d span book ctx n (App rT Nil)) (split d span book ctx c (All a (Lam "h" Nothing (\h -> All (Lst a) (Lam "t" Nothing (\t -> App rT (Con h t)))))))
--     (LstM n c, _) ->
--       term
--     (Sym s, Enu y) -> term
--     (Sym s, Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) -> term
--     (EnuM cs df, All (force book -> Eql (force book -> Enu syms) (force book -> Sym s1) (force book -> Sym s2)) rT) -> do
--       if s1 == s2
--         then case lookup s1 cs of
--           Just t -> do
--             EnuM (map (\(s,t) -> (s,split d span book ctx t (App rT Rfl))) cs) (split d span book ctx df (All (Enu syms) (Lam "_" Nothing (\v -> App rT v)))) 
--           Nothing -> do
--             EnuM cs (split d span book ctx df (All (Enu syms) (Lam "_" Nothing (\v -> App rT v))))
--         else term
--     (EnuM cs df, All (force book -> Enu syms) rT) -> do
--       -- mapM_ (\(s, t) -> checkAnn d span book ctx t (App rT (Sym s))) cs
--       let cs' = map (\(s, t) -> split d span book ctx t (App rT (Sym s))) cs
--       let covered_syms = map fst cs
--       let all_covered = length covered_syms >= length syms
--                      && all (`elem` syms) covered_syms
--       if not all_covered
--         then do
--           let enu_type = Enu syms
--           let lam_goal = All enu_type (Lam "_" Nothing (\v -> App rT v))
--           checkAnn d span book ctx df lam_goal
--           Done term
--         else return term
--     (EnuM cs df, _) -> do
--       Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Enu []) (Lam "_" Nothing (\_ -> Set)))) Nothing
--     (SigM f, All (force book -> Eql (force book -> Sig a b) (force book -> Tup x1 y1) (force book -> Tup x2 y2)) rT) -> do
--       checkAnn d span book ctx f (All (Eql a x1 x2) (Lam "xp" Nothing (\xp -> 
--         All (Eql (App b x1) y1 y2) (Lam "yp" Nothing (\yp -> 
--           App rT (Tup xp yp))))))
--       Done term
--     (SigM f, All (force book -> Sig a b) rT) -> do
--       checkAnn d span book ctx f $ All a (Lam "x" Nothing (\h -> All (App b h) (Lam "y" Nothing (\t -> App rT (Tup h t)))))
--       Done term
--     (SigM f, _) -> do
--       Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Sig (Var "_" 0) (Lam "_" Nothing (\_ -> Var "_" 0))) (Lam "_" Nothing (\_ -> Set)))) Nothing
--     (Tup a b, Sig aT bT) -> do
--       checkAnn d span book ctx a aT
--       checkAnn d span book ctx b (App bT a)
--       Done term
--     (Tup a b, Eql (force book -> Sig aT bT) (force book -> Tup a1 b1) (force book -> Tup a2 b2)) -> do
--       checkAnn d span book ctx a (Eql aT a1 a2)
--       checkAnn d span book ctx b (Eql (App bT a1) b1 b2)
--       Done term
--     (Rfl, Eql t a b) -> do
--       if equal d book a b
--         then Done term
--         else Fail $ TermMismatch span (normalCtx book ctx) (normal book a) (normal book b) Nothing
--     (EqlM f, All (force book -> Eql t a b) rT) -> do
--       let rewrittenGoal = rewrite d book a b (App rT Rfl)
--       let rewrittenCtx  = rewriteCtx d book a b ctx
--       checkAnn d span book rewrittenCtx f rewrittenGoal
--       Done term
--     (Fix k f, _) -> do
--       checkAnn (d+1) span book (extend ctx k (Fix k f) goal) (f (Fix k f)) goal
--       Done term
--     (Val v@(U64_V _), Num U64_T) -> do
--       Done term
--     (Val v@(I64_V _), Num I64_T) -> do
--       Done term
--     (Val v@(F64_V _), Num F64_T) -> do
--       Done term
--     (Val v@(CHR_V _), Num CHR_T) -> do
--       Done term
--     (Val v1, Eql (force book -> Num t) (force book -> Val v2) (force book -> Val v3)) -> do
--       if v1 == v2 && v2 == v3
--         then Done term
--         else Fail $ TermMismatch span (normalCtx book ctx) (normal book (Val v2)) (normal book (Val v3)) Nothing
--     (Op2 op a b, _) -> do
--       ta <- infer d span book ctx a
--       tb <- infer d span book ctx b
--       tr <- inferOp2Type d span book ctx op ta tb
--       if equal d book tr goal
--         then Done term
--         else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing
--     (Op1 op a, _) -> do
--       ta <- infer d span book ctx a
--       tr <- inferOp1Type d span book ctx op ta
--       if equal d book tr goal
--         then Done term
--         else Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book tr) Nothing
--     (Sup l a b, _) -> do
--       checkAnn d span book ctx a goal
--       checkAnn d span book ctx b goal
--       Done term
--     (SupM l f, All (force book -> Eql t (force book -> Sup l1 a1 b1) (force book -> Sup l2 a2 b2)) rT) -> do
--       if equal d book l l1 && equal d book l1 l2
--         then do
--           checkAnn d span book ctx f (All (Eql t a1 a2) (Lam "ap" Nothing (\ap -> 
--                  All (Eql t b1 b2) (Lam "bp" Nothing (\bp -> 
--                    App rT (Sup l ap bp))))))
--           Done term
--         else Fail $ TermMismatch span (normalCtx book ctx) (normal book l1) (normal book l2) Nothing
--     (SupM l f, _) -> do
--       checkAnn d span book ctx l (Num U64_T)
--       case force book goal of
--         All xT rT -> do
--           checkAnn d span book ctx f (All xT (Lam "p" Nothing (\p -> All xT (Lam "q" Nothing (\q -> App rT (Sup l p q))))))
--           Done term
--         _ -> Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (normal book (All (Var "_" 0) (Lam "_" Nothing (\_ -> Set)))) Nothing
--     (Frk l a b, _) -> do
--       checkAnn d span book ctx l (Num U64_T)
--       checkAnn d span book ctx a goal
--       checkAnn d span book ctx b goal
--       Done term
--     (Rwt e f, _) -> do
--       eT <- infer d span book ctx e
--       case force book eT of
--         Eql t a b -> do
--           let rewrittenCtx  = rewriteCtx d book a b ctx
--           let rewrittenGoal = rewrite d book a b goal
--           checkAnn d span book rewrittenCtx f rewrittenGoal
--           Done term
--         _ ->
--           Fail $ TypeMismatch span (normalCtx book ctx) (normal book (Eql (Var "_" 0) (Var "_" 0) (Var "_" 0))) (normal book eT) Nothing
--     (Pat _ _ _, _) -> do
--       error $ "not-supported:\n-term: " ++ show term ++ "\n-goal: " ++ show goal
--     (Log s x, _) -> do
--       checkAnn d span book ctx s (Lst (Num CHR_T))
--       checkAnn d span book ctx x goal
--       Done term
--     (App (Pri HVM_INC) x, _) -> do
--       checkAnn d span book ctx x goal
--       Done term
--     (App (Pri HVM_DEC) x, _) -> do
--       checkAnn d span book ctx x goal
--       Done term
--     (Lam f t x, _) ->
--       Fail $ TypeMismatch span (normalCtx book ctx) (normal book goal) (Ref "Function" 1) Nothing
--     (App (SupM l f) x, _) -> do
--       xT <- infer d span book ctx x
--       checkAnn d span book ctx f (All xT (Lam "_" Nothing (\_ -> All xT (Lam "_" Nothing (\_ -> goal)))))
--       Done term
--     (App (cut -> EmpM) x, _) -> do
--       checkAnn d span book ctx x Emp
--       Done term
--     (App fn@(cut -> UniM f) x, _) -> do
--       x' <- checkAnn d span book ctx x Uni
--       f' <- checkAnn d span book (rewriteCtx d book x One ctx) f (rewrite d book x One goal)
--       case cut x of
--         Var _ _ -> Done $ App (UniM f) x
--         _       -> Done $ App (Chk (UniM f) (All Uni (Lam "_" Nothing (\_ -> goal)))) x
--     (App (cut -> BitM f t) x, _) -> do
--       checkAnn d span book ctx x Bit
--       checkAnn d span book (rewriteCtx d book x Bt0 ctx) f (rewrite d book x Bt0 goal)
--       checkAnn d span book (rewriteCtx d book x Bt1 ctx) t (rewrite d book x Bt1 goal)
--       Done term
--     (App (cut -> NatM z s) x, _) -> do
--       -- traceM $ "- CHECK NATM: " ++ show term ++ " :: " ++ show goal ++ " , x = " ++ show x
--       checkAnn d span book ctx x Nat
--       checkAnn d span book (rewriteCtx d book x Zer ctx) z (rewrite d book x Zer goal)
--       case cut s of
--         Lam p mtb bp -> do
--           let body         = bp (Var p d)
--           let ctxWithP     = (extend ctx p (Var p d) Nat)
--           let ctxWithSucP  = (rewriteCtx (d+1) book x (Suc (Var p d)) ctxWithP)
--           let bodyWithSucP = (rewrite (d+1) book x (Suc (Var p d)) body)
--           let goalWithSucP = (rewrite (d+1) book x (Suc (Var p d)) goal)
--           -- traceM $ "- CHECK NATM SUC: " ++ show bodyWithSucP ++ " :: " ++ show goalWithSucP
--           checkAnn (d+1) (getSpan span body) book ctxWithSucP bodyWithSucP goalWithSucP
--           Done term
--         _ -> do
--           checkAnn d span book ctx s (All Nat (Lam "_" Nothing (\_ -> goal)))
--           Done term
--     (App (cut -> LstM z s) x, _) -> do -- TODO: perhaps add a case for x = [], checkAnning only `z`
--       xT <- infer d span book ctx x
--       checkAnn d span book (rewriteCtx d book x Nil ctx) z (rewrite d book x Nil goal)
--       case cut $ normal book xT of 
--         Lst hT ->
--           case cut s of
--             Lam h mth bh -> do
--               case cut (bh (Var h d)) of
--                 Lam t mtt bt -> do
--                   let hV = (Var h d)
--                   let tV = (Var t (d+1))
--                   let ctxWithHT      = extend (extend ctx h hV hT) t tV (Lst hT)
--                   let ctxWithConsHT  = (rewriteCtx (d+2) book x (Con hV tV) ctxWithHT)
--                   let bodyWithConsHT = (rewrite (d+2) book x (Con hV tV) (bt (Var t (d+1))))
--                   let goalWithConsHT = (rewrite (d+2) book x (Con hV tV) goal)
--                   checkAnn (d+2) span book ctxWithConsHT bodyWithConsHT goalWithConsHT
--                   Done term
--                 _ -> do
--                   checkAnn d span book ctx s (All hT (Lam "_" Nothing (\_ -> (All (Lst hT) (Lam "_" Nothing (\_ -> goal))))))
--                   Done term
--             _ -> do
--               checkAnn d span book ctx s (All hT (Lam "_" Nothing (\_ -> (All (Lst hT) (Lam "_" Nothing (\_ -> goal))))))
--               Done term
--         xT -> Fail $ TypeMismatch (getSpan span x) (normalCtx book ctx) (normal book (Lst (Var "_" 0))) (normal book xT) Nothing
--
--     (App (cut -> SigM g) x, _) -> do
--       xT <- case cut x of
--         Tup a b -> do
--           inferIndirect d span book ctx x term
--         _ -> do
--           xTinfer <- infer d span book ctx x
--           Done $ derefADT xTinfer
--             where
--               derefADT trm = case cut trm of
--                 Ref k i ->
--                   let xTbody = getDefn book k in
--                   case xTbody of
--                     Just (_, cut -> bod@(Sig (cut -> Enu _) _), _) -> bod
--                     _ -> trm
--                 _ -> trm
--
--       case cut $ normal book xT of
--         Sig aT bTFunc@(cut -> Lam y mty yb) -> do
--           case cut g of
--             Lam l mtl lb -> do
--               case cut (lb (Var l d)) of
--                 Lam r mtr rb -> do
--                   -- let lV = Var l d
--                   let lV = case cut x of
--                           Tup a b -> a
--                           _       -> Var l d
--                   -- let rV = Var r (d+1)
--                   let rV = case cut x of
--                           Tup a b -> b
--                           _       -> Var r (d+1)
--                   let tupV = Tup lV rV
--                   let bT = App bTFunc lV 
--                   let ctxWithPair = extend (extend ctx l lV aT) r rV bT
--                   let ctxRewritten  = rewriteCtx (d+2) book x tupV ctxWithPair
--                   let bodyRewritten = rewrite    (d+2) book x tupV $ rewrite (d+2) book (Var l d) lV (rb rV)
--                   -- let bodyRewritten = rewrite    (d+2) book x tupV (rb rV)
--                   let goalRewritten = rewrite    (d+2) book x tupV goal
--                   -- traceM $ "- STEP 2: " ++ show x ++ " -> " ++ show tupV
--                   -- traceM $ "\n- STEP 2: " ++ show (rb rV)  ++ " || " ++ show lV ++ " || " ++ show (Var l d) ++ " -> " ++ show bodyRewritten
--                   -- traceM $ "- STEP 2: " ++ show bodyRewritten ++ " ::?:: " ++ show goalRewritten ++ "\n-ctx rewritten: \n" ++ show ctxRewritten ++ "\n"
--                   checkAnn (d+2) span book ctxRewritten bodyRewritten goalRewritten
--                   Done term
--                 _ -> do
--                   let bT = App bTFunc (Var l d)
--                   checkAnn d span book ctx g (All aT (Lam l Nothing (\_ -> All bT (Lam "_" Nothing (\_ -> goal)))))
--                   Done term
--             _ -> do
--               verifyAnn d span book ctx term goal
--         _ -> do
--           verifyAnn d span book ctx term goal
--
--     (App (cut -> EnuM cs df) x, _) -> do
--       xT <- infer d span book ctx x
--       let doT = case cs of
--             []          -> Nothing
--             ((s,t):_)   -> case infer d span book ctx (Sym s) of
--               Done doT' -> Just doT'
--               _         -> Nothing
--       case (cut xT, doT) of
--         (Enu syms, Just (Enu syms')) | syms == syms' -> do
--               _ <- mapM_ (\(s, t) -> do
--                 checkAnn d span book (rewriteCtx d book x (Sym s) ctx) t (rewrite d book x (Sym s) goal)) cs
--               Done $ term
--         _ -> do
--           verifyAnn d span book ctx term goal
--     (term, _) -> do
--       let (fn, xs) = collectApps term []
--       if isLam fn then do
--         verifyAnn d span book ctx term goal
--       else do
--         verifyAnn d span book ctx term goal
--
--
--
reWrap :: Term -> Term -> Term
reWrap (Loc l _) z = Loc l z
reWrap (Chk x t) z = Chk z t
reWrap _        z = z

cutLoc :: Term -> Term
cutLoc (Loc l t) = t
cutLoc t         = t

isMatch :: Term -> Bool
isMatch (Loc _ f) = isLam f
isMatch EmpM      = True
isMatch UniM{}    = True
isMatch BitM{}    = True
isMatch NatM{}    = True
isMatch LstM{}    = True
isMatch EnuM{}    = True
isMatch SigM{}    = True
isMatch SupM{}    = True
isMatch EqlM{}    = True
isMatch _         = False

isVar :: Term -> Bool
isVar Var{} = True
isVar _     = False

split :: Int -> Int -> Term -> Term
split d aux term@(Log l t)    = Log (split d aux l) (split d aux t)
split d aux term@(Loc l t)    = Loc l (split d aux t)
split d aux term@(Lam k mt b) = Lam k mt (\x -> bindVarByName k x $ split (d+1) aux (b (Var k d)))
split d aux term@(App f x)    = 
  let f' = split d aux f
      x' = split d aux x
  in
  case cutLoc f' of
    (Chk f'' t) | isMatch (cut f'') && not (isVar $ cut x') -> Let ("$aux_" ++ show aux) (Just t) f'' (\v -> App v x')
    _                                                       -> App f' x' 
split d aux term              = term













