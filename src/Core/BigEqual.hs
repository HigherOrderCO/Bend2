{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.BigEqual where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import Data.Maybe (fromMaybe, isNothing)
import Control.Applicative
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Type
import Core.WHNF
import Core.Show

import Debug.Trace

-- Equality
-- ========

equal :: Int -> Book -> Term -> Term -> Bool
equal d book a b =
  -- trace ("- equal: " ++ show (normal book a) ++ " == " ++ show (normal book b)) $
  eql True d book a b

eql :: Bool -> Int -> Book -> Term -> Term -> Bool
eql False d book a b = let res = cmp False d book (cut a) (cut b)
                        in
                          -- trace (if res then "- EQ: " ++ show a ++ " == " ++ show b else "- DIF: " ++ show a ++ " == " ++ show b)
                          res
eql True  d book a b = 
  if identical 
    then
      -- trace ("identic " ++ show a ++ " == " ++ show b) $
      True
    else if similar
      then 
        -- trace ("similar " ++ show a ++ " == " ++ show b) $
        -- trace ("similar " ++ show (force book a) ++ " ~~ " ++ show (force book b)) $
        True
      else 
        -- trace ("different " ++ show a ++ " != " ++ show b) $
        False
  where
    identical = eql False d book a b
    similar   = cmp True  d book (force book a) (force book b)

cmp :: Bool -> Int -> Book -> Term -> Term -> Bool
cmp red d book a b =
  let res = case (cut a , cut b) of
            (Fix ka fa      , Fix kb fb      ) -> eql red d book (fa (fb (Var ka d))) (fb (fa (Var kb d)))
            (Fix ka fa      , b              ) -> eql red d book (fa b) b
            (a              , Fix kb fb      ) -> eql red d book a (fb (Fix kb fb))
            (Ref ka ia      , Ref kb ib      ) -> ka == kb
            (Ref ka ia      , b              ) -> case getDefn book ka of { Just (_, term, _) -> eql red d book term b ; Nothing -> False }
            (a              , Ref kb ib      ) -> case getDefn book kb of { Just (_, term, _) -> eql red d book a term ; Nothing -> False }
            (Var ka ia      , Var kb ib      ) -> ia == ib
            (Sub ta         , Sub tb         ) -> eql red d book ta tb
            (Let ka ta va fa, Let kb tb vb fb) -> eql red d book va vb && eql red (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql red d book) ta tb)
            (Use ka va fa   , Use kb vb fb   ) -> eql red d book va vb && eql red d book (fa va) (fb vb)
            (Set            , Set            ) -> True
            (Chk xa ta      , Chk xb tb      ) -> eql red d book xa xb && eql red d book ta tb
            (Emp            , Emp            ) -> True
            (EmpM           , EmpM           ) -> True
            (Uni            , Uni            ) -> True
            (One            , One            ) -> True
            (UniM fa        , UniM fb        ) -> eql red d book fa fb
            -- new \/
            (UniM fa        , Lam kb mtb bb  ) -> eql red (d+1) book fa (bb (Var kb d)) && fromMaybe True (liftA2 (eql red d book) (Just Uni) mtb)
            (Lam ka mta ba  , UniM fb        ) -> eql red (d+1) book (ba (Var ka d)) fb && fromMaybe True (liftA2 (eql red d book) mta (Just Uni))

            (Bit            , Bit            ) -> True
            (Bt0            , Bt0            ) -> True
            (Bt1            , Bt1            ) -> True
            (BitM fa ta     , BitM fb tb     ) -> eql red d book fa fb && eql red d book ta tb
            -- new \/
            (BitM fa ta     , Lam kb mtb bb  ) -> eql red (d+1) book fa (bb (Var kb d)) && eql red (d+1) book ta (bb (Var kb d))
              && fromMaybe True (liftA2 (eql red d book) (Just Bit) mtb)
            (Lam ka mta ba  , BitM fb tb     ) -> eql red (d+1) book (ba (Var ka d)) fb && eql red (d+1) book (ba (Var ka d)) tb
              && fromMaybe True (liftA2 (eql red d book) mta (Just Bit))

            (Nat            , Nat            ) -> True
            (Zer            , Zer            ) -> True
            (Suc na         , Suc nb         ) -> eql red d book na nb
            (NatM za sa     , NatM zb sb     ) -> eql red d book za zb && eql red d book sa sb
            -- new \/
            (NatM za sa     , Lam kb mtb bb  ) -> eql red (d+1) book za (bb (Var kb d)) && eql red (d+1) book sa (bb (Var kb d))
              && fromMaybe True (liftA2 (eql red d book) (Just Nat) mtb)
            (Lam ka mta ba  , NatM zb sb     ) -> eql red (d+1) book (ba (Var ka d)) zb && eql red (d+1) book (ba (Var ka d)) sb
              && fromMaybe True (liftA2 (eql red d book) mta (Just Nat))

            (Lst ta         , Lst tb         ) -> eql red d book ta tb
            (Nil            , Nil            ) -> True
            (Con ha ta      , Con hb tb      ) -> eql red d book ha hb && eql red d book ta tb
            (LstM na ca     , LstM nb cb     ) -> eql red d book na nb && eql red d book ca cb
            (Enu sa         , Enu sb         ) -> sa == sb
            (Sym sa         , Sym sb         ) -> sa == sb
            (EnuM ca da     , EnuM cb db     ) -> length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql red d book t1 t2) (zip ca cb) && case (da,db) of
              (Nothing, Nothing)   -> True
              (Just dat, Just dbt) -> eql red d book dat dbt
              _                    -> False
            (Sig aa ba      , Sig ab bb      ) -> eql red d book aa ab && eql red d book ba bb
            (Tup aa ba      , Tup ab bb      ) -> eql red d book aa ab && eql red d book ba bb
            (SigM fa        , SigM fb        ) -> eql red d book fa fb
            (All aa ba      , All ab bb      ) -> eql red d book aa ab && eql red d book ba bb
            (Lam ka ta fa   , Lam kb tb fb   ) -> eql red (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql red d book) ta tb)

            (App (cut -> Lam ka mta ba) (cut -> xa), _) | not (isLamApp b) ->
              eql red d book a (App (Lam ka mta (\_ -> b)) xa)
            (_, App (cut -> Lam kb mtb bb) (cut -> xb)) | not (isLamApp a) ->
              eql red d book (App (Lam kb mtb (\_ -> a)) xb) b
            
            (App (cut -> UniM f) (cut -> xa), _) | not (isUniMApp b) ->
              eql red d book a (App (UniM b) xa)
            (_, App (cut -> UniM f) (cut -> xb)) | not (isUniMApp a) ->
              eql red d book (App (UniM b) xb) b

            -- (App (cut -> BitM f t) (cut -> xa), _) | not (isBitMApp b) ->
            --   eql red d book a (App (BitM b b) xa)
            -- (_, App (cut -> BitM f t) (cut -> xb)) | not (isBitMApp b) ->
            --   eql red d book (App (BitM a a) xb) b

            (App (cut -> NatM s (cut -> Lam p mtp pb)) (cut -> xa), _) | not (isNatMApp b) ->
              eql red d book a (App (NatM b (Lam p mtp (\_ -> b))) xa)

            (App (cut -> LstM s c) xa, _) | not (isLstMApp b) ->
              eql red d book a (App (LstM b (Lam "_" Nothing (\_ -> Lam "_" Nothing (\_ -> b)))) xa)
            --
            -- (_, App (cut -> LstM s (cut -> Lam h mth hb)) (cut -> xb)) | not (isLstMApp a) ->
            --   eql red d book (App (LstM a (Lam "_" Nothing (\_ -> Lam "_" Nothing (\_ -> a)))) xb) b

              -- case cut (hb (Var h d)) of
              --   Lam t mtt tb ->
              -- eql red d book a (App (NatM b (Lam p mtp (\_ -> b))) xa)

            -- (App (cut -> SigM g) (cut -> xa), (cut -> b)) | not (isSigMApp b) ->
            --   case cut g of
            --     Lam ka mta ba -> case cut (ba (Var ka d)) of
            --       Lam kb mtb bb -> eql red d book a (App (SigM (Lam ka mta (\_ -> Lam kb mtb (\_ -> b)))) xa)
            --       _ -> False
            --     _ -> False
            
            -- (App (cut -> EnuM cs Nothing) (cut -> xa), (cut -> b)) | not (isEnuMApp b) ->
            --   eql red d book a (App (EnuM (map (\(label, _) -> (label, b)) cs) Nothing) xa)
            
            (App (cut -> EnuM cs Nothing) (cut -> xa), (cut -> b)) | not (isEnuMApp b) ->
              let replaceInnermost term = case cut term of
                    Sig ty (Lam k mt body) -> Sig ty (Lam k mt (\x -> replaceInnermost (body x)))
                    _ -> b
                  newClauses = map (\(label, body) -> (label, replaceInnermost body)) cs
              in eql red d book a (App (EnuM newClauses Nothing) xa)

            (App fa xa, App fb xb) -> eql red d book fa fb && eql red d book xa xb
            (Eql ta aa ba   , Eql tb ab bb   ) -> eql red d book ta tb && eql red d book aa ab && eql red d book ba bb
            -- (Eql ta _  _  , b            ) -> eql red d book ta b
            -- (a            , Eql tb _  _  ) -> eql red d book a tb
            (Rfl            , Rfl            ) -> True
            (Rwt ea fa      , Rwt eb fb      ) -> eql red d book ea eb && eql red d book fa fb
            (Loc _ ta       , b              ) -> eql red d book ta b
            (a              , Loc _ tb       ) -> eql red d book a tb
            (Era            , Era            ) -> True
            (Sup la aa ba   , Sup lb ab bb   ) -> eql red d book la lb && eql red d book aa ab && eql red d book ba bb
            (SupM la fa     , SupM lb fb     ) -> eql red d book la lb && eql red d book fa fb
            (Frk la aa ba   , Frk lb ab bb   ) -> eql red d book la lb && eql red d book aa ab && eql red d book ba bb
            (Num ta         , Num tb         ) -> ta == tb
            (Val va         , Val vb         ) -> va == vb
            (Op2 oa aa ba   , Op2 ob ab bb   ) -> oa == ob && eql red d book aa ab && eql red d book ba bb
            (Op1 oa aa      , Op1 ob ab      ) -> oa == ob && eql red d book aa ab
            (Pri pa         , Pri pb         ) -> pa == pb
            (Met _  _  _    , Met _  _  _    ) -> error "not-supported"
            (Pat _  _  _    , Pat _  _  _    ) -> error "not-supported"
            (_              , _              ) -> False
  in
    -- trace ("- cmp: " ++ show a ++ " == " ++ show b ++ " -> " ++ show res)
    if
      res
    then
      res
    else 
      -- trace ("- cmp: " ++ show a ++ " == " ++ show b ++ " -> " ++ show res)
      res

isLamApp :: Term -> Bool
isLamApp (cut -> App (cut -> Lam _ _ _) _) = True
isLamApp _ = False

isUniMApp :: Term -> Bool
isUniMApp (cut -> App (cut -> UniM _) _) = True
isUniMApp _ = False

isBitMApp :: Term -> Bool
isBitMApp (cut -> App (cut -> BitM _ _) _) = True
isBitMApp _ = False

isNatMApp :: Term -> Bool
isNatMApp (cut -> App (cut -> NatM _ _) _) = True
isNatMApp _ = False

isLstMApp :: Term -> Bool
isLstMApp (cut -> App (cut -> LstM _ _) _) = True
isLstMApp _ = False

isSigMApp :: Term -> Bool
isSigMApp (cut -> App (cut -> SigM _) _) = True
isSigMApp _ = False

isEnuMApp :: Term -> Bool
isEnuMApp (cut -> App (cut -> EnuM _ Nothing) _) = True
isEnuMApp _ = False
