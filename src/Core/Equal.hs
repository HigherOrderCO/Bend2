{-./Type.hs-}

{-# LANGUAGE ViewPatterns #-}

module Core.Equal where

import System.IO.Unsafe
import Data.IORef
import Data.Bits
import Data.Maybe (fromMaybe, isNothing)
import Control.Applicative
import GHC.Float (castDoubleToWord64, castWord64ToDouble)

import Core.Type
import Core.WHNF

import Debug.Trace

-- Equality
-- ========

equal :: Int -> Book -> Term -> Term -> Bool
equal d book a b = eql 3 d book a b

eql :: Int -> Int -> Book -> Term -> Term -> Bool
eql 0  d book a b = cmp 0 d book (cut a) (cut b)
eql lv d book a b = identical || similar where
  identical = eql 0 d book a b
  similar   = cmp lv d book (force book a) (force book b)

cmp :: Int -> Int -> Book -> Term -> Term -> Bool
cmp lv d book a b =
  case (a , b) of
    (Fix ka fa      , Fix kb fb      ) -> eql lv d book (fa (fb (Var ka d))) (fb (fa (Var kb d)))
    (Fix ka fa      , b              ) -> eql lv d book (fa b) b
    (a              , Fix kb fb      ) -> eql lv d book a (fb (Fix kb fb))
    (Ref ka         , Ref kb         ) -> ka == kb
    (Ref ka         , b              ) -> case deref book ka of { Just (_, term, _) -> eql lv d book term b ; Nothing -> False }
    (a              , Ref kb         ) -> case deref book kb of { Just (_, term, _) -> eql lv d book a term ; Nothing -> False }
    (Var ka ia      , Var kb ib      ) -> ia == ib
    (Sub ta         , Sub tb         ) -> eql lv d book ta tb
    (Let ka ta va fa, Let kb tb vb fb) -> eql lv d book va vb && eql lv (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql lv d book) ta tb)
    (Set            , Set            ) -> True
    (Chk xa ta      , Chk xb tb      ) -> eql lv d book xa xb && eql lv d book ta tb
    (Emp            , Emp            ) -> True
    (EmpM xa        , EmpM xb        ) -> eql lv d book xa xb
    (Uni            , Uni            ) -> True
    (One            , One            ) -> True
    (UniM xa fa     , UniM xb fb     ) -> eql lv d book xa xb && eql lv d book fa fb
    (Bit            , Bit            ) -> True
    (Bt0            , Bt0            ) -> True
    (Bt1            , Bt1            ) -> True
    (BitM xa fa ta  , BitM xb fb tb  ) -> eql lv d book xa xb && eql lv d book fa fb && eql lv d book ta tb
    (Nat            , Nat            ) -> True
    (Zer            , Zer            ) -> True
    (Suc na         , Suc nb         ) -> eql lv d book na nb
    (NatM xa za sa  , NatM xb zb sb  ) -> eql lv d book xa xb && eql lv d book za zb && eql lv d book sa sb
    (Lst ta         , Lst tb         ) -> eql lv d book ta tb
    (Nil            , Nil            ) -> True
    (Con ha ta      , Con hb tb      ) -> eql lv d book ha hb && eql lv d book ta tb
    (LstM xa na ca  , LstM xb nb cb  ) -> eql lv d book xa xb && eql lv d book na nb && eql lv d book ca cb
    (Enu sa         , Enu sb         ) -> sa == sb
    (Sym sa         , Sym sb         ) -> sa == sb
    (EnuM xa ca da  , EnuM xb cb db  ) -> eql lv d book xa xb && length ca == length cb && all (\ ((s1,t1), (s2,t2)) -> s1 == s2 && eql lv d book t1 t2) (zip ca cb) && eql lv d book da db
    (Sig aa ba      , Sig ab bb      ) -> eql lv d book aa ab && eql lv d book ba bb
    (Tup aa ba      , Tup ab bb      ) -> eql lv d book aa ab && eql lv d book ba bb
    (SigM xa fa     , SigM xb fb     ) -> eql lv d book xa xb && eql lv d book fa fb
    (All aa ba      , All ab bb      ) -> eql lv d book aa ab && eql lv d book ba bb
    (Lam ka ta fa   , Lam kb tb fb   ) -> eql lv (d+1) book (fa (Var ka d)) (fb (Var kb d)) && fromMaybe True (liftA2 (eql lv d book) ta tb)
    (App fa xa      , App fb xb      ) -> eql lv d book fa fb && eql lv d book xa xb
    (Eql ta aa ba   , Eql tb ab bb   ) -> eql lv d book ta tb && eql lv d book aa ab && eql lv d book ba bb
    -- (Eql ta _  _  , b            ) -> eql lv d book ta b
    -- (a            , Eql tb _  _  ) -> eql lv d book a tb
    (Rfl            , Rfl            ) -> True
    (EqlM xa fa     , EqlM xb fb     ) -> eql lv d book xa xb && eql lv d book fa fb
    (Ind ta         , b              ) -> eql lv d book ta b
    (a              , Ind tb         ) -> eql lv d book a tb
    (Frz ta         , b              ) -> eql lv d book ta b
    (a              , Frz tb         ) -> eql lv d book a tb
    (Loc _ ta       , b              ) -> eql lv d book ta b
    (a              , Loc _ tb       ) -> eql lv d book a tb
    (Rwt _ _ xa     , _              ) -> eql lv d book xa b
    (_              , Rwt _ _ xb     ) -> eql lv d book a xb
    (Era            , Era            ) -> True
    (Sup la aa ba   , Sup lb ab bb   ) -> eql lv d book la lb && eql lv d book aa ab && eql lv d book ba bb
    (SupM xa la fa  , SupM xb lb fb  ) -> eql lv d book xa xb && eql lv d book la lb && eql lv d book fa fb
    (Frk la aa ba   , Frk lb ab bb   ) -> eql lv d book la lb && eql lv d book aa ab && eql lv d book ba bb
    (Num ta         , Num tb         ) -> ta == tb
    (Val va         , Val vb         ) -> va == vb
    (Op2 oa aa ba   , Op2 ob ab bb   ) -> oa == ob && eql lv d book aa ab && eql lv d book ba bb
    (Op1 oa aa      , Op1 ob ab      ) -> oa == ob && eql lv d book aa ab
    (Pri pa         , Pri pb         ) -> pa == pb
    (Met _  _  _    , Met _  _  _    ) -> error "not-supported"
    (Pat _  _  _    , Pat _  _  _    ) -> error "not-supported"
    (_              , _              ) -> False
