{-# LANGUAGE ViewPatterns #-}

module Core.Type where

import Data.List (intercalate)
import Debug.Trace
import Highlight (highlightError)
import Data.Int (Int32, Int64)
import Data.Word (Word32, Word64)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S

data Bits = O Bits | I Bits | E deriving Show
type Name = String
type Body = Term -> Term
type Case = ([Term], Term)
type Move = (String, Term)
type Type = Term

data NTyp
  = U64_T
  | I64_T
  | F64_T
  | CHR_T
  deriving (Show, Eq)

data NVal
  = U64_V Word64
  | I64_V Int64
  | F64_V Double
  | CHR_V Char
  deriving (Show, Eq)

data NOp2
  = ADD | SUB | MUL | DIV | MOD | POW
  | EQL | NEQ  
  | LST | GRT | LEQ | GEQ
  | AND | OR  | XOR
  | SHL | SHR
  deriving (Show, Eq)

data NOp1
  = NOT | NEG
  deriving (Show, Eq)

data PriF
  = U64_TO_CHAR
  deriving (Show, Eq)

-- Bend's Term Type
data Term
  -- Variables
  = Var Name Int -- x
  | Ref Name     -- x
  | Sub Term     -- x

  -- Definitions
  | Fix Name Body -- μx. f
  | Let Term Term -- !v; f

  -- Universe
  | Set -- Set

  -- Annotation
  | Chk Term Type -- x::t

  -- Empty
  | Emp       -- Empty
  | EmpM Term -- ~x{}

  -- Unit
  | Uni            -- Unit
  | One            -- ()
  | UniM Term Term -- ~x{():f}

  -- Bool
  | Bit                 -- Bool
  | Bt0                 -- False
  | Bt1                 -- True
  | BitM Term Term Term -- ~x{False:t;True:t}

  -- Nat
  | Nat                 -- Nat
  | Zer                 -- 0
  | Suc Term            -- ↑n
  | NatM Term Term Term -- ~x{0n:z;1n+:s}

  -- List
  | Lst Type            -- T[]
  | Nil                 -- []
  | Con Term Term       -- h<>t
  | LstM Term Term Term -- ~x{[]:n;<>:c}

  -- Enum
  | Enu [String]                   -- {@foo,@bar...}
  | Sym String                     -- @foo
  | EnuM Term [(String,Term)] Term -- ~x{@foo:f;@bar:b;...d}

  -- Numbers
  | Num NTyp           -- CHR | U64 | I64 | F64
  | Val NVal           -- 123 | +123 | +123.0
  | Op2 NOp2 Term Term -- x + y
  | Op1 NOp1 Term      -- !x

  -- Pair
  | Sig Type Type       -- ΣA.B
  | Tup Term Term       -- (a,b)
  | SigM Term Term      -- ~x{(,):f}

  -- Function
  | All Type Type -- ∀A.B
  | Lam Name Body -- λx.f
  | App Term Term -- (f x)

  -- Equality
  | Eql Type Term Term -- T{a==b}
  | Rfl                -- {==}
  | EqlM Term Term     -- ~x{{==}:f}

  -- MetaVar
  | Met Int Type [Term] -- ?N:T{x0,x1,...}
  
  -- Hints
  | Ind Type -- ~~T
  | Frz Type -- ∅T

  -- Supperpositions
  | Era                 -- *
  | Sup Term Term Term  -- &L{a,b}
  | SupM Term Term Term -- ~x{&L{,}:f}

  -- Errors
  | Loc Span Term -- x
  | Rwt Term Term Term -- a → b ; x

  -- Primitive
  | Pri PriF -- SOME_FUNC

  -- Sugars
  | Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
  | Frk Term Term Term       -- fork L:a else:b

-- Book of Definitions
type Inj  = Bool -- "is injective" flag. improves pretty printing
type Defn = (Inj, Term, Type)
data Book = Book (M.Map Name Defn)

-- Substitution Map
type Subs = [(Term,Term)]

-- Context (new type)
data Ctx = Ctx [(Name,Term,Term)]

-- Error Location (NEW TYPE)
data Span = Span
  { spanBeg :: (Int,Int)
  , spanEnd :: (Int,Int)
  , spanSrc :: String -- original file
  }

data Error
  = CantInfer Span Ctx
  | TypeMismatch Span Ctx Term Term
  | TermMismatch Span Ctx Term Term
  | IncompleteMatch Span Ctx

data Result a
  = Done a
  | Fail Error

instance Functor Result where
  fmap f (Done a) = Done (f a)
  fmap _ (Fail e) = Fail e

instance Applicative Result where
  pure              = Done
  Done f <*> Done a = Done (f a)
  Fail e <*> _      = Fail e
  _      <*> Fail e = Fail e

instance Monad Result where
  Done a >>= f = f a
  Fail e >>= _ = Fail e

instance Show Term where
  show (Var k i)      = k -- ++ "^" ++ show i
  show (Ref k)        = k
  show (Sub t)        = show t
  show (Fix k f)      = "μ" ++ k ++ ". " ++ show (f (Var k 0))
  show (Let v f)      = "!" ++ show v ++ ";" ++ show f
  show (Set)          = "Set"
  show (Chk x t)      = "(" ++ show x ++ "::" ++ show t ++ ")"
  show (Emp)          = "Empty"
  show (EmpM x)       = "~" ++ show x ++ "{}"
  show (Uni)          = "Unit"
  show (One)          = "()"
  show (UniM x f)     = "~ " ++ show x ++ " { (): " ++ show f ++ " }"
  show (Bit)          = "Bool"
  show (Bt0)          = "False"
  show (Bt1)          = "True"
  show (BitM x f t)   = "~ " ++ show x ++ " { False: " ++ show f ++ " ; True: " ++ show t ++ " }"
  show (Nat)          = "Nat"
  show (Zer)          = "0n"
  show (Suc n)        = "1n+" ++ show n
  show (NatM x z s)   = "~ " ++ show x ++ " { 0n: " ++ show z ++ " ; 1n+: " ++ show s ++ " }"
  show (Lst t)        = show t ++ "[]"
  show (Nil)          = "[]"
  show (Con h t)      = fromMaybe (show h ++ "<>" ++ show t) (prettyStr (Con h t))
  show (LstM x n c)   = "~ " ++ show x ++ " { []:" ++ show n ++ " ; <>:" ++ show c ++ " }"
  show (Enu s)        = "&{" ++ intercalate "," (map (\x -> "&" ++ x) s) ++ "}"
  show (Sym s)        = "&" ++ s
  show (EnuM x c e)   = "~ " ++ show x ++ " { " ++ intercalate " ; " (map (\(s,t) -> "&" ++ s ++ ": " ++ show t) c) ++ " ; " ++ show e ++ " }"
  show (Sig a b)      = sig a b where
    sig a (Lam "_" f) = show a ++ "&" ++ show (f (Var "_" 0))
    sig a (Lam k f)   = "Σ" ++ k ++ ":" ++ show a ++ ". " ++ (show (f (Var k 0)))
    sig a b           = "Σ" ++ show a ++ ". " ++ (show b)
  show tup@(Tup _ _)  = fromMaybe ("(" ++ intercalate "," (map show (flattenTup tup)) ++ ")") (prettyCtr tup)
  show (SigM x f)     = "~ " ++ show x ++ " { (,):" ++ show f ++ " }"
  show (All a b) = case b of
      Lam "_" f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" 0))
      Lam k   f -> "∀" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _         -> "∀" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case t of
          All{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          All _ (Lam k _) | k /= "_"  -> "(" ++ show t ++ ")"
          _                           -> show t
  show (Lam k f)      = "λ" ++ k ++ ". " ++ show (f (Var k 0))
  show app@(App _ _)  = fnStr ++ "(" ++ intercalate "," (map show args) ++ ")" where
           (fn, args) = collectApps app []
           fnStr      = case cut fn of
              Var k i -> show (Var k i)
              Ref k   -> show (Ref k)
              fn      -> "(" ++ show fn ++ ")"
  show (Eql t a b)     = show t ++ "{" ++ show a ++ "==" ++ show b ++ "}"
  show (Rfl)           = "{==}"
  show (EqlM x f)      = "~ " ++ show x ++ " { {==}:" ++ show f ++ " }"
  show (Ind t)         = "~~ {" ++ show t ++ "}"
  show (Frz t)         = "∅" ++ show t
  show (Loc _ t)       = show t
  show (Rwt a b x)     = show a ++ " ⇒ " ++ show b ++ "; " ++ show x
  show (Era)           = "*"
  show (Sup l a b)     = "&" ++ show l ++ "{" ++ show a ++ "," ++ show b ++ "}"
  show (SupM x l f)    = "~ " ++ show x ++ " { &" ++ show l ++ "{,}:" ++ show f ++ " }"
  show (Frk l a b)     = "fork " ++ show l ++ ":" ++ show a ++ " else:" ++ show b
  show (Met _ _ _)     = "?"
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
  show (Num U64_T)     = "U64"
  show (Num I64_T)     = "I64"
  show (Num F64_T)     = "F64"
  show (Num CHR_T)     = "Char"
  show (Val (U64_V n)) = show n
  show (Val (I64_V n)) = if n >= 0 then "+" ++ show n else show n
  show (Val (F64_V n)) = show n
  show (Val (CHR_V c)) = "'" ++ showChar c ++ "'" where
         showChar '\n' = "\\n"
         showChar '\t' = "\\t"
         showChar '\r' = "\\r"
         showChar '\0' = "\\0"
         showChar '\\' = "\\\\"
         showChar '\'' = "\\'"
         showChar c    = [c]
  show (Op2 ADD a b)   = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (Op2 SUB a b)   = "(" ++ show a ++ " - " ++ show b ++ ")"
  show (Op2 MUL a b)   = "(" ++ show a ++ " * " ++ show b ++ ")"
  show (Op2 DIV a b)   = "(" ++ show a ++ " / " ++ show b ++ ")"
  show (Op2 MOD a b)   = "(" ++ show a ++ " % " ++ show b ++ ")"
  show (Op2 EQL a b)   = "(" ++ show a ++ " == " ++ show b ++ ")"
  show (Op2 NEQ a b)   = "(" ++ show a ++ " !== " ++ show b ++ ")"
  show (Op2 LST a b)   = "(" ++ show a ++ " < " ++ show b ++ ")"
  show (Op2 GRT a b)   = "(" ++ show a ++ " > " ++ show b ++ ")"
  show (Op2 LEQ a b)   = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Op2 GEQ a b)   = "(" ++ show a ++ " >= " ++ show b ++ ")"
  show (Op2 AND a b)   = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Op2 OR a b)    = "(" ++ show a ++ " | " ++ show b ++ ")"
  show (Op2 XOR a b)   = "(" ++ show a ++ " ^ " ++ show b ++ ")"
  show (Op2 SHL a b)   = "(" ++ show a ++ " << " ++ show b ++ ")"
  show (Op2 SHR a b)   = "(" ++ show a ++ " >> " ++ show b ++ ")"
  show (Op2 POW a b)   = "(" ++ show a ++ " ** " ++ show b ++ ")"
  show (Op1 NOT a)     = "(not " ++ show a ++ ")"
  show (Op1 NEG a)     = "(-" ++ show a ++ ")"
  show (Pat t m c)     = "match " ++ unwords (map show t) ++ " {" ++ showMoves ++ showCases ++ " }" where
             showMoves = if null m then "" else " with " ++ intercalate " with " (map mv m) where
               mv(k,x) = k ++ "=" ++ show x
             showCases = if null c then "" else " " ++ intercalate " " (map cs c) where
               cs(p,x) = "case " ++ unwords (map showPat p) ++ ": " ++ show x
             showPat p = "(" ++ show p ++ ")"

instance Show Book where
  show (Book defs) = unlines (map defn (M.toList defs))
    where defn (k,(_,x,t)) = k ++ " : " ++ show t ++ " = " ++ show x

instance Show Span where
  show span = "\n\x1b[1mLocation:\x1b[0m "
    ++ "\x1b[2m(line "++show (fst $ spanBeg span)++ ", column "++show (snd $ spanBeg span)++")\x1b[0m\n"
    ++ highlightError (spanBeg span) (spanEnd span) (spanSrc span)

instance Show Error where
  show (CantInfer span ctx) = 
    "\x1b[1mCantInfer:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TypeMismatch span ctx goal typ) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- Goal: " ++ show goal ++ 
    "\n- Type: " ++ show typ ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (TermMismatch span ctx a b) = 
    "\x1b[1mMismatch:\x1b[0m" ++
    "\n- " ++ show a ++ 
    "\n- " ++ show b ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span
  show (IncompleteMatch span ctx) = 
    "\x1b[1mIncompleteMatch:\x1b[0m" ++
    "\n\x1b[1mContext:\x1b[0m\n" ++ show ctx ++
    show span

instance Show Ctx where
  show (Ctx ctx)
    | null lines = ""
    | otherwise  = init (unlines lines)
    where
      lines = map snd (reverse (clean S.empty (reverse (map showAnn ctx))))

      showAnn :: (Name,Term,Term) -> (Name,String)
      showAnn (k,_,t) = (k, "- " ++ k ++ " : " ++ show t)
    
      clean :: S.Set Name -> [(Name,String)] -> [(Name,String)]
      clean _    []                             = []
      clean seen ((n,l):xs) | n `S.member` seen = clean seen xs
                            | take 1 n == "_"   = clean seen xs
                            | otherwise         = (n,l) : clean (S.insert n seen) xs

-- Utils
-- -----

deref :: Book -> Name -> Maybe Defn
deref (Book defs) name = M.lookup name defs

cut :: Term -> Term
cut (Loc _ t) = cut t
cut (Chk x _) = cut x
cut t         = t

unlam :: Name -> Int -> (Term -> Term) -> Term
unlam k d f = f (Var k d)

collectArgs :: Term -> ([(String, Term)], Term)
collectArgs = go [] where
  go acc (Loc _ t)         = go acc t
  go acc (All t (Lam k f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal              = (acc, goal)

collectApps :: Term -> [Term] -> (Term, [Term])
collectApps (cut -> App f x) args = collectApps f (x:args)
collectApps f                args = (f, args)

noSpan :: Span
noSpan = Span (0,0) (0,0) ""

flattenTup :: Term -> [Term]
flattenTup (Tup l r) = l : flattenTup r
flattenTup t         = [t]

lastElem :: Term -> Maybe Term
lastElem (Tup _ r) = lastElem r
lastElem t         = Just t

prettyCtr :: Term -> Maybe String
prettyCtr (Tup (Sym name) rest) = 
  case lastElem rest of
    Just One -> Just ("@" ++ name ++ "{" ++ intercalate "," (map show (init (flattenTup rest))) ++ "}")
    _        -> Nothing
prettyCtr _ = Nothing

prettyStr :: Term -> Maybe String
prettyStr = go [] where
  go :: [Char] -> Term -> Maybe String
  go acc Nil                        = Just ("\"" ++ reverse acc ++ "\"")
  go acc (Con (Val (CHR_V c)) rest) = go (c:acc) rest
  go acc (Loc _ t)                  = go acc t
  go _   _                          = Nothing
