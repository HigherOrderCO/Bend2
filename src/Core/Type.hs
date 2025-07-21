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
  | CHAR_TO_U64
  deriving (Show, Eq)

-- Bend's Term Type
data Term
  -- Variables
  = Var Name Int -- x
  | Ref Name     -- x
  | Sub Term     -- x

  -- Definitions
  | Fix Name Body                   -- μx. f
  | Let Name (Maybe Term) Term Body -- !x : T = v; f

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
  | All Type Type              -- ∀A.B
  | Lam Name (Maybe Term) Body -- λx.f | λx:A . f
  | App Term Term              -- (f x)

  -- Equality
  | Eql Type Term Term -- T{a==b}
  | Rfl                -- {==}
  | EqlM Term Term     -- ~x{{==}:f}

  -- MetaVar
  | Met Name Type [Term] -- ?N:T{x0,x1,...}
  
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

  -- Logging
  -- NOTE: THIS IS A NEW PRIMITIVE (WIP)
  -- when the user writes:
  -- `log "foo" 123`
  -- the evaluator (whnf) will log "foo" to the screen, and return 123
  -- it will do so from Haskell-side by using Debug.Trace
  -- the first term must be a Char[]. the whnfLog function will normalize the
  -- Bend string layer by layer to convert to a Haskell string, and then print.
  -- if this fails (say, if ill-typed, or stuck), nothing will be printed.
  | Log Term Term -- log s ; x

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
  | Undefined Span Ctx Name
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
  show (Let k t v f)  = case t of
    Just t  -> "!" ++ k ++ " : " ++ show t ++ " = " ++ show v ++ ";" ++ show (f (Var k 0))
    Nothing -> "!" ++ k ++                    " = " ++ show v ++ ";" ++ show (f (Var k 0))
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
  show (Enu s)        = "enum{" ++ intercalate "," (map (\x -> "&" ++ x) s) ++ "}"
  show (Sym s)        = "&" ++ s
  show (EnuM x c e)   = "~ " ++ show x ++ " { " ++ intercalate " ; " (map (\(s,t) -> "&" ++ s ++ ": " ++ show t) c) ++ " ; " ++ show e ++ " }"
  show (Sig a b) = case b of
      Lam "_" t f -> showArg a ++ " & " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "Σ" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "Σ" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          Sig _ (Lam k _ _) | k /= "_" -> "(" ++ show t ++ ")"
          _                           -> show t
  show tup@(Tup _ _)  = fromMaybe ("(" ++ intercalate "," (map show (flattenTup tup)) ++ ")") (prettyCtr tup)
  show (SigM x f)     = "~ " ++ show x ++ " { (,):" ++ show f ++ " }"
  show (All a b) = case b of
      Lam "_" t f -> showArg a ++ " -> " ++ showCodomain (f (Var "_" 0))
      Lam k t f   -> "∀" ++ k ++ ":" ++ showArg a ++ ". " ++ show (f (Var k 0))
      _           -> "∀" ++ showArg a ++ ". " ++ show b
    where
      showArg t = case t of
          All{} -> "(" ++ show t ++ ")"
          Sig{} -> "(" ++ show t ++ ")"
          _     -> show t
      showCodomain t = case t of
          All _ (Lam k _ _) | k /= "_"  -> "(" ++ show t ++ ")"
          _                           -> show t
  show (Lam k t f)      = case t of
    Just t  -> "λ" ++ k ++ " : " ++ show t ++ " . " ++ show (f (Var k 0))
    Nothing -> "λ" ++ k ++ ". " ++ show (f (Var k 0))
  show app@(App _ _)  = fnStr ++ "(" ++ intercalate "," (map show args) ++ ")" where
           (fn, args) = collectApps app []
           fnStr      = case cut fn of
              Var k i -> show (Var k i)
              Ref k   -> show (Ref k)
              fn      -> "(" ++ show fn ++ ")"
  show (Eql t a b)     = case t of
    (Sig _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    (All _ _) -> "(" ++ show t ++ ")" ++ "{" ++ show a ++ "==" ++ show b ++ "}"
    _         ->        show t ++        "{" ++ show a ++ "==" ++ show b ++ "}"
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
  show (Met n t ctx)   = "?" ++ n ++ ":" ++ show t ++ "{" ++ intercalate "," (map show ctx) ++ "}"
  show (Log s x)       = "log " ++ show s ++ " " ++ show x
  show (Pri p)         = pri p where
    pri U64_TO_CHAR    = "U64_TO_CHAR"
    pri CHAR_TO_U64    = "CHAR_TO_U64"
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
  show (Undefined span ctx name) = 
    "\x1b[1mUndefined:\x1b[0m " ++ name ++
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
  go acc (Loc _ t)            = go acc t
  go acc (All t (Lam k ty f)) = go (acc ++ [(k, t)]) (f (Var k 0))
  go acc goal                 = (acc, goal)

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

-- | Returns the free variables in a term by name.
freeVars :: S.Set Name -> Term -> S.Set Name
freeVars ctx tm = case tm of
  Var n _     -> if n `S.member` ctx then S.empty else S.singleton n
  Sub t       -> freeVars ctx t
  Fix n f     -> freeVars (S.insert n ctx) (f (Var n 0))
  Let k t v f -> S.unions [foldMap (freeVars ctx) t, freeVars ctx v, freeVars (S.insert k ctx) (f (Var k 0))]
  Chk v t     -> S.union (freeVars ctx v) (freeVars ctx t)
  EmpM x      -> freeVars ctx x
  UniM x f    -> S.union (freeVars ctx x) (freeVars ctx f)
  BitM x f t  -> S.unions [freeVars ctx x, freeVars ctx f, freeVars ctx t]
  Suc n       -> freeVars ctx n
  NatM x z s  -> S.unions [freeVars ctx x, freeVars ctx z, freeVars ctx s]
  Lst t       -> freeVars ctx t
  Con h t     -> S.union (freeVars ctx h) (freeVars ctx t)
  LstM x n c  -> S.unions [freeVars ctx x, freeVars ctx n, freeVars ctx c]
  EnuM x c e  -> S.unions [freeVars ctx x, S.unions (map (freeVars ctx . snd) c), freeVars ctx e]
  Op2 _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  Op1 _ a     -> freeVars ctx a
  Sig a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Tup a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  SigM x f    -> S.union (freeVars ctx x) (freeVars ctx f)
  All a b     -> S.union (freeVars ctx a) (freeVars ctx b)
  Lam n t f   -> S.union (freeVars (S.insert n ctx) (f (Var n 0))) (foldMap (freeVars ctx) t)
  App f x     -> S.union (freeVars ctx f) (freeVars ctx x)
  Eql t a b   -> S.unions [freeVars ctx t, freeVars ctx a, freeVars ctx b]
  EqlM x f    -> S.union (freeVars ctx x) (freeVars ctx f)
  Met _ t c   -> S.unions (freeVars ctx t : map (freeVars ctx) c)
  Ind t       -> freeVars ctx t
  Frz t       -> freeVars ctx t
  Sup _ a b   -> S.union (freeVars ctx a) (freeVars ctx b)
  SupM x l f  -> S.unions [freeVars ctx x, freeVars ctx l, freeVars ctx f]
  Frk l a b   -> S.unions [freeVars ctx l, freeVars ctx a, freeVars ctx b]
  Log s x     -> S.union (freeVars ctx s) (freeVars ctx x)
  Loc _ t     -> freeVars ctx t
  Rwt a b x   -> S.unions [freeVars ctx a, freeVars ctx b, freeVars ctx x]
  Pat s m c   -> S.unions ((map (freeVars ctx) s) ++ (map (\(_,m) -> freeVars ctx m) m) ++ (map (\(_,c) -> freeVars ctx c) c))
  _           -> S.empty

-- | Check if a term contains a Metavar
hasMet :: Term -> Bool
hasMet term = case term of
  Met {} -> True
  Sub t -> hasMet t
  Fix _ f -> hasMet (f (Var "" 0))
  Let v f -> hasMet v || hasMet f
  Chk x t -> hasMet x || hasMet t
  EmpM x -> hasMet x
  UniM x f -> hasMet x || hasMet f
  BitM x f t -> hasMet x || hasMet f || hasMet t
  Suc n -> hasMet n
  NatM x z s -> hasMet x || hasMet z || hasMet s
  Lst t -> hasMet t
  Con h t -> hasMet h || hasMet t
  LstM x n c -> hasMet x || hasMet n || hasMet c
  EnuM x cs e -> hasMet x || any (hasMet . snd) cs || hasMet e
  Op2 _ a b -> hasMet a || hasMet b
  Op1 _ a -> hasMet a
  Sig a b -> hasMet a || hasMet b
  Tup a b -> hasMet a || hasMet b
  SigM x f -> hasMet x || hasMet f
  All a b -> hasMet a || hasMet b
  Lam _ t f -> maybe False hasMet t || hasMet (f (Var "" 0))
  App f x -> hasMet f || hasMet x
  Eql t a b -> hasMet t || hasMet a || hasMet b
  EqlM x f -> hasMet x || hasMet f
  Ind t -> hasMet t
  Frz t -> hasMet t
  Sup _ a b -> hasMet a || hasMet b
  SupM x l f -> hasMet x || hasMet l || hasMet f
  Loc _ t -> hasMet t
  Rwt a b x -> hasMet a || hasMet b || hasMet x
  Log s x -> hasMet s || hasMet x
  Pat s m c -> any hasMet s || any (hasMet . snd) m || any (\(p,b) -> any hasMet p || hasMet b) c
  Frk l a b -> hasMet l || hasMet a || hasMet b
  _ -> False
