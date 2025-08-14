{-# LANGUAGE MultilineStrings #-}

import Test

matches :: String
matches = """
# f functions - Single argument, single pattern match on each type
# Tests basic pattern matching for each type in the language
def f1(u: Unit) -> Unit:
  match u:
    case (): ()

def f2(b: Bool) -> Unit:
  match b:
    case False: ()
    case True: ()

def f3(n: Nat) -> Nat:
  match n:
    case 0n: n
    case 1n+p: 1n+n

def f4(e: Empty) -> Nat:
  match e:

def f5(l: Bool[]) -> Nat:
  match l:
    case []: 0n
    case h <> t: 1n

def f6(p: Bool & Nat) -> Nat:
  match p:
    case (a,b): 0n

def f7(eq: Nat{0n == 0n}) -> Nat:
  match eq:
    case {==}: 0n

# Custom algebraic data types
type Boolean():
  case @Tr:
  case @Fl:

def f8(b: Boolean) -> Unit:
  match b:
    case @Tr: ()
    case @Fl: ()

type Nats():
  case @Zero:
  case @Succ: p : Nats

def f9(m : Nats) -> Unit:
  match m:
    case @Zero: ()
    case @Succ{p}: ()

# # h functions - Two arguments, single pattern match on one argument
# # Tests argument order permutations with one pattern match
# # Unit and Bool combinations
def h1(u: Unit, b: Bool) -> Unit:
  match u:
    case (): ()

def h2(u: Unit, b: Bool) -> Unit:
  match b:
    case False: ()
    case True: ()

def h3(b: Bool, u: Unit) -> Unit:
  match u:
    case (): ()

def h4(b: Bool, u: Unit) -> Unit:
  match b:
    case False: ()
    case True: ()

# Nat and Bool combinations
def h5(n: Nat, b: Bool) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: 1n

def h6(b: Bool, n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+p: 1n

# Empty and Bool combinations
def h7(e: Empty, b: Bool) -> Nat:
  match e:

def h8(b: Bool, e: Empty) -> Nat:
  match e:

# List and Bool combinations
def h9(l: Bool[], b: Bool) -> Nat:
  match l:
    case []: 0n
    case h <> t: 1n

def h10(b: Bool, l: Bool[]) -> Nat:
  match l:
    case []: 0n
    case h <> t: 1n

# Pair and Bool combinations
def h11(p: Bool & Nat, b: Bool) -> Nat:
  match p:
    case (a,b): 0n

def h12(b: Bool, p: Bool&Nat) -> Nat:
  match p:
    case (a,b): 0n


# Equality type and Bool combinations
def h13(eq: Nat{0n == 0n}, b: Bool) -> Nat:
  match eq:
     case {==}: 0n

def h14(b: Bool, eq: Nat{0n == 0n}) -> Nat:
  match eq:
    case {==}: 0n

# Boolean ADT and Bool combinations
def h15(bo: Boolean, b: Bool) -> Unit:
  match bo:
    case @Tr: ()
    case @Fl: ()

def h16(b: Bool, bo: Boolean) -> Unit:
  match bo:
    case @Tr: ()
    case @Fl: ()

# Nats ADT and Bool combinations
def h17(m: Nats, b: Bool) -> Unit:
  match m:
    case @Zero: ()
    case @Succ{p}: ()

def h18(b: Bool, m: Nats) -> Unit:
  match m:
    case @Zero: ()
    case @Succ{p}: ()

# # i functions - Two arguments, nested pattern matches
# # Tests all permutations of argument order and match nesting

# Unit and Bool - all 4 permutations of argument and match order
def i1(u: Unit, b: Bool) -> Unit:
  match u:
    case ():
      match b:
        case False: ()
        case True: ()

def i2(b: Bool, u: Unit) -> Unit:
  match u:
    case ():
      match b:
        case False: ()
        case True: ()

def i3(b: Bool, u: Unit) -> Unit:
  match b:
    case False:
      match u:
        case (): ()
    case True:
      match u:
        case (): ()

def i4(u: Unit, b: Bool) -> Unit:
  match b:
    case False:
      match u:
        case (): ()
    case True:
      match u:
        case (): ()

# Pair with Unit - matching on pair then component
def i5(p: Unit & Unit) -> Unit:
  match p:
    case (a,b):
      match a:
        case (): ()

# Nat and Unit combinations
def i6(n: Nat, u: Unit) -> Unit:
  match n:
    case 0n:
      match u:
        case (): ()
    case 1n+p:
      match u:
        case (): ()

def i7(u: Unit, n: Nat) -> Unit:
  match n:
    case 0n:
      match u:
        case (): ()
    case 1n+p:
      match u:
        case (): ()

# Nat and Bool combinations
def i8(n: Nat, b: Bool) -> Unit:
  match n:
    case 0n:
      match b:
        case False: ()
        case True: ()
    case 1n+p:
      match b:
        case False: ()
        case True: ()

def i9(b: Bool, n: Nat) -> Unit:
  match n:
    case 0n:
      match b:
        case False: ()
        case True: ()
    case 1n+p:
      match b:
        case False: ()
        case True: ()

# List and Unit combinations
def i10(l: Bool[], u: Unit) -> Unit:
  match l:
    case []:
      match u:
        case (): ()
    case h <> t:
      match u:
        case (): ()

def i11(u: Unit, l: Bool[]) -> Unit:
  match l:
    case []:
      match u:
        case (): ()
    case h <> t:
      match u:
        case (): ()

# List and Bool combinations
def i12(l: Bool[], b: Bool) -> Unit:
  match l:
    case []:
      match b:
        case False: ()
        case True: ()
    case h <> t:
      match b:
        case False: ()
        case True: ()

def i13(b: Bool, l: Bool[]) -> Unit:
  match l:
    case []:
      match b:
        case False: ()
        case True: ()
    case h <> t:
      match b:
        case False: ()
        case True: ()

# Pair and Unit combinations
def i14(p: Bool & Nat, u: Unit) -> Unit:
  match p:
    case (a,b):
      match u:
        case (): ()

def i15(u: Unit, p: Bool&Nat) -> Unit:
  match p:
    case (a,b):
      match u:
        case (): ()

# Pair and Bool combinations
def i16(p: Bool&Nat, b: Bool) -> Unit:
  match p:
    case (a,c):
      match b:
        case False: ()
        case True: ()

def i17(b: Bool, p: Bool&Nat) -> Unit:
  match p:
    case (a,c):
      match b:
        case False: ()
        case True: ()

# Equality type and Unit combinations
def i18(eq: Nat{0n == 0n}, u: Unit) -> Unit:
  match eq:
    case {==}:
      match u:
        case (): ()

def i19(u: Unit, eq: Nat{0n == 0n}) -> Unit:
  match eq:
    case {==}:
      match u:
        case (): ()

# Equality type and Bool combinations
def i20(eq: Nat{0n == 0n}, b: Bool) -> Unit:
  match eq:
    case {==}:
      match b:
        case False: ()
        case True: ()

def i21(b: Bool, eq: Nat{0n == 0n}) -> Unit:
  match eq:
    case {==}:
      match b:
        case False: ()
        case True: ()

# Boolean ADT and Unit combinations
def i22(bo: Boolean, u: Unit) -> Unit:
  match bo:
    case @Tr:
      match u:
        case (): ()
    case @Fl:
      match u:
        case (): ()

def i23_(u: Unit) -> Unit:
  match u:
    case (): ()

def i23(u: Unit, bo: Boolean) -> Unit:
  match bo:
    case @Tr:
      i23_(u)
    case @Fl:
      i23_(u)

# Boolean ADT and Bool combinations
def i24(bo: Boolean, b: Bool) -> Unit:
  match bo:
    case @Tr:
      match b:
        case False: ()
        case True: ()
    case @Fl:
      match b:
        case False: ()
        case True: ()

def i25_(b: Bool) -> Unit:
  match b:
    case False: ()
    case True: ()

def i25(b: Bool, bo: Boolean) -> Unit:
  match bo:
    case @Tr:
      i25_(b)
    case @Fl:
      i25_(b)

# Nats ADT and Unit combinations
def i26(m: Nats, u: Unit) -> Unit:
  match m:
    case @Zero:
      match u:
        case (): ()
    case @Succ{p}:
      match u:
        case (): ()

def i27_(u: Unit) -> Unit:
  match u:
    case (): ()

def i27(u: Unit, m: Nats) -> Unit:
  match m:
    case @Zero:
      i27_(u)
    case @Succ{p}:
      i27_(u)


"""

main :: IO ()
main = testFileChecks matches
