# Identity
def id<A>(x: A) -> A:
  x

# Type Negation
def Not(A: Set) -> Set:
  A -> Empty

# Congruence of equality
def app
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  rewrite e
  finally

# Negation on booleans
# - neg(True)  = False
# - neg(False) = True
def neg(x: Bool) -> Bool:
  if x:
    False
  else:
    True

# Proof: double negation is identity
def double_neg_theo(x: Bool) -> Bool{neg(neg(x)) == x}:
  if x:
    finally
  else:
    finally

# Double of a Nat
# - mul2(3) = 6
# - mul2(4) = 8
# - mul2(5) = 10
def mul2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + p:
      2n + mul2(p)

# Half of a Nat
# - div2(3) = 1
# - div2(6) = 3
# - div2(8) = 4
def div2(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n + p:
      1n + div2(p)

# Proof: n*2/2 = n (old method)
def div2_mul2_theo(n: Nat) -> Nat{div2(mul2(n)) == n}:
  match n:
    case 0n:
      finally
    case 1n + p:
      ind = div2_mul2_theo(p)
      prf = app(Nat, Nat, div2(mul2(p)), p, λx. 1n + x, ind)
      prf

# Nat Predecessor
def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      return 0n
    case 1n + p:
      return p

# Nat Addition
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

# Nat multiplication
def mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + ap:
      add(b, mul(ap, b))

# Nat Equality
def eql(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n   0n  : True
    case 1n+a 0n  : False
    case 0n   1n+b: False
    case 1n+a 1n+b: eql(a, b)

# Proof: n*2/2 = n (simpler method)
def div2_mul2_theo_2(n: Nat) -> Nat{(div2 (mul2 n)) == n}:
  match n:
    case 0n:
      finally
    case 1n + p:
      1n + div2_mul2_theo_2(p)

# Nat Parity (with nested match)
# - is_even_b(3) = False
# - is_even_b(4) = True
# - is_even_b(5) = False
# - is_even_b(6) = True
def is_even_a(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n:
      False
    case 2n + p:
      is_even_a(p)

# Nat Parity (calling 'not')
# - is_even_b(3) = False
# - is_even_b(4) = True
# - is_even_b(5) = False
# - is_even_b(6) = True
def is_even_b(n: Nat) -> Bool:
  match n:
    case 0n:
      True
    case 1n + p:
      neg(is_even_b(p))

# Proof that both is_even implementations are identical
# (Can we have FunExt?)
def is_even_ab_theo(n: Nat) -> Bool{(is_even_a n) == (is_even_b n)}:
  match n:
    case 0n:
      finally
    case 1n:
      finally
    case 2n + p:
      rewrite double_neg_theo(is_even_b(p))
      is_even_ab_theo(p)

# List Map
def map<A,B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case x <> xs:
      f(x) <> map<A,B>(f, xs)

# Add: reduce zero on right
def zero_right(a: Nat) -> Nat{a == add(a,0n)}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      1n + zero_right(ap)

# Add: reduce succ on right
def succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      1n + succ_right(ap,b)

# Add commutes
def comm(a: Nat, b: Nat) -> Nat{add(a,b) == add(b,a)}:
  match a:
    case 0n:
      zero_right(b)
    case 1n+ap:
      rewrite comm(ap,b)
      rewrite succ_right(b,ap)
      finally

# 0 != 1+n
def succ_neq_zero(n: Nat) -> Nat{0n != (1n+n)}:
  lambda e. match e {}

# 1n+n = 1n+m implies n = m
def succ_inj(n: Nat, m: Nat, e: Nat{(1n+n)==(1n+m)}) -> Nat{n==m}:
  match n m e:
    case 0n 0n e:
      finally
    case 1n+n 0n e:
      absurd e
    case 0n 1n+m e:
      absurd e
    case 1n+n 1n+m e:
      app<Nat,Nat>(1n+1n+n, 1n+1n+m, pred, e)

# Inductive Datatype
# ------------------

# data Vec (A : Set) : Nat → Set where
#   nil  : Vec A zero
#   cons : ∀ {n} → A → Vec A n → Vec A (suc n)
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A,n)
    e: Nat{N == (1n+n)}

def VecInd
  ( A: Set
  , P: all n:Nat xs:Vec(A,n). Set
  , N: P(0n,@Nil{finally})
  , C: all s:Nat x:A xs:Vec(A,s) p:P(s,xs). P(1n+s,@Cons{s,x,xs,finally})
  , n: Nat
  , x: Vec(A,n)
  ) -> P(n,x):
  match x:
    case @Nil{e}:
      rewrite e
      N
    case @Cons{n,h,t,e}:
      rewrite e
      C(n,h,t,VecInd(A,P,N,C,n,t))

# Proofs by o3
# ------------

# Add: reduce zero on the *left*
def zero_left(b: Nat) -> Nat{add(0n, b) == b}:
  finally

# Add: associativity (helper)
def assoc(a: Nat, b: Nat, c: Nat) -> Nat{add(add(a,b), c) == add(a, add(b,c))}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      1n + assoc(ap, b, c)

# Left-distributivity of multiplication over addition
def mul_dist_left(n: Nat, m: Nat, k: Nat) -> Nat{mul(n, add(m,k)) == add(mul(n,m), mul(n,k))}:
  match n:
    case 0n:
      finally
    case 1n + p:
      rewrite mul_dist_left(p, m, k)               #- Goal: Nat{add(add(m,k),add(mul(p,m),mul(p,k))) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      rewrite assoc(m, k, add(mul(p,m),mul(p,k)))  #- Goal: Nat{add(m,add(k,add(mul(p,m),mul(p,k)))) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      rewrite comm(k, add(mul(p,m),mul(p,k)))      #- Goal: Nat{add(m,add(add(mul(p,m),mul(p,k)),k)) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      rewrite assoc(mul(p,m), mul(p,k), k)         #- Goal: Nat{add(m,add(mul(p,m),add(mul(p,k),k))) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      rewrite comm(mul(p,k), k)                    #- Goal: Nat{add(m,add(mul(p,m),add(k,mul(p,k)))) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      rewrite assoc(m, mul(p,m), add(k,mul(p,k)))  #- Goal: Nat{add(add(m,mul(p,m)),add(k,mul(p,k))) == add(add(m,mul(p,m)),add(k,mul(p,k)))}
      finally

# Multiplication: zero on the **right**
def mul_zero_right(n: Nat) -> Nat{mul(n, 0n) == 0n}:
  match n:
    case 0n:
      finally
    case 1n + p:
      rewrite mul_zero_right(p) #- Goal: Nat{add(0n, 0n) == 0n}
      finally

# Multiplication: zero on the **left**
def mul_zero_left(b: Nat) -> Nat{mul(0n , b) == 0n}:
  finally

# Multiplication: zero on the **left**
def mul_zero_left(b: Nat) -> Nat{mul(0n , b) == 0n}:
  finally

# Multiplication: successor on the **left**
def succ_left_mul(a: Nat, b: Nat) -> Nat{mul(1n + a, b) == add(b, mul(a, b))}:
  finally

# W-Types
# -------

# W-Tree Type
type W(A: Set, B: A -> Set):
  case @Sup:
    x: A
    f: B(x) -> W(A,B)

# Generic W-Type Fold
def wfold
  ( A: Set
  , B: A -> Set
  , P: Set
  , w: W(A,B)
  , F: all x:A k:(B(x) -> P) . P
  ) -> P:
  match w:
    case @Sup{x,f}:
      F(x, λy. wfold(A,B,P,f(y),F))

# W-Tree
# ------

# W-Tree Tag
type WTreeTag<A: Set>:
  case @WLeaf:
    value: A
  case @WNode:

# W-Tree Recursive Fields
def WTreeRec(tag: WTreeTag(Nat)) -> Set:
  match tag:
    case @WLeaf{value}:
      return Empty
    case @WNode:
      return &{&lft, &rgt}

# W-Tree Type
def WTree : Set =
  W(WTreeTag(Nat), WTreeRec)

# Constructs a W-Leaf
def WLeaf(n: Nat) -> WTree:
  return @Sup{@WLeaf{n}, λe. absurd e}

# Constructs a W-Node
def WNode(l: WTree, r: WTree) -> WTree:
  return @Sup{@WNode{}, λi. match i: case &lft: l case &rgt: r  }

# Sums a W-Tree
def sum_wtree(w: WTree) -> Nat:
  match w:
    case @Sup{x,f}:
      match x:
        case @WLeaf{value}:
          return value
        case @WNode{}:
          a = f(&lft)
          b = f(&rgt)
          return add(sum_wtree(a), sum_wtree(b))

# Sum a W-Tree (using the generic fold)
def sum_wtree_fold(w: WTree) -> Nat:
  wfold<WTreeTag(Nat), WTreeRec, Nat>(w,
    lambda tag f.
    match tag:
      case @WLeaf{value}:
        value
      case @WNode:
        add(f(&lft), f(&rgt)))
