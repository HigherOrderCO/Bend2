# Identity
def id<A>(x: A) -> A:
  x

# Negation on booleans
# - not(True)  = False
# - not(False) = True
def not(x: Bool) -> Bool:
  if x:
    False
  else:
    True

# Proof: double negation is identity
def double_neg_theo(x: Bool) -> Bool{not(not(x)) == x}:
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

# Congruence of equality
def cong
  ( A: Set
  , B: Set
  , a: A
  , b: A
  , f: A -> B
  , e: A{a == b}
  ) -> B{f(a) == f(b)}:
  rewrite e
  finally

# Proof: n*2/2 = n (old method)
def div2_mul2_theo(n: Nat) -> Nat{div2(mul2(n)) == n}:
  match n:
    case 0n:
      finally
    case 1n + p:
      ind = div2_mul2_theo(p)
      prf = cong(Nat, Nat, div2(mul2(p)), p, λx. 1n + x, ind)
      prf

# Nat Equality
def equal(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n   0n  : True
    case 1n+a 0n  : False
    case 0n   1n+b: False
    case 1n+a 1n+b: equal(a, b)

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
      not(is_even_b(p))

# Proof that both is_even implementations are identical
# (Can we have FunExt?)
def is_even_ab_theo(n: Nat) -> Bool{(is_even_a n) == (is_even_b n)}:
  match n:
    case 0n:
      finally
    case 1n:
      finally
    case 2n + p:
      #rewrite double_neg_theo(is_even_b(p))
      #is_even_ab_theo(p)
      ()

## List Map
#def map<A,B>(f: A -> B, xs: A[]) -> B[]:
  #match xs:
    #case []:
      #[]
    #case x <> xs:
      #f(x) <> map<A,B>(f, xs)

## Inductive Datatype
## ------------------

## Can we encode inductive datatypes?

## data Vec (A : Set) : Nat → Set where
##   nil  : Vec A zero
##   cons : ∀ {n} → A → Vec A n → Vec A (suc n)
#type Vec<A: Set>(N: Nat) -> Set:
  #case @Nil:
    #e: Nat{N == 0}
  #case @Cons:
    #n: Nat
    #h: A
    #t: Vec(A,n)
    #e: Nat{N == (1n+n)}

#def VecInd
  #( A: Set
  #, P: all n:Nat xs:Vec(A,n). Set
  #, N: P(0,@Nil{finally})
  #, C: all s:Nat x:A xs:Vec(A,s) . P(s,xs) -> P(1n+s,@Cons{s,x,xs,finally})
  #, n: Nat
  #, x: Vec(A,n)
  #) -> P(n,x):
  #match x:
    #case @Nil{e}:
      #rewrite e
      #N
    #case @Cons{n,h,t,e}:
      #rewrite e
      #C(n,h,t,VecInd(A,P,N,C,n,t))

####def VecInd
####:(∀A: Set.
  ####∀P: ∀n:Nat. ∀xs: Vec(A,n). Set.
  ####∀N: P(0,@Nil{{==}}).
  ####∀C: (∀s:Nat. ∀x:A. ∀xs:Vec(A,s).  P(s,xs) -> P(1n+s,@Cons{s,x,xs,{==}})).
  ####∀n: Nat.
  ####∀x: Vec(A,n).
  ####P(n,x))
####= λA. λP. λN. λC. λn. λx.
  ####(λ{
    ####(,):λ_x6. λ_x7. (λ{
      ####@Nil: λ_x7. (λ{
        ####(,):λe. λ_x9. (λ{
          ####():λe. (λ{ {==}:N })(e)
        ####})(_x9,e)
      ####})(_x7)
      ####@Cons: λ_x7. (λ{
        ####(,):λn. λ_x10. (λ{
          ####(,):λh. λ_x12. λn. (λ{
            ####(,):λt. λ_x14. λn. λh. (λ{
              ####(,):λe. λ_x16. λn. λh. λt. (λ{
                ####():λn. λh. λt. λe. (λ{
                  ####{==}:C(n,h,t,VecInd(A,P,N,C,n,t)) })(e)
                ####})(_x16,n,h,t,e)
              ####})(_x14,n,h,t)
            ####})(_x12,n,h)
          ####})(_x10,n)
        ####})(_x7)
        ####λ_x7. λ_x9. λ{}
      ####})(_x6,_x7)
  ####})(x)

##### More Stuff
##### ----------

####def main(x: Char) -> Char[]:
  ####"foo bar!!"
