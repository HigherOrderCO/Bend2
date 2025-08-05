# Advanced Features in Bend

This guide covers advanced features of Bend using examples from the WanShi repository that are verified to type-check.

## Table of Contents

- [Lambda Matching](#lambda-matching)
- [Fixed Points and Recursion](#fixed-points-and-recursion)
- [Proof Techniques](#proof-techniques)
- [Advanced Pattern Matching](#advanced-pattern-matching)
- [Higher-Order Type Constructions](#higher-order-type-constructions)

## Lambda Matching

Lambda matching allows you to define functions by pattern matching on their arguments using special lambda syntax.

### Basic Lambda Matching

From WanShi's examples:

```bend
# From List/fold.bend
def List/fold<A>(xs: A[]) -> ∀P:Set. P -> (A -> P -> P) -> P:
  match xs:
    case []:
      lambda P nil cons.
      nil
    case x <> xs:
      lambda P nil cons.
      cons(x, List/fold(A,xs,P,nil,cons))
```

### Pattern Matching with Lambda

```bend
# From Bool/not.bend
def Bool/not(b: Bool) -> Bool:
  match b:
    case False:
      True
    case True:
      False
```

## Fixed Points and Recursion

### Basic Recursion Patterns

```bend
# From Nat/add/_.bend
def Nat/add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + Nat/add(p, b)

# From Nat/mul/_.bend
def Nat/mul(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n + p:
      Nat/add(b, Nat/mul(p, b))
```

### Structural Recursion on Lists

```bend
# From List/map.bend
def List/map<A,B>(xs: A[], f: A -> B) -> B[]:
  match xs:
    case []:
      []
    case x <> xs:
      f(x) <> List/map<A,B>(xs,f)

# From List/filter.bend
def List/filter<A>(p: A -> Bool, xs: A[]) -> A[]:
  match xs:
    case []:
      []
    case h <> t:
      if p(h):
        h <> List/filter<A>(p, t)
      else:
        List/filter<A>(p, t)
```

## Proof Techniques

### Equality Proofs

```bend
# From Equal/app.bend
def Equal/app<A,B>(a: A, b: A, f: A -> B, e: A{a == b}) -> B{f(a) == f(b)}:
  rewrite e
  finally

# From Equal/sym.bend
def Equal/sym<A>(a: A, b: A, e: A{a == b}) -> A{b == a}:
  rewrite e
  finally
```

### Inductive Proofs

```bend
# From Nat/add/commutative.bend
def Nat/add/commutative() -> Algebra/commutative<Nat,Nat>(Nat/add):
  λa.λb.
  match a:
    case 0n:
      rewrite Nat/add/unit_right(b)
      finally
    case 1n + pa:
      ind = Nat/add/commutative(pa,b)
      rewrite ind
      rewrite Nat/succ/add_suc_right(b,pa)
      finally

# From Nat/add/associative.bend
def Nat/add/associative() -> Algebra/associative<Nat>(Nat/add):
  λa.λb.λc.
  match a:
    case 0n:
      finally
    case 1n + ap:
      rewrite Nat/add/associative(ap, b, c)
      finally
```

### Proof by Induction

```bend
# From Nat/add/unit_right.bend
def Nat/add/unit_right(x: Nat) -> Nat{Nat/add(x,0n) == x}:
  match x:
    case 0n:
      finally
    case 1n + xp:
      ind = Nat/add/unit_right(xp)
      rewrite ind
      finally
```

## Advanced Pattern Matching

### Multiple Scrutinees

```bend
# From Nat/cmp.bend
def Nat/cmp(a: Nat, b: Nat) -> Cmp:
  match a b:
    case 0n 0n:
      @EQ
    case 0n 1n+b:
      @LT
    case 1n+a 0n:
      @GT
    case 1n+a 1n+b:
      Nat/cmp(a, b)
```

### Nested Pattern Matching

```bend
# From TC/Board/check_line.bend
def TC/Board/check_line(line: TC/Cell[]) -> Maybe<TC/Player>:
  match line:
    case [@X, @X, @X]:
      @Some{@X}
    case [@O, @O, @O]:
      @Some{@O}
    case _:
      @None{}
```

### Constructor Patterns

```bend
# From Maybe/_.bend
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

# From Tree/_.bend
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>
```

## Higher-Order Type Constructions

### Dependent Types

```bend
# From Set/Equal/_.bend
def Set/Equal<A>(a:A,b:A) -> Set:
  ∀P: A->Set . (P(a) -> P(b))

# From Proof/forall/_.bend
def Proof/forall<A,P>(f: ∀a:A.P(a), x:A) -> P(x):
  f(x)
```

### Existential Types

```bend
# From Set/Exists/_.bend
# ∃a ∈ A : P(a)
def Set/Exists(A : Set, P: A -> Set) -> Set:
  ∀C:Set . ((∀a:A . (P(a) -> C)) -> C)

# From Proof/exists/_.bend
def Proof/exists<A,P>(x:A, px: P(x)) -> Set/Exists(A, P):
  λC f. f(x,px)
```

### Type-Level Functions

```bend
# From Set/Function/is_bijection.bend
def Set/Function/is_bijection<A,B>(f: A -> B) -> Set:
  Set/And(
    ∀a1:A. ∀a2:A. (B{f(a1) == f(a2)} -> A{a1 == a2}),
    ∀b:B. Σa:A. B{f(a) == b}
  )

# From Set/Function/has_left_inverse.bend
def Set/Function/has_left_inverse<A,B>(f: A -> B) -> Set:
  Σg: B -> A . Set/Function/is_left_inverse<A,B>(g, f)
```

### Advanced Type Constructions

```bend
# From Set/And/_.bend
def Set/And(P: Set, Q: Set) -> Set:
  ∀C: Set . (P -> Q -> C) -> C

# From Set/Or/_.bend
def Set/Or(P: Set, Q: Set) -> Set:
  ∀C: Set . (P -> C) -> (Q -> C) -> C

# From Set/Iff/_.bend
# A <-> B
def Set/Iff(A: Set, B: Set) -> Set:
  Set/And(A->B,B->A)
```

### Algebraic Properties

```bend
# From Algebra/associative.bend
def Algebra/associative<A>(f: A -> A -> A) -> Set:
  ∀a:A.∀b:A.∀c:A. A{f(f(a, b), c) == f(a, f(b, c))}

# From Algebra/commutative.bend
def Algebra/commutative<A,B>(f: A -> B -> B) -> Set:
  ∀a:A.∀b:B. B{f(a, b) == f(b, a)}

# From Algebra/distributive_left.bend
def Algebra/distributive_left<A>(mult: A -> A -> A, add: A -> A -> A) -> Set:
  ∀a:A. ∀b:A. ∀c:A. A{mult(a, add(b, c)) == add(mult(a, b), mult(a, c))}
```

### Proofs of Properties

```bend
# From Nat/mul/associative.bend
def Nat/mul/associative() -> Algebra/associative<Nat>(Nat/mul):
  λa b c.
  match a:
    case 0n:
      finally
    case 1n+pa:
      rewrite Nat/mul/associative(pa, b, c)
      rewrite Nat/add/associative(b, Nat/mul(pa, b), Nat/mul(c, Nat/mul(pa, b)))
      rewrite Nat/mul/distributive_left(b, c, Nat/mul(pa, b))
      finally

# From Nat/succ/injective.bend
def Nat/succ/injective() -> Proof/function/injective(Nat, Nat, Nat/succ):
  λx.λy.λeq1.λeq2.
    eq1(Nat/pred/preserves_eq(1n+x,1n+y, eq2))
```

### Inductive Type Reasoning

```bend
# From Not/_.bend
def Not/_(A: Set) -> Set:
  A -> Empty

# From Nat/succ/neq_zero.bend
def Nat/succ/neq_zero(n: Nat) -> Not/_(Nat{1n+n == 0n}):
  λe. match e {}
```

All examples in this document are taken directly from the WanShi repository and are verified to type-check correctly with Bend.