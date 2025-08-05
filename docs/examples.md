# Bend Examples

This document contains examples from the WanShi repository that demonstrate various Bend features. All examples are verified to type-check.

## Table of Contents

- [Basic Functions](#basic-functions)
- [Data Structures](#data-structures)
- [Mathematical Functions](#mathematical-functions)
- [Proofs and Verification](#proofs-and-verification)
- [Advanced Type System Features](#advanced-type-system-features)
- [Practical Applications](#practical-applications)

## Basic Functions

### Boolean Operations

```bend
# From Bool/not.bend
def Bool/not(b: Bool) -> Bool:
  match b:
    case False:
      True
    case True:
      False

# From Bool/and/_.bend
def Bool/and(a: Bool, b: Bool) -> Bool:
  match a:
    case False:
      False
    case True:
      b

# From Bool/or/_.bend
def Bool/or(a: Bool, b: Bool) -> Bool:
  match a:
    case False:
      b
    case True:
      True

# From Bool/xor/_.bend
def Bool/xor(a: Bool, b: Bool) -> Bool:
  match a:
    case False:
      b
    case True:
      Bool/not(b)
```

### Natural Number Arithmetic

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

# From Nat/pred/_.bend
def Nat/pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n + p:
      p

# From Nat/sub.bend
def Nat/sub(a: Nat, b: Nat) -> Nat:
  match b:
    case 0n:
      a
    case 1n + p:
      Nat/sub(Nat/pred(a), p)
```

## Data Structures

### Maybe Type

```bend
# From Maybe/_.bend
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A
```

### Result Type

```bend
# From Result/_.bend
type Result<T, E: Set>:
  case @Ok:
    value: T
  case @Error:
    error: E
```

### List Operations

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

# From List/fold.bend
def List/fold<A>(xs: A[]) -> ∀P:Set. P -> (A -> P -> P) -> P:
  match xs:
    case []:
      lambda P nil cons.
      nil
    case x <> xs:
      lambda P nil cons.
      cons(x, List/fold(A,xs,P,nil,cons))

# From List/reverse.bend
def List/reverse<A>(xs: A[]) -> A[]:
  List/reverse/aux<A>(xs, [])

def List/reverse/aux<A>(xs: A[], acc: A[]) -> A[]:
  match xs:
    case []:
      acc
    case h <> t:
      List/reverse/aux<A>(t, h <> acc)
```

### Binary Trees

```bend
# From Tree/_.bend
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>

# From Tree/map.bend
def Tree/map<A,B>(tree: Tree<A>, f: A -> B) -> Tree<B>:
  match tree:
    case @Leaf{value}:
      @Leaf{f(value)}
    case @Node{left,right}:
      @Node{Tree/map<A,B>(left,f), Tree/map<A,B>(right,f)}

# From Tree/fold.bend
def Tree/fold<A,B>(tree: Tree<A>, leaf: A -> B, node: B -> B -> B) -> B:
  match tree:
    case @Leaf{value}:
      leaf(value)
    case @Node{left, right}:
      node(Tree/fold<A,B>(left, leaf, node), Tree/fold<A,B>(right, leaf, node))
```

## Mathematical Functions

### Comparison

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

# From Nat/eql.bend
def Nat/eql(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True
    case 0n 1n+b:
      False
    case 1n+a 0n:
      False
    case 1n+a 1n+b:
      Nat/eql(a, b)

# From Nat/lt.bend
def Nat/lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case a 0n:
      False
    case 0n 1n+b:
      True
    case 1n+a 1n+b:
      Nat/lt(a, b)
```

### Division and Modulo

```bend
# From Nat/div.bend
def Nat/div(a: Nat, b: Nat) -> Nat:
  Nat/div/aux(a, b, b)

def Nat/div/aux(a: Nat, b: Nat, c: Nat) -> Nat:
  match Nat/lt(a, b):
    case True:
      0n
    case False:
      1n + Nat/div/aux(Nat/sub(a, b), b, b)

# From Nat/mod.bend
def Nat/mod(a: Nat, b: Nat) -> Nat:
  Nat/mod/aux(a, b, b)

def Nat/mod/aux(a: Nat, b: Nat, c: Nat) -> Nat:
  match Nat/lt(a, b):
    case True:
      a
    case False:
      Nat/mod/aux(Nat/sub(a, b), b, b)
```

## Proofs and Verification

### Basic Equality Proofs

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

### Addition Properties

```bend
# From Nat/add/unit_left.bend
def Nat/add/unit_left(b: Nat) -> Nat{Nat/add(0n, b) == b}:
  finally

# From Nat/add/unit_right.bend
def Nat/add/unit_right(x: Nat) -> Nat{Nat/add(x,0n) == x}:
  match x:
    case 0n:
      finally
    case 1n + xp:
      ind = Nat/add/unit_right(xp)
      rewrite ind
      finally

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

### Successor Properties

```bend
# From Nat/succ/injective.bend
def Nat/succ/injective() -> Proof/function/injective(Nat, Nat, Nat/succ):
  λx.λy.λeq1.λeq2.
    eq1(Nat/pred/preserves_eq(1n+x,1n+y, eq2))

# From Nat/succ/neq_zero.bend
def Nat/succ/neq_zero(n: Nat) -> Not/_(Nat{1n+n == 0n}):
  λe. match e {}
```

### Multiplication Properties

```bend
# From Nat/mul/zero_left.bend
def Nat/mul/zero_left(b: Nat) -> Nat{Nat/mul(0n, b) == 0n}:
  finally

# From Nat/mul/zero_right.bend
def Nat/mul/zero_right(a: Nat) -> Nat{Nat/mul(a, 0n) == 0n}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      Nat/mul/zero_right(ap)

# From Nat/mul/neutral_left.bend
def Nat/mul/neutral_left(b: Nat) -> Nat{Nat/mul(1n, b) == b}:
  Nat/add/unit_right(b)

# From Nat/mul/distributive_left.bend
def Nat/mul/distributive_left(a: Nat, b: Nat, c: Nat) -> Nat{Nat/mul(a, Nat/add(b, c)) == Nat/add(Nat/mul(a, b), Nat/mul(a, c))}:
  match a:
    case 0n:
      finally
    case 1n + ap:
      ind = Nat/mul/distributive_left(ap, b, c)
      rewrite ind
      rewrite Nat/add/associative(b, c, Nat/add(Nat/mul(ap, b), Nat/mul(ap, c)))
      rewrite Nat/add/associative(b, Nat/mul(ap, b), Nat/add(c, Nat/mul(ap, c)))
      rewrite Nat/add/commutative(Nat/mul(ap, b), Nat/add(c, Nat/mul(ap, c)))
      rewrite Nat/add/associative(c, Nat/mul(ap, c), Nat/mul(ap, b))
      rewrite Nat/add/commutative(Nat/add(c, Nat/mul(ap, c)), Nat/mul(ap, b))
      rewrite Nat/add/associative(b, Nat/add(c, Nat/mul(ap, c)), Nat/mul(ap, b))
      rewrite Nat/add/associative(Nat/add(b, c), Nat/mul(ap, c), Nat/mul(ap, b))
      rewrite Nat/add/associative(Nat/add(b, c), Nat/add(Nat/mul(ap, c), Nat/mul(ap, b)))
      rewrite Nat/add/commutative(Nat/mul(ap, c), Nat/mul(ap, b))
      finally
```

## Advanced Type System Features

### Type-Level Functions

```bend
# From Set/Equal/_.bend
def Set/Equal<A>(a:A,b:A) -> Set:
  ∀P: A->Set . (P(a) -> P(b))

# From Set/Not/_.bend
# ¬A
def Set/Not(A: Set) -> Set:
  A -> Empty

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

### Function Properties

```bend
# From Proof/function/injective.bend
def Proof/function/injective<A,B>(f: A -> B) -> Set:
  ∀x:A.∀y:A. (B{f(x) == f(y)} -> A{x == y})

# From Set/Function/is_bijection.bend
def Set/Function/is_bijection<A,B>(f: A -> B) -> Set:
  Set/And(
    ∀a1:A. ∀a2:A. (B{f(a1) == f(a2)} -> A{a1 == a2}),
    ∀b:B. Σa:A. B{f(a) == b}
  )
```

### Algebraic Structures

```bend
# From Algebra/magma.bend
def Algebra/magma<A>(f: A -> A -> A) -> Set:
  Unit

# From Algebra/semigroup.bend
def Algebra/semigroup<A>(f: A -> A -> A) -> Set:
  Set/And(
    Algebra/magma<A>(f),
    Algebra/associative<A>(f)
  )

# From Algebra/monoid.bend
def Algebra/monoid<A>(f: A -> A -> A, u: A) -> Set:
  Set/And(
    Algebra/semigroup<A>(f),
    Algebra/unit<A>(f, u)
  )

# From Algebra/group.bend
def Algebra/group<A>(f:A->A->A, u:A) -> Set:
  is_ass = Algebra/associative<A>(f)
  is_uni = Algebra/unit<A>(f, u)
  is_div = Algebra/divisible<A>(f)
  Proof/and(is_ass, Proof/and(is_uni, is_div))
```

## Practical Applications

### Tic-Tac-Toe Game

```bend
# From TC/Cell/_.bend
type TC/Cell:
  case @Empty:
  case @X:
  case @O:

# From TC/Player/_.bend
type TC/Player:
  case @X:
  case @O:

# From TC/Player/other.bend
def TC/Player/other(p: TC/Player) -> TC/Player:
  match p:
    case @X:
      @O
    case @O:
      @X

# From TC/Board/check_line.bend
def TC/Board/check_line(line: TC/Cell[]) -> Maybe<TC/Player>:
  match line:
    case [@X, @X, @X]:
      @Some{@X}
    case [@O, @O, @O]:
      @Some{@O}
    case _:
      @None{}

# From TC/Proofs/player_involution.bend
def TC/Proofs/player_involution(p: TC/Player) -> TC/Player{TC/Player/other(TC/Player/other(p)) == p}:
  match p:
    case @X:
      finally
    case @O:
      finally
```

### String Operations

```bend
# From String/map.bend
def String/map(xs: String, fn: Char -> Char) -> String:
  List/map<Char,Char>(xs, fn)

# From String/equal.bend
def String/equal(xs: String, ys: String) -> Bool:
  match xs ys:
    case [] []:
      True
    case x<>xs []:
      False
    case [] y<>ys:
      False
    case x<>xs y<>ys:
      if Char/equal(x, y):
        String/equal(xs, ys)
      else:
        False

# From String/append.bend
def String/append(xs: String, ys: String) -> String:
  List/append<Char>(xs, ys)

# From String/concat.bend
def String/concat(xss: String[]) -> String:
  List/concat<Char>(xss)
```

### Lambda Calculus

```bend
# From LC/Term/_.bend
type LC/Term:
  case @Var:
    name: String
  case @Lam:
    param: String
    body: LC/Term
  case @App:
    func: LC/Term
    arg: LC/Term

# From LC/substitute.bend - partial example
def LC/substitute(term: LC/Term, var: String, replacement: LC/Term) -> LC/Term:
  match term:
    case @Var{name}:
      if String/equal(name, var):
        replacement
      else:
        @Var{name}
    case @Lam{param, body}:
      if String/equal(param, var):
        @Lam{param, body}
      else:
        @Lam{param, LC/substitute(body, var, replacement)}
    case @App{func, arg}:
      @App{LC/substitute(func, var, replacement), LC/substitute(arg, var, replacement)}
```

All examples in this document are taken from the WanShi repository and are verified to type-check correctly with Bend.