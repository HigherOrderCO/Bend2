# Inductive Datatypes in Bend2

Bend2 has a minimal Core, which doesn't include built-in inductive datatypes. To
encode them, we use other primitives, including labels, sigmas, and the identity
type. For example, in Agda, a Vector can be defined as:

```agda
data Vec (A : Set) : Nat → Set where
  nil  : Vec A zero
  cons : ∀ {n} → A → Vec A n → Vec A (suc n)
```

In Bend2, the same type is *encoded* as:

```python
def Vec(A: Set, N: Nat) -> Set:
  any ctr: @{@Nil,@Cons}.
  match ctr:
    case @Nil: # Nil
      any e : Nat{N == 0n}.
      Unit
    case @Cons: # Cons
      any n : Nat.
      any h : A.
      any t : Vec(A,n).
      any e : Nat{N == 1n+n}.
      Unit
```

Let's parse this, line by line.

```python
def Vec(A: Set, N: Nat) -> Set
```

This declares a Vec as a function from a type `A`, and a length `N : Nat`, to
a type. This is the same type as the Agda counterpart, except here it is a user
defined function, rather than a built-in top-level declaration.

```
any ctr: @{@Nil,@Cons}.
```

Here:

- `any x: A. B` is a sugar for `Σ(x:A).B(x)` - i.e., a Sigma type, with the
  first element, `x` having type `A`, and the second element having type `B(x)`. 

- `@{@Nil,@Cons}` is an inline Enum type, with 2 variants: `@Nil` and `Cons`.

In other words, this line declares a Sigma type, with the first element being an
*enum* of the constructor names, `@Nil` and `@Cons`.

Then, for the second element of the sigma type, we *match* on that name:

```python
  match ctr:
```

This will give us two cases.

**The `@Nil` case is:**

```python
    case @Nil:
      any e: Nat{N == 0}.
      Unit
```

This means that, the first element is `@Nil`, the second is a Sigma, with:

- `e`: asserts that the length of the empty list is 0
- Unit: just a placeholder, by convention

So, to construct an empty list `xs`, we write:

`(@Nil,e,())`

Which includes the constructor name (Nil), a proof, `e`, that `N(xs) == 0`
(useful in proofs), and `()`, which is just the unit element (for convention).

**The `@Cons` case is:**

```python
    case @Cons:
      any n: Nat.
      any h: A.
      any t: Vec(A,n).
      any e: Nat{N == 1+n}.
      Unit
```

Here, we have 4 Sigmas, one for each field:

- `n`: the length of the tail
- `h`: the head element
- `t`: all elements except the head
- `e`: asserts the new length is 1 + the length of the tail
- Unit: just a placeholder, by convention

So, to extend a list `xs` with an element `x`, we write:

`(@Cons, n, x, xs, e, ())`

Which includes the constructor name (Cons), the length of the tail `n`, the head
element `x`, the tail `xs`, a proof that `N(x:xs) == 1+N(xs)`, and the unit
element (for convention).

## Proving Induction

To show that this encoding is sufficient to prove induction, let's do for `Vec`.

We start by writing the type of induction on vectors:

```python
def VecInd
  ( A: Set
  , P: all N:Nat xs:Vec(A,N). Set
  , N: P(0n,(@Nil,{==},()))
  , C: all n:Nat h:A t:Vec(A,n) . P(n,t) -> P(1n+n,(@Cons,n,h,t,{==},()))
  , N: Nat
  , x: Vec(A,N)
  ) -> P(N,x):
  ()
```

This gives us the following goal:

```
Mismatch:
- Goal: (P N x)
- Type: Unit
Context:
- A : Set
- P : ∀N:Nat.∀xs:(@Vec A N).Set
- N : (P 0 (@Nil,{==},()))
- C : ∀n:Nat.∀h:A.∀t:(@Vec A n).(P n t)→(P 1+n (@Cons,n,h,t,{==},()))
- N : Nat
- x : Σctr:{@Nil,@Cons}.(λ{@Nil:Σe:Nat{N==0}.Unit;@Cons:Σn:Nat.Σh:A.Σt:(Vec A n).Σe:Nat{N==1+n}.Unit} ctr)
```

We then proceed by case analysis on the vector `x`:

```python
    case (ctr, fields):
      match ctr:
        case @Nil:
          ()
        case @Cons:
          ()
```

This gives us the goal for the `Nil` case:

```
Mismatch:
- Goal: (P N (@Nil,fields))
- Type: Unit
Context:
- A : Set
...
- fields : (λctr.(λ{@Nil:Σe:Nat{N==0}.Unit;@Cons:Σn:Nat.Σh:A.Σt:(Vec A n).Σe:Nat{N==1+n}.Unit} ctr) ctr)
```

Note that, here, `fields` is not specialized w.r.t. value of `ctr`. Unlike
Agda/Lean, specialization isn't automatic; we need to manually do it using
a `with` statement:

```python
def VecInd
  ( A: Set
  , P: all N:Nat xs:Vec(A,N). Set
  , N: P(0n,(@Nil,{==},()))
  , C: all n:Nat h:A t:Vec(A,n) . P(n,t) -> P(1n+n,(@Cons,n,h,t,{==},()))
  , N: Nat
  , x: Vec(A,N)
  ) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with bag
        case @Nil:
          ()
        case @Cons:
          ()
```

This updates the `Nil` goal to:

```
Mismatch:
- Goal: (P N (@Nil,fields))
- Type: Unit
Context:
- A : Set
...
- fields : Σe:Nat{N==0}.Unit
```

Note that, now, `fields` includes the fields of the `Nil` constructor, which is
just a proof that the vector length, `N`, is `0`. We can extract it:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          ()
        case @Cons:
          ()
```

This updates the `Nil` goal to:

```
Mismatch:
- Goal: (P N (@Nil,e,()))
- Type: Unit
Context:
- A : Set
...
- fields : Σe:Nat{N==0}.Unit
- e : Nat{N==0}
```

Now, note that the goal is `(P N (@Nil,e,()))`, but, in the context, we have a
proof, `e` that `N == 0`. This allows us to pattern-match on this proof with
either `match e: case {==}:`, or directly, with `{==} = e`:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          ()
        case @Cons:
          ()
```

Causing the goal to be updated to:

```
Mismatch:
- Goal: (P 0 (@Nil,{==},()))
- Type: Unit
Context:
- A : Set
...
- N : (P 0 (@Nil,{==},()))
...
- fields : Σe:Nat{N==0}.Unit
- e : Nat{N==0}
```

Note that the type of `N` is exactly the type of our goal, allowing us to
prove this case:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          N
        case @Cons:
          ()
```

This leaves us with the `@Cons` case:

```
Mismatch:
- Goal: (P N (@Cons,fields))
- Type: Unit
Context:
- A : Set
...
- fields : Σn:Nat.Σh:A.Σt:(Vec A n).Σe:Nat{N==1+n}.Unit
```

Once again, we can extract the fields:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          N
        case @Cons:
          (n, h, t, e, ()) = fields
          ()
```

Giving us the goal:

```
- Goal: (P N (@Cons,n,h,t,e,()))
- Type: Unit
Context:
- A : Set
...
- n : Nat
- h : A
- t : Vec(A,n)
- e : Nat{N==1+n}
Expression:
- ()
Location: (line 156, column 11)
156 |           ()
```

Which, once again, we can specialize by pattern-matching on `e`:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          N
        case @Cons:
          (n, h, t, e, ()) = fields
          {==} = e
          ()
```

Giving us the goal:

```
Mismatch:
- Goal: (P 1+n (@Cons,n,h,t,{==},()))
- Type: Unit
Context:
- A : Set
...
- n : Nat
- h : A
- t : Vec(A,n)
- e : Nat{N==1+n}
```

By induction on `t`, we can construct `ind : (P n t)`:

```python
def VecInd
  (...) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          (e, ()) = fields
          {==} = e
          N
        case @Cons:
          (n, h, t, e, ()) = fields
          {==} = e
          ind = VecInd(A,P,N,C,n,t)
          ()
```

Giving us the goal:

```
Mismatch:
- Goal: (P 1+n (@Cons,n,h,t,{==},()))
- Type: Unit
Context:
- A : Set
- C : ∀n: Nat.
      ∀h: A.
      ∀t: (@Vec A n).
      (P n t) →
      (P 1+n (@Cons,n,h,t,{==},()))
...
- n : Nat
- h : A
- t : Vec(A,t)
- e : Nat{N==1+n}
- ind : (P n t)
```

Now, we have everything we need to call `C`, which returns exactly the demanded
goal, completing the proof. We can write it compactly, as:

```python
def VecInd
  ( A: Set
  , P: all N:Nat xs:Vec(A,N). Set
  , N: P(0n,(@Nil,{==},()))
  , C: all n:Nat h:A t:Vec(A,n) . P(n,t) -> P(1n+n,(@Cons,n,h,t,{==},()))
  , N: Nat
  , x: Vec(A,N)
  ) -> P(N,x):
  match x:
    case (ctr, fields):
      match ctr:
        with fields
        case @Nil:
          ({==}, ()) = fields
          N
        case @Cons:
          (n, h, t, {==}, ()) = fields
          C(n,h,t,VecInd(A,P,N,C,n,t))
```

## A Syntax Sugar

Since handling datatypes are common, Bend includes syntax sugars to declare,
construct and eliminate them.

### Datatype Declaration

The Vector type can be declared as:

```python
type Vec<A: Set>(N: Nat):
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A, n)
    e: Nat{N == 1n+n}
```

This will desugar to the same `def Vec ...` declaration we wrote before.

The general form is:

```
type Vec<p0: P0, p1: P1, ...>(i0: I0, i1: i1, ...):
  case @Ctr0:
    f0: F0
    f1: F1
    ...
    e0: i0 == E0
    e1: i1 == E1
    ...
  case @Ctr1:
    ...
```

Where:
- `pN: PN` declare parameters and their types...
- `iN: IN` declare indices and their types...
- `case @CtrN:` introduce constructors...
- `fN: FN` declare fields and their types...
- `eN: iN == EN` declare index equalities...

For completion, here are some Agda types and their translations:

```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

```python
type Bool:
  case @True:
  case @False:
```

```agda
data Maybe (A : Set) : Set where
  none : Maybe A
  some : (value : A) -> Maybe A
```

```python
type Maybe(A: Set):
  case @None:
  case @Some:
    value: A
```

```agda
data List (A : Set) : Set where
  nil  : List A
  cons : A → List A → List A
```

```python
type List(A: Set):
  case @Nil:
  case @Cons:
    head: A
    tail: List(A)
```

```agda
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B
```

```python
type Sigma(A: Set, B: A -> Set):
  case @Pair:
    fst: A
    snd: B(fst)
```

```agda
data Equal (A : Set) (x : A) : A → Set where
  refl : (x : A) → Equal A x x
```

```python
type Equal<A: Set, x: A>(y: A):
  case @Refl:
    x: A
    e: y == x
```

### Constructor Syntax

Constructors can be written using a compact syntax:

```python
# Instead of:
empty : List(Nat) = (@Nil, ())

# We can write:
empty : List(Nat) = @Nil{}

# Instead of:
myList : List(Nat) = (@Cons, 2, 42, (@Cons, 1, 7, (@Nil, {==}, ()), {==}, ()), {==}, ())

# We can write:
myList : List(Nat) = @Cons{42, @Cons{7, @Nil{}}}
```

### Pattern Matching Syntax

Similarly, pattern matching can use a more familiar syntax:

```python
# Instead of:
match vec:
  case (ctr, fields):
    match ctr:
      with fields
      case @Nil:
        ({==}, ()) = fields
        ...
      case @Cons:
        (n, h, t, {==}, ()) = fields
        ...

# We can write:
match vec:
  case @Nil{}:
    ...
  case @Cons{n, h, t, {==}}:
    ...
```

This sugar automatically handles the constructor matching, field extraction, and index equality proofs.
