# Proper Case-Trees

Internally, Bend stores top-level definitions as proper case-trees. In a future
update, the compiler will automatically convert functions to this format. As of
Aug 2025, it won't do that, so, it must be enforced manually by the user.

A definition is in proper case-tree form when its body is a chain of nested
pattern matches where the scrutinee is a variable (i.e., not an expression),
ending in a return expression which has no pattern-matches. Examples:

The following function IS in proper case-tree form with 4 branches:

```python
def F_A(x: Nat, y: Nat) -> Nat:
  match x:
    case 0n:
      match y:
        case 0n:
          A
        case 1n + yp:
          B(yp)
    case 1n + xp:
      match y:
        case 0n:
          C(xp)
        case 1n + yp:
          D(xp, yp)
```

Because its body is a chain of nested pattern-matches (`match x`, then `match
y`), where the scrutinees are variables (`x` and `y`) and not compound
expressions, ending in expressions that don't contain further pattern-matches
(`A`, `B(yp)`, `C(xp)`, `D(xp, yp)`).

The following function IS in proper case-tree form with 4 branches:
          
```python
def F_B(x: Nat, y: Nat) -> Nat:
  match x y:
    case 0n 0n:
      A
    case 0n 1n+yp:
      B(yp)
    case 0n 1n+xp:
      C(xp)
    case 1n+xp 1n+yp:
      D(xp, yp)
```

Because it is just a shorter version of the first function.

The following function IS NOT in proper case-tree form with 4 branches:
          
```python
def F_C(x: Nat, y: Nat) -> Nat:
  match (x+1n) F(y):
    case 0n 0n:
      A
    case 0n 1n+yp:
      B(yp)
    case 0n 1n+xp:
      C(xp)
    case 1n+xp 1n+yp:
      D(xp, yp)
```
  
Because some scrutinees (`x+1n`, `F(y)`) are expressions rather than variables.

The following function is NOT in proper case-tree form:

```python
def F_D(x: Nat, y: Nat) -> Nat:
  match x y:
    case 0n 0n:
      A
    case 0n 1n+yp:
      B(match yp: case 0n: 0n case 1n+ypp: ypp)
    case 0n 1n+xp:
      C(xp)
    case 1n+xp 1n+yp:
      D(xp, yp)
```

Because the returned expression of the 2nd branch has a `match` inside it.

The following function is NOT in proper case-tree form:

```python
def F_E(x: Nat, y: Nat) -> Nat:
  F(match x y:
    case 0n 0n:
      A
    case 0n 1n+yp:
      B(match yp: case 0n: 0n case 1n+ypp: ypp)
    case 0n 1n+xp:
      C(xp)
    case 1n+xp 1n+yp:
      D(xp, yp))
```

Because its body isn't a match expression directly, but a *function* applied to
a match expression. That causes the whole body to be interpreted as the returned
expression - i.e., it has only one branch - and that branch has a `match` inside
it, so, it isn't proper.

The following function is NOT in proper case-tree form:

```python
def F_F(x: Nat, y: Nat) -> Nat:
  z = x + y
  match x y:
    case 0n 0n:
      A
    case 0n 1n+yp:
      B(match yp: case 0n: 0n case 1n+ypp: ypp)
    case 0n 1n+xp:
      C(xp)
    case 1n+xp 1n+yp:
      D(xp, yp)
```

Because, once again, its body isn't a match expression directly, but an
assignment. It has only one branch, and that branch has matches.

The following function IS in proper case-tree form:

```python
def F_G(x: Nat, y: Nat) -> Nat:
  z = x + y
  F(z + 3n)
```

Because, while it has only one branch, there is no match expression in it.

# Affine Proper Case-Trees

Affine proper case-trees include the additional restrictions that variables must
be used in an *affine* fashion, meaning they only occur *at most once per branch
of variables defined before it*. Examples:

This function IS in affine proper case-tree form (with 2 branches):

```python
def F_H(a: Bool, b: Bool, c: Bool) -> Bool:
  match b:
    case False:
      c
    case True:
      c
```
    
Because it is in proper case-tree form, and the `c` variable occurs only once
per branch of `match b`, and `b` is declared *before* `c`.

This function is NOT in affine proper case-tree form:

```python
def F_I(a: Bool, b: Bool, c: Bool) -> Bool:
  match c:
    case False:
      b
    case True:
      b
```

Because, while it is in affine proper case-tree form, and while the `b` variable
occurs only once per branch of `match c`, the `b` variable is declared *after*
`c`. Internally, this counts as two uses of `b`, thus, its usage is NOT affine.

This function is NOT in affine proper case-tree form:

```python
def F_J(a: Bool, b: Bool, c: Bool) -> Bool:
  match c:
    case False:
      F(b, b)
    case True:
      False
```

Clearly so, since `b` is used twice in the same branch, thus, is NOT affine.

This function IS in affine proper case-tree form:

```python
def F_K(a: Bool, b: Bool, c: Bool) -> Bool:
  match c:
    case False:
      b
    case True:
      c
```

Clearly so, since no variable ever occurs more than once, thus, are all affine.

This function IS in affine proper case-tree form:

```python
def F_L(xs: Bool[]) -> Bool[]:
  match xs:
    case []:
      []
    case x <> xs:
      match x:
        case True:
          xs
        case False:
          True <> xs
```

Because, while `xs` occurs twice, it only occurs once per branch of `match x`,
and `x` was introduced *before* `xs`.

# Lambda-Match Form

Internally, proper case-tree functions are elaborated to nested lambda-matches:

For example, `F_H` is desugared to:

```python
F = λa. λ{
  True: λc. c
  False: λc. c
}
```

And `F_I` is desugared to:

```python
F = λa. λb. λ{
  False: b
  True: b
}
```

Here, you can see why `F_I` isn't affine: in its translation, `λb.` was
introduced before the lambda-match for `c`, causing the `b` variable to occur
twice. Meanwhile, `F_H` *is* affine, because `λc.` was introduced once per
branch, and each `c` variable is bound to that branch's lambda, and, thus,
occurs exactly once.

Definitions that are not proper case-trees can't be elaborated to nested
lambda-matches without creating a new definition.

For example, `F_A` is elaborated to:

```python
F_A = λ{
  0n: λ{
    0n: A
    1n+: λyp. B(yp)
  }
  1n+: λ{
    0n: λxp. λyp. C(xp)
    1n+: λyp. D(xp, yp)
  }
}
```

Meanwhile, `F_C` could, at best, be elaborated to:

```python
F_C = λx. λy. 
  (λ{
    0n: λ{
      0n: A
      1n+: λyp. B(yp)
    }
    1n+: λxp. λ{
      0n: C(xp)
      1n+: λyp. D(xp, yp)
    }
  })(x + 1n, F(y))
```

Which contains a lambda-match application (`(λ{...} ...)`). This form is *not*
allowed on Bend's core, making `F_C` invalid. We could fix `F_C` by splitting
it into multiple definitions:

```python
F_C = λx. λy. 
  F_C_aux(x + 1n, F(y))

F_C_aux = λ{
  0n: λ{
    0n: A
    1n+: λyp. B(yp)
  }
  1n+: λxp. λ{
    0n: C(xp)
    1n+: λyp. D(xp, yp)
  }
}
```

This works, because both definitions are in proper case-tree form.

# Why / when this matters?

In the long-term, most end-users won't need to worry about this low-level
implementation detail, because Bend will automatically convert and split
definitions into proper case-trees. That said, being aware of it might help
having more control, in two ways:

First, by implementing functions in proper case-tree format, the user can
guarantee that they won't be split into auxiliary functions, which can be
helpful when proving theorems (it results in shorter proofs and cleaner
contexts), and is a micro optimization that can be impactiful in some cases.

Second, by re-arranging arguments cleverly (ideally, arguments should be ordered
in the same order they're matched), the user can ensure that variables are
affine (i.e., not cloned), which can be an important optimization in linear
back-ends like the HVM.
