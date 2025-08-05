# Bend Language Syntax Reference

Bend is a functional programming language with Python-inspired syntax, Haskell-like semantics, and a Lean-like dependent type system. This comprehensive reference covers all syntax constructs with examples.

## Table of Contents

- [Comments](#comments)
- [Basic Types](#basic-types)
- [Variables and Names](#variables-and-names)
- [Functions](#functions)
- [Pattern Matching](#pattern-matching)
- [Data Types](#data-types)
- [Type System](#type-system)
- [Operators](#operators)
- [Control Flow](#control-flow)
- [Advanced Features](#advanced-features)
- [Imports and Modules](#imports-and-modules)

## Comments

```bend
# Single line comment
```

Comments start with `#` and continue to the end of the line.

## Basic Types

### Primitive Types

```bend
Set      # Type universe
Empty    # Empty type (⊥)
Unit     # Unit type 
()       # Unit value
Bool     # Boolean type  
False    # Boolean false value
True     # Boolean true value
Nat      # Natural number type
0n       # Zero (natural number literal)
123n     # Natural number literals
```

### Numeric Types

```bend
U64      # Unsigned 64-bit integer type
I64      # Signed 64-bit integer type
F64      # 64-bit floating point type
Char     # Character type
123      # U64 literal (unsigned)
+123     # I64 literal (signed positive)
-456     # I64 literal (signed negative)
123.0    # F64 literal (floating point)
'x'      # Character literal
```

**Numeric Literal Formats:**
- Decimal: `123`, `+456`, `-789`
- Hexadecimal: `0xFF`, `0x123ABC`
- Binary: `0b1010`, `0b11110000`
- Float: `3.14`, `-2.71`, `+1.0`

### String and Character Literals

```bend
'a'           # Character literal
'\n'          # Escaped newline
'\t'          # Escaped tab
'\u0041'      # Unicode escape (A)

"hello"       # String literal (desugars to character list)
"hello\n"     # String with newline
"unicode: \u03B1"  # String with Unicode
```

**String Desugaring:**
`"abc"` desugars to `'a' <> 'b' <> 'c' <> []`

### Compound Types

```bend
T[]              # List of T
A -> B           # Function type (sugar for ∀_:A. B)
A & B            # Product type (sugar for ∀_:A. B)
∀x:A. B          # Dependent function type (Π-type)
∀x:A y:B. C      # Multi-argument dependent function
any x:A. B       # Dependent pair type (Σ-type)
any x:A y:B. C   # Multi-argument dependent pair
T{a == b}        # Propositional equality type
T{a != b}        # Propositional inequality type
```

**Unicode Alternatives:**
- `∀` can be written as `all`
- `Σ` can be written as `any`
- `λ` can be written as `lambda`

### Enum Types

```bend
enum{&A, &B, &C}  # Inline enum type
&Tag              # Enum value/symbol
```

## Variables and Names

### Variable Patterns

```bend
x               # Simple variable
foo_bar         # Variable with underscore
Type123         # Variables can contain numbers
Nat/add         # Namespaced variable (module path)
```

### Variable Bindings

```bend
x = value           # Untyped assignment
x : Type = value    # Typed assignment
```

## Functions

### Lambda Expressions

```bend
lambda x. expr          # Single argument lambda
lambda x y z. expr      # Multi-argument lambda (curried)
λx. expr               # Unicode lambda
λx y. expr             # Multi-argument unicode lambda

# Pattern lambdas
lambda (x, y). expr     # Tuple pattern
lambda @Some{value}. expr  # Constructor pattern
```

### Function Definitions

```bend
# Simple function definition
def identity<A>(x: A) -> A:
  x

# Multi-argument function
def add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p, b)

# Type parameters
def map<A, B>(f: A -> B, xs: A[]) -> B[]:
  match xs:
    case []:
      []
    case h <> t:
      f(h) <> map<A, B>(f, t)
```

### Function Application

```bend
f(x)                    # Single argument
f(x, y, z)             # Multiple arguments
f<Type1, Type2>(x, y)  # Polymorphic application
```

**Note:** All functions actually take one argument. Multi-argument syntax is sugar for curried functions.

## Pattern Matching

### Basic Pattern Matching

```bend
# Boolean patterns
if condition:
  trueCase
else:
  falseCase

# Natural number patterns
match n:
  case 0n:
    zeroCase
  case 1n + p:
    successorCase

# List patterns
match list:
  case []:
    emptyCase
  case head <> tail:
    consCase
```

### Advanced Pattern Matching

```bend
# Multiple scrutinees
match x y:
  case 0n True:
    case1
  case 1n+a False:
    case2

# With clauses for linearization
match vec:
  with length = Vec/length(vec)
  case @Nil{}:
    handleEmpty
  case @Cons{n, h, t}:
    handleCons
```

### Constructor Patterns

```bend
# Simple constructor patterns
match maybe:
  case @None{}:
    default
  case @Some{value}:
    value

# Constructor patterns with equalities
match vec:
  case @Nil{e}:        # e : Nat{length == 0}
    handleEmpty
  case @Cons{n, h, t, e}:  # e : Nat{length == 1+n}
    handleCons
```

### Lambda-Match Expressions

```bend
# Unit eliminator
λ{(): result}

# Boolean eliminator
λ{False: falseCase; True: trueCase}

# Natural number eliminator
λ{0n: zeroCase; 1n+: successorCase}

# List eliminator
λ{[]: nilCase; <>: consCase}

# Tuple eliminator
λ{(,): pairFunction}

# Equality eliminator
λ{{==}: equalityFunction}

# Enum eliminator
λ{&A: caseA; &B: caseB; default}
```

## Data Types

### Simple Algebraic Data Types

```bend
# Maybe type
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A
```

### Recursive Data Types

```bend
# List type
type List<A: Set>:
  case @Nil:
  case @Cons:
    head: A
    tail: List<A>

# Binary tree
type Tree<A: Set>:
  case @Leaf:
    value: A
  case @Node:
    left: Tree<A>
    right: Tree<A>
```

### Inductive Types with Indices

```bend
# Length-indexed vectors
type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    head: A
    tail: Vec<A, n>
    e: Nat{N == 1n + n}
```

### Constructor Usage

```bend
# Constructor syntax
@None{}                    # Empty constructor
@Some{42}                  # Constructor with single field
@Cons{1n, 'a', @Nil{}}    # Constructor with multiple fields

# Desugaring
@None{}        # → (&None, ())
@Some{value}   # → (&Some, value, ())
```

## Type System

### Type Annotations

```bend
x :: Type              # Type ascription
```

### Dependent Types

```bend
# Dependent function types
∀n:Nat. Vec<A, n>     # Vector of length n
∀A:Set. A -> A        # Polymorphic identity type

# Dependent pair types
any n:Nat. Vec<A, n>  # Existential length vector
any A:Set x:A. P(x)   # Dependent pair
```

### Equality Types

```bend
# Propositional equality
Nat{a == b}           # Type of proofs that a equals b
A{x != y}             # Type of proofs that x doesn't equal y

# Equality proofs
{==}                  # Reflexivity proof
finally               # Alternative syntax for reflexivity
```

### Type Definitions

```bend
# Type aliases
def String() -> Set:
  Char[]

# Complex type definitions
def Equal<A: Set>(x: A, y: A) -> Set:
  ∀P: A -> Set. P(x) -> P(y)
```

## Operators

### Arithmetic Operators

```bend
a + b       # Addition (or Nat successor: 3n + x)
a - b       # Subtraction
a * b       # Multiplication
a / b       # Division
a % b       # Modulo
a ** b      # Exponentiation
-x          # Negation
```

### Comparison Operators

```bend
a === b     # Equality
a !== b     # Inequality
a < b       # Less than
a > b       # Greater than
a <= b      # Less than or equal
a >= b      # Greater than or equal
```

### Logical Operators

```bend
a and b     # Logical AND
a or b      # Logical OR
a xor b     # Logical XOR
not x       # Logical NOT
```

### Bitwise Operators

```bend
a << b      # Left shift
a >> b      # Right shift
a ^ b       # Bitwise XOR
```

### List Operators

```bend
head <> tail    # List cons
```

### Type Operators

```bend
A -> B          # Function type
A & B           # Product type
A[]             # List type
```

## Control Flow

### Conditional Expressions

```bend
if condition:
  thenBranch
else:
  elseBranch
```

### Pattern Matching

```bend
match expression:
  case pattern1:
    body1
  case pattern2:
    body2
```

### Fork Expressions

```bend
fork label:
  branchA
else:
  branchB

# Multi-way fork
fork label:
  branchA
elif:
  branchB
elif:
  branchC
else:
  branchD
```

## Advanced Features

### Fixed Points

```bend
μf. expression        # Fixed point operator
```

### Rewriting

```bend
rewrite proof body    # Rewrite using equality proof
```

### Superposition

```bend
&L{a, b}             # Superposition with label L
```

### Logging

```bend
log "message" expr   # Log message and continue with expr
```

### Holes and Metavariables

```bend
()                   # Hole (in proof context)
try name : Type      # Metavariable declaration
```

### View Functions

```bend
view(functionName)   # Reference to function's "$" variant
```

## Imports and Modules

### Import Statements

```bend
import Path/To/Module as Alias
```

### Automatic Imports

Bend automatically imports definitions based on their usage:
- `Foo/bar(123)` automatically imports from `./Foo/bar.bend` or `./Foo/bar/_.bend`

### Module Paths

```bend
Nat/add             # Function from Nat module
List/map            # Function from List module
Vec/head            # Function from Vector module
```

## Literals and Special Values

### List Literals

```bend
[]                  # Empty list
[1, 2, 3]          # List literal
```

### Tuple Literals

```bend
(a, b)              # Pair
(a, b, c)           # Triple (desugars to (a, (b, c)))
```

### Special Values

```bend
*                   # Eraser
()                  # Unit value / hole
{==}                # Reflexivity proof
finally             # Alternative reflexivity syntax
```

## Error Handling

### Absurd

```bend
absurd proof        # Eliminate impossible case
# Desugars to: match proof {}
```

## Syntax Sugar Summary

- `A -> B` ≡ `∀_:A. B`
- `A & B` ≡ `any _:A. B`
- `"string"` ≡ `'s' <> 't' <> 'r' <> 'i' <> 'n' <> 'g' <> []`
- `@Tag{}` ≡ `(&Tag, ())`
- `@Tag{f1, f2}` ≡ `(&Tag, f1, f2, ())`
- `T{a != b}` ≡ `Not(T{a == b})`
- `absurd e` ≡ `match e {}`
- `finally` ≡ `{==}`
- `all` ≡ `∀`
- `any` ≡ `Σ`
- `lambda` ≡ `λ`

## Examples

See the [Getting Started Guide](getting-started.md) and [Examples](examples.md) for complete working examples of Bend programs.