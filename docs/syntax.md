# Bend Syntax Reference

Bend has Python-like surface syntax, Haskell-like semantics (pure/functional), and Lean-like dependent types and proofs. This document reflects the actual parser and examples in this repository.

## Lexical

- Comments:
  - Line: `# …`
  - Block: `{- … -}` (nests not supported)
- Identifiers: letters, digits, `_`, and `/`; cannot start with a digit. Slash supports hierarchical names like `Nat/add`.
- Reserved words: `match`, `case`, `else`, `elif`, `if`, `end`, `all`, `any`, `finally`, `import`, `as`, `and`, `or`, `def`, `log`, `gen`, `enum`, `assert`, `lambda`.
- Whitespace and newlines are significant for certain constructs (indented `case` blocks). Most forms also have a braced `{ … }` alternative.

## Built‑ins and Literals

- Universes and basic types/values:
  - `Set`
  - `Empty`
  - `Unit`, value `()`
  - `Bool`, values `False`, `True`
  - `Nat`, literals like `0n`, `1n`, `2n`, `42n`
  - Eraser: `*` (erasable value placeholder)
  - Numeric types: `U64`, `I64`, `F64`, `Char`
    - Unsigned integer: `123`, `0xFF`, `0b1011` → `U64`
    - Signed integer: `+123`, `-456`, `+0x1F` → `I64`
    - Float: `3.14`, `-2.0` → `F64`
    - Char: `'a'`, `'\n'`, `'\u0041'` → `Char`
    - String: `"hello"` desugars to a `Char[]` list: `'h' <> 'e' <> … <> []`
- Lists:
  - Empty: `[]`
  - Literal: `[a, b, c]` (desugars via cons)
  - Cons: `head <> tail`
  - Type: `T[]`
- Enums:
  - Type: `enum{&A, &B, &C}`
  - Tag literal: `&Tag` (preferred).
 - Superposition: `&L{a, b}` builds a labeled superposition of `a` and `b` with label `L` (advanced; also has eliminator forms in `λ{…}` and `~ … { … }`).

## Terms and Types

- Function type: `A -> B` (sugar for `all _:A. B`)
- Product type: `A & B` (sugar for `any _:A. B`)
- Dependent function: `all x:A. B` (also `∀ x:A. B`)
- Dependent pair: `any x:A. B` (also `Σ x:A. B`)
- Annotation: `x :: T`
- Equality type: `T{a == b}`; inequality `T{a != b}` is sugar for `Not (T{a==b})`
- Reflexivity proof: `{==}` or `finally`
- Negation (as def): `Not(A: Set) = A -> Empty`

## Variables and Bindings

- Assignment: `x = v; body` or `x : T = v; body` (semicolon optional before a following top‑level or block delimiter). Assignment targets must be variables; attempting to assign to literals/types is a parse error.
- Pattern binding: `pattern = value; body` desugars to a one‑case `match`.

## Functions and Application

- Lambda: `lambda x. body` or `λ x. body`
  - Multiple binders: `lambda x y z. body`
  - Typed binders: `lambda (x: T) (y: U). body`
  - Pattern binders are supported; they desugar to a match on an introduced fresh variable.
- Application: `f(a, b, c)` or parenthesized `(f a b c)`
- Polymorphic application: `f<T, U>(args ...)` desugars to term application of type params first.
- Fixed point: `μ f. body` (rarely needed directly; available for completeness).

## Control Flow and Matching

- If: `if cond: then_branch else: else_branch` (Boolean eliminator)
- Match (indented form):
  ```py
  match x y:
    with a = val, b           # optional “with” moves; bind or alias values
    case pat1 pat2:
      body1
    case pat1' pat2':
      body2
  ```
- Match (braced form):
  ```py
  match x { case pat: body; case pat': body' }
  ```
- Eliminator lambdas: low‑level matches that you can write explicitly:
  - `λ{(): u}` (Unit), `λ{False: f; True: t}` (Bool)
  - `λ{0n: z; 1n+: s}` (Nat)
  - `λ{[]: n; <>: c}` (List)
  - `λ{(,): p}` (Pair)
  - `λ{{==}: k}` (Equality)
  - `λ{@A: a; @B: b}` or `λ{&A: a; &B: b}` (Enum)
- Expression‑match with `~` (applies an eliminator to a scrutinee):
  ```py
  ~ xs { []: n; <>: c }
  ~ b  { False: f; True: t }
  ~ n  { 0n: z; 1n+: s }
  ~ x  { (): u }
  ~ e  { {{==}: k} }
  ~ t  { @A: a; @B: b; default }
  ```
  The braces form supports optional semicolons `;` between arms. An empty `{}` is valid for `Empty`.
- Forks: `fork L: a elif: b elif: c else: d` builds a right‑associated chain `Frk L a (Frk L b (… d))`.
- Rewrite: `rewrite e body` rewrites under equality proof `e`.
- Absurd: `absurd x` is sugar for `match x {}`.
- Return: `return t` is syntactic sugar for just `t`.
- Logging: `log s t` (string/list of chars for `s`) evaluates `t` and emits a log.
- View: `view(name)` enables viewing of named function when pretty‑printing (debug utility).

## Numeric Operators

- Binary: `+`, `-`, `*`, `/`, `%`, `**` (pow), `^` or `xor` (xor), `and`, `or`, comparisons `<`, `<=`, `>`, `>=`, strict eq `===`, strict neq `!==`, bit shifts `<<`, `>>`.
- Unary: `-x`, `not x`.
- Special Nat sugar: when the left operand of `+` is a Nat literal, `k n + t` is parsed as `k` Peano successors on `t`. In patterns, write `1n + p` (or via eliminator `1n+` in λ/`~` forms).

## Datatypes (Sugar)

Datatype declarations synthesize constructors and an encoded dependent pair:

```py
type Maybe<A: Set>:
  case @None:
  case @Some:
    value: A

type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    n: Nat
    h: A
    t: Vec(A,n)
    e: Nat{N == 1n+n}
```

- Constructors:
  - Full: `@Some{value}` → `(&Some,(value,()))`
  - Bare: `@None` allowed only for arity‑0; otherwise use `@Tag{…}`.
  - Disambiguation: if different types share a constructor name, use `@Type::Tag{…}`.
- Patterns accept the same forms: `case @Some{value}: …` or zero‑arity `case @None:`.
- Constructor arity is checked statically at parse time using declarations above.

## Definitions

- Function or value:
  ```py
  def name : Type = term
  def name(x: A, y: B) -> Ret:
    body
  def name<A,B>(x: A) -> Ret:       # generic params become implicit Set‑typed args
    body
  ```
- Datatype: `type …` as above.
- Metavariable context (synthesis playground):
  ```py
  try goal : Type { ctx_term0, ctx_term1, ... }
  try goal<A>(x: T) -> U { ctx... }
  ```
  Creates a hole named `goal` with explicit type and an optional context list.
- Assertions (compile‑time equality checks):
  ```py
  assert A == B : T
  ```
  Desugars to a fresh top‑level definition `E<N> : T{A==B} = {==}`. Fails if unsatisfiable later in checking.

## Imports and Namespaces

- Names can contain `/`: e.g., `Nat/add`.
- Import aliasing:
  ```py
  import Path/To/Lib as Lib
  ```
  After this, `Lib/foo` resolves to `Path/To/Lib/foo` (and `Lib` alone to the directory root). Aliasing applies before reserved‑word checks.
- Auto‑import by reference: using a name like `Foo/bar` triggers loading `Foo/bar.bend` or `Foo/bar/_.bend` if not already in scope.

## Notes on Indentation and Braces

- `match` and `case` support either:
  - Indented form: a colon `:` after `match …` and each `case …:`; out‑denting ends the block.
  - Braced form: `match … { case …: body; case …: body }` with optional semicolons.
- Eliminator forms `λ{…}` and `~ scrut { … }` accept semicolons between arms; the closing `}` ends the form.

## Examples

- See `examples/main.bend` and `examples/prompt.bend` for idiomatic patterns, proofs (`rewrite`, `{==}`), datatypes, and higher‑level programming.

## Type Inference

- Polymorphic applications must be explicit: `List/map<U64,Nat>(f, xs)`; type arguments are not inferred.
