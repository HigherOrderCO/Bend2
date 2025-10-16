# Bend Pretty-Printing Algorithm

This document describes the deterministic procedure for translating mined HVM lambda terms into structured Bend source. The description operates purely on raw lambda terms; it does not depend on any runtime specifics of the Kolmo/HVM implementation.

## Overview

Given a normalized lambda term `λh₁. … λhₖ. λf. body`, where:

- `h₁ … hₖ` are auxiliary helper lambdas supplied via the generator context (library imports, higher-order parameters, etc.).
- `f` is the recursive function binder corresponding to the goal definition.
- `body` is built from eliminators (matchers), constructors, variables, and references.

The prettifier reconstructs a Bend `def` by:

1. **Stripping helper lambdas** so the Bend definition exposes only the user-declared arguments.
2. **Recovering the parameter queue** from the generator signature (or equivalent metadata) in the declared order.
3. **Walking the body** with a queue-based environment that tracks which lambda binders and matcher introductions correspond to each Bend pattern variable.
4. **Printing matches and returns** by consuming queue entries exactly at the points where the original term introduced lambdas, ensuring predecessor/head/tail bindings stay in sync with the user-level structure.

The queue discipline mirrors the step-by-step procedure below.

## Queue-Based Traversal

1. **Initial queue** – Start with the ordered list of function parameters. For `def sort(n, m, o)`, the queue is `[n, m, o]`. Helper binders do *not* appear in the queue after they are stripped.
2. **Encountering a matcher** – When the term introduces a matcher (e.g., `λ{0n: …; 1n+: …}` for natural numbers):
   - Pop the next variable name from the front of the queue; this is the scrutinee.
   - Emit the corresponding `match <name>:` in Bend.
   - For each branch, clone the remaining queue before descending.
3. **Zero/base branches** – Inside a base case (e.g., the `0n` arm), the queue clone is used as-is. Any nested lambdas consume names from the *front* of that branch’s queue clone to obtain the appropriate Bend binders.
4. **Successor/inductive branches** – Before entering the successor arm body, push the new binder (predecessor) to the *front* of that branch’s queue clone. For natural numbers this is usually `p`; for lists, both head and tail are pushed in order (`h` first, then `t`).
5. **Nested matchers** – Repeat steps 2–4 recursively. Each matcher consumes the next queued name and pushes any branch-specific binders to the front before processing sub-bodies.
6. **Return expressions** – When reaching a leaf expression (no further lambda/matcher nodes), emit `return …`. Variable occurrences look up their mapped Bend names from the current environment (including helpers and dynamically introduced binders).

## Worked Example

Consider the normalized term:

```
λinc.λsort.λ{0n:λa.λb.[];1n+:λa.λ{[]:λb.inc(sort(a,b,[]));<>:λ{0n:λb.λc.(0n<>sort(1n+a,b,c));1n+:λb.λc.λd.sort(1n+a,c,(b<>d))}}}
```

This term corresponds to the function signature:

```
def sort(n : Nat, m : Nat[], o : Nat[]) -> Nat[]
```

Walking the term step by step:

1. Strip helper lambdas (`λinc`, `λsort`). Queue starts as `[n, m, o]`.
2. Encounter the outer matcher on `n`: pop `n`, emit `match n:`.
3. Zero branch (`0n`):
   - Queue clone is `[m, o]`.
   - Two lambdas consume `m` then `o`, resulting in `return []`.
4. Successor branch (`1n+`):
   - Push predecessor `p` to front → queue becomes `[p, m, o]`.
   - Lambda binds `p`, leaving `[m, o]`.
   - Nested matcher on `m`: pop `m`, emit `match m:`.
     - `[]` branch: lambda binds `o`; emit `return inc(sort(p, o, []))`.
     - `<>` branch:
       - Push head/tail to front → queue `[h, t, o]`.
       - Nested matcher on `h`: pop `h`, emit `match h:`.
         - `0n` branch: lambdas bind `t`, `o`; emit `return 0n <> sort(1n+p, t, o)`.
         - `1n+` branch:
           - Push predecessor `p1` → queue `[p1, t, o]`.
           - Lambdas bind `p1`, `t`, `o`; emit `return sort(1n+p, t, (p1 <> o))`.

This produces the Bend definition:

```
def sort(n : Nat, m : Nat[], o : Nat[]) -> Nat[]:
  match n:
    case 0n:
      return []
    case 1n+p:
      match m:
        case []:
          return inc(sort(p, o, []))
        case h <> t:
          match h:
            case 0n:
              return 0n <> sort(1n+p, t, o)
            case 1n+p1:
              return sort(1n+p, t, (p1 <> o))
```

The algorithm is purely mechanical: every introduction in the lambda term consumes or prepends entries in the parameter queue, guaranteeing that bindings remain aligned with their corresponding Bend pattern variables. No heuristics are involved; once the helper lambdas are removed and the initial queue is established, the traversal is deterministic.
