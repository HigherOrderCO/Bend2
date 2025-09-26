
# Pattern Desugaring

This algorithm converts all `Pat`s to native expression-based matches. It removes all the `Pat` terms from the term.

`desugarPats` is the entry point that gets a depth, a Loc span and the term, and returns a `Result Term`.

`Result` is used here to propagate errors.

For most of the terms, this function does nothing but recursively calling itself on subterms.

Recap: pat constructs are:

```
| Pat [Term] [Move] [Case] -- match x ... { with k=v ... ; case @A ...: F ; ... }
```

When we reach a `Pat` constructor, we have three main cases:

- If we have empty cases, there is nothing to desugar.

- If we have a pattern with multiple scrutinees, this is wrong and fails, because the `FlattenPats` algorithm should've removed all the multiple scrutinees match.

- If we have a pattern with one scrutinee, we call the `match` function passing the scrutinee, moves and cases.

The `match` function aims to transform a high level pattern match using `Pat` into a lower level pattern match using the correct construct (i.e `NatM` for `Nat` terms, `BitM` for `Bool` terms and so on).

So, it pattern matches in the type of the cases. If we have a case for `Zer` and a case for `Suc n`, we're in a `NatM`. Note that we have to do it for both combinations (i.e orderings).

`NatM` rule:
```
match x { 0n: z ; 1n+p: s }
---------------------------
~x { 0n: z ; 1n+: λp. s }
```

We recursively `desugarPats` of the zero and suc bodies.

Then we create eliminator branches (for the `Suc n` for examlpe we need to add a lambda to grab the predecessor that we get).

We finalize returning an application of the scrutinee to the Nat match, removing the `Pat` construct successfully.

We also have to handle matches with default cases. Considering the `NatM` with default case, we have:

```
match x { 0n: z ; k: v }
--------------------------------------
~x { 0n: z ; 1n+: λk. v[k := 1n+k] }
```

The main difference in the algorithm here is that we have to bind `k` with the `Suc n` case by name in the term (which in practice translates to specializing it).

This keeps going for all native matches.

The algorithm changes a little bit for custom types (refer to the `inductive types` documentation).

The goal and process is very similar. 

We collect the cases and return case branches and a default branch (if there is one).

After collecting them, we just create an `EnuM` passing the case branches and the default branch (that can be empty).



