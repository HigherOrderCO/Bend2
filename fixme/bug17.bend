# not a bug
# use Σx:Nat.Nat instead. ΣNat.F accepts a function and can be used with lambda
# cases, like ΣNat.λ{0n:...;1n+:...}

###

# this gives the error

  # ✗ f
  # Mismatch:
  # - Goal: Nat -> Set
  # - Type: Set
  # Context:
  #
  # Location: (line 18, column 17)
  # 18 | def f() -> ΣNat.Nat:
  #                      ^ (color pointer points here)

# unless we turn right-hand type into an explicit function λa.Nat

def f() -> ΣNat.Nat:
  (0n,1n)
