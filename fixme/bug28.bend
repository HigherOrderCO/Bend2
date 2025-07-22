# FIXME

###

# incorrect annotation of doesn't stop the check from passing

def proj(p:Σa:Nat.Nat) -> Nat:
  (m :: Bool) : Nat = ~p{(,):λx.λy.x}
  m

def main() -> Nat:
  proj((2n,10n))

  # ✓ main
  # ✓ proj
  #
  # 1n+1n+0n
