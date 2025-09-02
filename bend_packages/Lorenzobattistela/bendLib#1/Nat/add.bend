
def Nat/add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      return b
    case 1n+p:
      return 1n + Nat/add(p, b)
