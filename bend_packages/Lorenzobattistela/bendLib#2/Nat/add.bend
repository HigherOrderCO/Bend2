
def Nat/add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      return b
    case 1n+p:
      return one() + Nat/add(p, b)

def one() -> Nat:
  return 1n
