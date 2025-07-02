def blaim()->Nat:22n


type Vec<A: Set>(N: Nat) -> Set:
  case @Nil:
    e: Nat{N == 0n}
  case @Cons:
    k: Nat
    h: A
    t: Vec(A, k)
    e: Nat{N == (1n+k)}


def mkv () -> Vec<I64>(0n):
  @Nil{finally}


def add(a:Nat, b:Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n + p:
      1n + add(p,b)



def zero_right(a: Nat) -> Nat{a == add(a,0n)}:
  match a:
    case 0n:
      finally
    case 1n + p:
      1n + zero_right(p)


def zeroaddright () -> Nat{1n == add(0n, 1n)}:
  finally

def addoneright(a:Nat) -> Nat{(a+ 1n) == add(a, 1n)}:
  # finally
  match a:
  case 0n:
  # finally
  zeroaddright()

  case 1n + p:
  finally


# # Add: reduce succ on right
# def succ_right(a: Nat, b: Nat) -> Nat{add(a,1n+b) == (1n+add(a,b))}:
#   match a:
#     case 0n:
#       finally
#     case 1n + ap:
#       1n + succ_right(ap,b)


# def app
#   ( A: Set
#   , B: Set
#   , a: A
#   , b: A
#   , f: A -> B
#   , e: A{a == b}
#   ) -> B{f(a) == f(b)}:
#   rewrite e
#   finally


# # def comm(a:Nat, b:Nat) -> Nat{add(a,b) == add(b,a)}
# #   match a:
# #     case 0n:
# #       zero_right(b)

# # def p0() -> Nat{(0n + 1n + 0n) == (1n + 0n)}:
# #   finally

# # def pp (k:Nat) -> Nat{(k + 1n) == (1n + k)} :
# #   match k:
# #     case 0n:
# #       p0()
# #     case 1n + p:
# #       finally

# # def mkvv() -> Vec<I64>(1n):
# #   @Cons{
# #     0n,
# #     +99,
# #     mkv(),
# #     finally
# #   }





# type sw () -> Set:
#   case @A:
#     x: Nat
#     p: Nat{2n == 2n}

# def sfn () -> sw:

#   @A{2n, finally}



# def vv () -> Nat: 22n

# def main() -> Set:
#   sw
  