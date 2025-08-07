{-# LANGUAGE MultilineStrings #-}

import Test

-- fixed in commit e268c925719922f390686ef0d351cd0f4245fb17
--
-- bug description:
-- Variables coming from let assignments not showing in the context of the error.

-- Given some user-defined ADT with nested fields
-- The HVM compiler doesn't work with nested pattern on constructors


nested_pat_on_ctors :: String
nested_pat_on_ctors = """

type T:
  case A{}:
  case B{}:
    a: T
    b: T

def bad(x: T) -> U64:
  match x:
    case B{A{}, x}:
      0
    case x:
      1

def main : U64 = 123

# the match above desugars into `case (&B, ((#A, ()), (x, ())))`
# It'll match left-to-right, outside-in, so (#A, ()) comes before (x, ()), which is what the compiler expects instead.

# After desugaring and simplifying the match expressions this is the result
# bad : ∀x:T. U64 =
#λx. match x { 
#  case ((_x1,_x2)): match _x1 { 
#    case (&B): match _x2 { 
#        case ((_x3,_x4)): match _x3 {  # Since the first field of @B (bound here to _x3) has nested matching we match first on it and then on the rest of @B
#          case ((_x5,_x6)): match _x5 { 
#            case (&A): match _x6 { 
#              case (()): match _x4 {   # Only here do we match on the second field of @B (x). 
#              case ((x,_x8)): match _x8 { 
#                case (()): 0 
#                case (_x9): 1 
#              } 
#              case (_x7): 1 
#            } 
#            case (_x7): 1 
#          } 
#          case (_x7): 1 
#        } 
#        case (_x5): 1 
#      } 
#      case (_x3): 1 
#    } 
#    case (_x3): 1 
#  } 
#  case (_x1): 1 
#}
"""

main :: IO ()
main = testFileChecks nested_pat_on_ctors

