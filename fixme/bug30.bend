# FIXME

# fixed. parseTermBefore should restore the blocked ops always
# even when its internal parseTerm fails. with this, additional
# parseTermBefore have to be used e.g. in parsing 'case ...:`

###

# when used under the combinator 'some',
# parseTermBefore "op" is not reseting the block list
# causing ":" to be blocked beyond where it was intended to

def f(a:Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      1n

def g() -> Nat:
  a = 0n :: Nat
  a

  # PARSE_ERROR
  # unexpected ":: Nat<newline>"
  # expecting "def", "import", "type", '(', ';', Eraser, absurd, character literal, dependent function type, dependent pair type, empty list ([]), end of input, enum symbol / constructor, enum type, fixed point, fork, if clause, lambda abstraction, list literal, log, natural number literal, natural number type (Nat), numeric literal, numeric unary operation, pattern match, reflexivity ({==} or finally), return statement, rewrite, string literal, superposition, tilde expression (induction or match), unit value (()), variable, or view
  #
  # At line 9, column 10:
  # 9 |   a = 0n :: Nat
