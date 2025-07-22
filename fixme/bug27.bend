# FIXME

###

# can't infer type of pair projection in assigment

def proj(p:Σa:Nat.Nat) -> Nat:
  m = ~p{(,):λx.λy.x}
  ()

  # ✗ proj
  # CantInfer:
  # Context:
  # - p : Σa:Nat. Nat
  # Location: (line 8, column 7)
  # 8 |   m = ~p{(,):λx.λy.x}
