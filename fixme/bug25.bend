# FIXME

# fixed by using Let with HOAS binding

###

# can't infer the type of a String

def main() -> Char[]:
  x = "x"
  x
  
  # ✗ main
  # CantInfer:
  # Context:
  #
  # Location: (line 8, column 7)
  # 8 |   x = "x"
