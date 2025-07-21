# FIXME

# fixed by using Let with HOAS binding

###

# an unused variable causes a type mismatch by rewriting goal:


def thm(A:Set, B:Set) -> (∀C:Set. (A->B->C) -> C) -> Σa:A.B:
  x = A
  unused_but_in_goal_1 = Σa:A.B
  unused_but_in_goal_2 = Σa:A.B
  λI.I(Σa:A.B, λa1.λb1.(a1,b1))

  # ✗ thm
  # Mismatch:
  # - Goal: unused_but_in_goal
  # - Type: A & B
  # Context:
  # - A : Set
  # - B : Set
  # - unused_but_in_goal : Set
  # - I : ∀C:Set. (A -> B -> C) -> C
  # - a1 : A
  # - b1 : B
  # Location: (line 7, column 24)
  # 7 |   λI.I(Σa:A.B, λa1.λb1.(a1,b1))
