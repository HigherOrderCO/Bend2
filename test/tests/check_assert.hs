{-# LANGUAGE MultilineStrings #-}

import Test

-- PARSE ERROR

-- Test the assert syntax feature
assert_bend :: String
assert_bend = """
assert 3n == 3n : Nat
assert True == True : Bool
assert [] == [] : Nat[]

# Test counter increments
def check_e0 : Nat{3n == 3n} = E0
def check_e1 : Bool{True == True}  = E1
def check_e2 : (Nat[]){[] == []} = E2

# Test with type parameters
def id<A>(x: A) -> A:
  x

assert id<Nat>(42n) == 42n : Nat
def check_e3 : Nat{id<Nat>(42n) == 42n} = E3

# Test inline assertions work
def T0 : Nat{3n == 3n} = {==}
def T1 : Bool{True == True} = {==}
def T2 : (Nat[]){[] == []} = {==}

"""

main :: IO ()
main = testFileChecks assert_bend
