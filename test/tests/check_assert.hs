{-# LANGUAGE MultilineStrings #-}

import Test

-- PARSE ERROR

-- Test the assert syntax feature
assert_bend :: String
assert_bend = """
# Test assert syntax that desugars to def EN : T{A == B} = {==}

# Basic assertions
assert 3n == 3n : Nat
assert True == True : Bool
assert [] == [] : Nat[]

# Test counter increments
def check_e0 : 3n == 3n :: Nat = E0
def check_e1 : True == True :: Bool = E1
def check_e2 : (Nat[]){[] == []} = E2

# Test with type parameters
def id<A>(x: A) -> A:
  x

assert id<Nat>(42n) == 42n : Nat
def check_e3 : id<Nat>(42n) == 42n :: Nat = E3

# Test inline assertions work
def T0 : 3n == 3n :: Nat = {==}
def T1 : True == True :: Bool = {==}
def T2 : (Nat[]){[] == []} = {==}
"""

main :: IO ()
main = testFileChecks assert_bend
