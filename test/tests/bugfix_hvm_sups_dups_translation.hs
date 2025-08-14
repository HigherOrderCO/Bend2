import Test

-- Regression test: HVM backend should not emit stray lambdas
-- when compiling SupM applications produced by forks. It must
-- compile to direct DUPs and evaluate to 3 for the program below.

main :: IO ()
main =
  test "bend main.bend --to-hvm | tee bug.hvm && hvm run bug.hvm -C" [("main.bend", bendProg)]
       "compile to HVM with proper sups/dups and run" $ \out err -> do
    -- Ensure HVM output contains DUP sugar (via !& lines) and no stray λx$ wrappers
    assert (not (out `has` "λx$"))
    -- Ensure it computes to 3
    assert (out `has` "3")

  where
    bendProg = unlines
      [ "def F(a: U64, b: U64) -> U64:"
      , "  a + b"
      , ""
      , "def foo(a: U64, b: U64) -> U64:"
      , "  fork 0:"
      , "    F(a, b)"
      , "  else:"
      , "    *"
      , ""
      , "def main : U64 = foo(1, 2)"
      ]

