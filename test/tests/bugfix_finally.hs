{-# LANGUAGE MultilineStrings #-}

-- fixed in commit (BenGen-align branch) 6fc55e28e93f25f6f3f2926728908be1e6bb3ba2

-- bug description:
-- this should check but doesn't:
--
-- PARSE_ERROR
-- reserved keyword 'finally'
--
-- At line 10, column 3:
-- 10 |   finally
--
import Test

finally_ :: String
finally_ = """
def t(A:Set, a:A) -> a==a :: A:
  finally

"""

main :: IO ()
main = testFileChecks finally_
