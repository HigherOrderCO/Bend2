module Core.Gen.Parser
  ( parseGeneratedTerm
  , parseGeneratedTerms
  ) where

import Target.HVM (HCore)

import Core.Gen.HVM.Parse (parseGeneratedTerm)

parseGeneratedTerms :: String -> Either String [HCore]
parseGeneratedTerms input = fmap pure (parseGeneratedTerm input)
