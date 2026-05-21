{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Good.FourEtaRedexStrategies

main :: IO ()
main = do
  assert "leaving eta-redexes keeps the tail-call continuation eta-expanded" $
    containsReifiedContinuationEtaRedex (topLevelLeaveEta sampleTailCall "topK")
  assert "construct-time eta detection removes the eta-redex" $
    not (containsReifiedContinuationEtaRedex (topLevelDetectEta sampleTailCall "topK"))
  assert "the inherited tail-call attribute removes the eta-redex" $
    not (containsReifiedContinuationEtaRedex (topLevelInheritedTail sampleTailCall "topK"))
  assert "duplicated tail-call rules remove the eta-redex" $
    not (containsReifiedContinuationEtaRedex (topLevelDuplicatedRules sampleTailCall "topK"))

assert :: String -> Bool -> IO ()
assert label condition =
  if condition
    then putStrLn ("pass: " <> label)
    else fail ("fail: " <> label)
