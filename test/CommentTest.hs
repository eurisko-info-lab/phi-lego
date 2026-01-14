-- | Test comment preservation in tokenization
module Main where

import Lego.Token

main :: IO ()
main = do
  putStrLn "=== Comment Preservation Tests ==="
  
  -- Test 1: Line comment preservation
  let toks1 = tokenizePreservingComments ["->"] "x -- comment\ny"
  putStrLn $ "Line comment: " ++ show toks1
  case [t | t@(TComment _) <- toks1] of
    [TComment c] | "--" `isPrefixOf` c -> putStrLn "✓ Line comment preserved"
    _ -> putStrLn "✗ Line comment NOT preserved"
  
  -- Test 2: Block comment preservation
  let toks2 = tokenizePreservingComments ["->"] "x /- block -/ y"
  putStrLn $ "Block comment: " ++ show toks2
  case [t | t@(TComment _) <- toks2] of
    [TComment c] | "/-" `isPrefixOf` c -> putStrLn "✓ Block comment preserved"
    _ -> putStrLn "✗ Block comment NOT preserved"
  
  -- Test 3: Standard tokenization (no comments)
  let toks3 = tokenizeWithSymbols ["->"] "x -- comment\ny"
  putStrLn $ "Without preservation: " ++ show toks3
  case [t | t@(TComment _) <- toks3] of
    [] -> putStrLn "✓ Comments stripped (as expected)"
    _ -> putStrLn "✗ Comments should NOT be preserved"

isPrefixOf :: String -> String -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
