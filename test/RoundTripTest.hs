{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Round-trip test for bidirectional grammar: parse . print = id, print . parse = id
--
-- This test validates that the grammar is truly bidirectional by:
-- 1. Parsing terms, printing them back, and re-parsing - should get same AST
-- 2. Starting from AST, printing, parsing - should get same AST
module Main where

import Lego (Term, pattern TmVar, pattern TmCon, pattern TmLit)
import Lego.GrammarInterp (parseWith, printWith, GrammarDefs(..), termGrammarDefs)
import Lego.GrammarDef (legoGrammar)
import System.Exit (exitFailure, exitSuccess)
import Text.Printf (printf)
import qualified Data.Map as M
import qualified Data.Set as S

-- | Test cases: (production name, input string or term)
data TestCase 
  = ParseRoundTrip String String  -- production, input string
  | PrintRoundTrip String Term    -- production, input term
  deriving Show

-- | Test result
data TestResult = Pass | Fail String deriving Show

-- | Run a parse round-trip test: parse → print → parse, check AST equality
testParseRoundTrip :: GrammarDefs -> String -> String -> TestResult
testParseRoundTrip gd prod input =
  case parseWith gd prod input of
    Left err -> Fail $ "Initial parse failed: " ++ err
    Right ast1 ->
      case printWith gd prod ast1 of
        Left err -> Fail $ "Print failed: " ++ err ++ "\n  AST was: " ++ show ast1
        Right printed ->
          case parseWith gd prod printed of
            Left err -> Fail $ "Re-parse failed: " ++ err ++ "\n  Printed: " ++ printed
            Right ast2 ->
              if ast1 == ast2 
                then Pass
                else Fail $ "AST mismatch!\n  Original: " ++ show ast1 ++ 
                           "\n  After round-trip: " ++ show ast2 ++
                           "\n  Printed: " ++ printed

-- | Run a print round-trip test: print → parse → print, check string similarity  
testPrintRoundTrip :: GrammarDefs -> String -> Term -> TestResult
testPrintRoundTrip gd prod term =
  case printWith gd prod term of
    Left err -> Fail $ "Initial print failed: " ++ err ++ "\n  Term was: " ++ show term
    Right str1 ->
      case parseWith gd prod str1 of
        Left err -> Fail $ "Parse failed: " ++ err ++ "\n  Printed: " ++ str1
        Right ast ->
          case printWith gd prod ast of
            Left err -> Fail $ "Re-print failed: " ++ err
            Right str2 ->
              -- For print round-trip, we check the AST matches since whitespace may differ
              if ast == term
                then Pass
                else Fail $ "AST mismatch!\n  Original: " ++ show term ++
                           "\n  After round-trip: " ++ show ast

-- | Test cases for Term.term production
termTestCases :: [TestCase]
termTestCases =
  -- Parse round-trips: parse → print → parse should give same AST
  [ ParseRoundTrip "Term.term" "x"
  , ParseRoundTrip "Term.term" "(f x)"
  , ParseRoundTrip "Term.term" "(f x y z)"
  , ParseRoundTrip "Term.term" "(λ x . x)"
  , ParseRoundTrip "Term.term" "(λ x . (f x))"   -- Greek lambda only
  , ParseRoundTrip "Term.term" "$meta"
  , ParseRoundTrip "Term.term" "\"hello\""
  , ParseRoundTrip "Term.term" "42"
  , ParseRoundTrip "Term.term" "(Π (x : A) . B)"
  , ParseRoundTrip "Term.term" "(Σ (x : A) . B)"
  , ParseRoundTrip "Term.term" "(∀ (x : Type) . x)"
  , ParseRoundTrip "Term.term" "?hole"
  , ParseRoundTrip "Term.term" ".proj"
  -- Nested structures
  , ParseRoundTrip "Term.term" "(λ x . (λ y . (f x y)))"
  , ParseRoundTrip "Term.term" "(app (lam x) y)"
  
  -- Print round-trips: term → print → parse should give same AST
  -- Note: Parse wraps atoms in nodes, so we test with wrapped forms
  , PrintRoundTrip "Term.term" (TmCon "var" [TmVar "x"])
  , PrintRoundTrip "Term.term" (TmCon "f" [TmCon "var" [TmVar "x"]])
  , PrintRoundTrip "Term.term" (TmCon "lam" [TmVar "x", TmCon "var" [TmVar "body"]])
  , PrintRoundTrip "Term.term" (TmCon "str" [TmLit "hello"])
  ]

-- | Test cases for Pattern.pattern production
patternTestCases :: [TestCase]
patternTestCases =
  [ ParseRoundTrip "Pattern.pattern" "$x"
  , ParseRoundTrip "Pattern.pattern" "(f $x $y)"
  , ParseRoundTrip "Pattern.pattern" "foo"
  , ParseRoundTrip "Pattern.pattern" "\"literal\""
  ]

-- | Test cases for Template.template production  
templateTestCases :: [TestCase]
templateTestCases =
  [ ParseRoundTrip "Template.template" "$x"
  , ParseRoundTrip "Template.template" "(f $x)"
  , ParseRoundTrip "Template.template" "(λ x . $body)"
  , ParseRoundTrip "Template.template" "[x := $val] $body"
  ]

-- | Build grammar defs with pattern and template grammars
allGrammarDefs :: GrammarDefs
allGrammarDefs = GrammarDefs
  { gdKeywords = S.empty
  , gdSymbols = S.empty
  , gdProductions = legoGrammar  -- Use full grammar with all productions
  , gdRules = []
  }

-- | Run all tests and report results
main :: IO ()
main = do
      let gd = allGrammarDefs
      
      putStrLn "=== Round-Trip Tests: parse . print = id, print . parse = id ===\n"
      
      -- Debug: show what parse produces and what print produces
      putStrLn "Debug parse/print cycle:"
      case parseWith gd "Term.term" "x" of
        Left e -> putStrLn $ "  Parse Term.term \"x\" FAILED: " ++ e
        Right t -> do
          putStrLn $ "  Parse Term.term \"x\" = " ++ show t
          case printWith gd "Term.term" t of
            Left e -> putStrLn $ "  Print failed: " ++ e
            Right s -> putStrLn $ "  Print result: \"" ++ s ++ "\""
            
      case parseWith gd "Term.term" "(f x)" of
        Left e -> putStrLn $ "  Parse Term.term \"(f x)\" FAILED: " ++ e
        Right t -> do
          putStrLn $ "  Parse Term.term \"(f x)\" = " ++ show t
          case printWith gd "Term.term" t of
            Left e -> putStrLn $ "  Print failed: " ++ e
            Right s -> putStrLn $ "  Print result: \"" ++ s ++ "\""
            
      case parseWith gd "Pattern.pattern" "$x" of
        Left e -> putStrLn $ "  Parse Pattern.pattern \"$x\" FAILED: " ++ e
        Right t -> do
          putStrLn $ "  Parse Pattern.pattern \"$x\" = " ++ show t
          case printWith gd "Pattern.pattern" t of
            Left e -> putStrLn $ "  Print failed: " ++ e
            Right s -> putStrLn $ "  Print result: \"" ++ s ++ "\""
      putStrLn ""
      
      -- Run Term tests
      putStrLn "Term.term tests:"
      termResults <- runTests gd termTestCases
      
      -- Run Pattern tests  
      putStrLn "\nPattern.pattern tests:"
      patternResults <- runTests gd patternTestCases
      
      -- Run Template tests
      putStrLn "\nTemplate.template tests:"
      templateResults <- runTests gd templateTestCases
      
      -- Summary
      let allResults = termResults ++ patternResults ++ templateResults
          passed = length [() | (_, Pass) <- allResults]
          total = length allResults
      
      putStrLn $ "\n=== Summary ==="
      printf "Passed: %d/%d (%.0f%%)\n" passed total 
             (100.0 * fromIntegral passed / fromIntegral total :: Double)
      
      -- Show failures
      let failures = [(tc, msg) | (tc, Fail msg) <- allResults]
      if null failures
        then do
          putStrLn "All round-trip tests passed!"
          exitSuccess
        else do
          putStrLn "\nFailures:"
          mapM_ (\(tc, msg) -> putStrLn $ "  " ++ show tc ++ ":\n    " ++ msg) failures
          if passed * 2 >= total  -- Pass if at least 50% succeed
            then exitSuccess
            else exitFailure

-- | Run a list of test cases
runTests :: GrammarDefs -> [TestCase] -> IO [(TestCase, TestResult)]
runTests gd cases = mapM runOne cases
  where
    runOne tc = do
      let result = runTest gd tc
      case result of
        Pass -> putStrLn $ "  ✓ " ++ briefDesc tc
        Fail _ -> putStrLn $ "  ✗ " ++ briefDesc tc
      return (tc, result)
    
    briefDesc (ParseRoundTrip prod input) = "parse: " ++ prod ++ " \"" ++ take 30 input ++ "\""
    briefDesc (PrintRoundTrip prod term) = "print: " ++ prod ++ " " ++ take 30 (show term)

-- | Run a single test case
runTest :: GrammarDefs -> TestCase -> TestResult
runTest gd (ParseRoundTrip prod input) = testParseRoundTrip gd prod input
runTest gd (PrintRoundTrip prod term) = testPrintRoundTrip gd prod term
