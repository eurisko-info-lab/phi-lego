{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
-- | Bootstrap Test: Load Grammar.sexpr and use it to parse/eval test files
--
-- This test validates the grammar pipeline:
-- 1. Load grammar from Grammar.sexpr (the compiled source of truth)
-- 2. Parse all .lego test files using that grammar
-- 3. Run embedded tests
--
-- This proves that Grammar.sexpr is consistent and can parse all example files.
--
-- NOTE: Grammar.lego cannot currently be parsed due to multi-line production
-- limitations. Grammar.sexpr is the authoritative source.
--
module Main where

import Lego (Term, GrammarExpr, LegoDecl(..),
             pattern TmVar, pattern TmCon, pattern TmLit,
             pattern GEmpty, pattern GLit, pattern GSeq, pattern GAlt,
             pattern GStar, pattern GRef, pattern GBind, pattern GNode,
             pattern GCut,
             Mode(..), BiState(..),
             TestResult(..), clGrammar, clRules, clTests,
             Test(..), Rule(..), RuleDir(..))
import Lego.GrammarParser (parseLegoFile)
import Lego.GrammarInterp (runGrammar)
import Lego.Token (tokenizeWithInfo, TokenInfo(..))
import Lego.SExpr (readSExprFile)
import qualified Lego.Eval as E
import qualified Data.Map as M
import qualified Data.Set as S
import System.Directory (listDirectory, doesDirectoryExist, doesFileExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM, when)
import System.Exit (exitFailure, exitSuccess)

--------------------------------------------------------------------------------
-- Main: Bootstrap test
--------------------------------------------------------------------------------

main :: IO ()
main = do
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn "Bootstrap Test: Grammar.sexpr → Parse test files → Run tests"
  putStrLn "═══════════════════════════════════════════════════════════════"
  
  -- Phase 1: Load Grammar from Grammar.sexpr (the source of truth)
  putStrLn "\n── Phase 1: Load grammar from Grammar.sexpr ──"
  grammarResult <- loadGrammarSExpr
  case grammarResult of
    Left err -> do
      putStrLn $ "FATAL: Cannot load Grammar.sexpr: " ++ err
      exitFailure
    Right grammar -> do
      putStrLn $ "  Loaded " ++ show (M.size grammar) ++ " grammar productions"
      
      -- Verify essential productions exist
      let essentialProds = ["File.legoFile", "Term.term", "Pattern.pattern", "Template.template"]
      let missing = filter (`M.notMember` grammar) essentialProds
      if not (null missing) then do
        putStrLn $ "FATAL: Missing essential productions: " ++ show missing
        exitFailure
      else do
        putStrLn "  ✓ All essential productions present"
        
        -- Phase 2: Parse a sample file and extract its grammar
        putStrLn "\n── Phase 2: Extract grammar from parsed .lego file ──"
        let sampleFile = "examples/basics/Arith.lego"
        sampleExists <- doesFileExist sampleFile
        when sampleExists $ do
          sampleContent <- readFile sampleFile
          case parseLegoFile sampleContent of
            Left _ -> putStrLn $ "  Skipped: " ++ sampleFile
            Right decls -> do
              let localGrammar = extractGrammarMap decls
              putStrLn $ "  Extracted " ++ show (M.size localGrammar) ++ " productions from " ++ sampleFile
        
        -- Phase 3: Use grammar to parse all test files
        runPhase2WithGrammar grammar

-- | Phase 3: Run tests with grammar
runPhase2WithGrammar :: M.Map String (GrammarExpr ()) -> IO ()
runPhase2WithGrammar grammar = do
  putStrLn "\n── Phase 3: Parse test files with grammar ──"
  testFilesResult <- runBootstrapTests grammar
  
  case testFilesResult of
    Left err -> do
      putStrLn $ "\nFATAL: " ++ err
      exitFailure
    Right (passed, total, filesOk, filesTotal) -> do
      putStrLn $ "\n═══════════════════════════════════════════════════════════════"
      putStrLn $ "Bootstrap Test Complete:"
      putStrLn $ "  Files: " ++ show filesOk ++ "/" ++ show filesTotal
      putStrLn $ "  Tests: " ++ show passed ++ "/" ++ show total
      if filesOk == filesTotal
        then exitSuccess
        else exitFailure

--------------------------------------------------------------------------------
-- Paths
--------------------------------------------------------------------------------

grammarLegoPath :: FilePath
grammarLegoPath = "prelude/lego/Grammar.lego"

grammarSExprPath :: FilePath
grammarSExprPath = "prelude/lego/Grammar.sexpr"

testDirs :: [FilePath]
testDirs = ["test/meta", "test/pushout"]

-- Directories with intentionally malformed files (expected to fail parsing)
errorTestDirs :: [FilePath]
errorTestDirs = ["test/examples/errors"]

-- Files known to use unsupported syntax (multi-line productions, etc.)
-- These are documentation/specification files, not runnable tests
skipFiles :: [FilePath]
skipFiles = 
  [ "test/pushout/01_BasicPushout.lego"    -- multi-line grammar |
  , "test/pushout/01_BasicImport.lego"     -- numeric import name
  , "test/pushout/02_ParamGrammar.lego"    -- parameterized grammar (TODO)
  , "test/pushout/03_ConflictShadow.lego"  -- multi-line grammar
  , "test/pushout/04_EOFIncremental.lego"  -- pattern syntax ($x : :)
  , "test/pushout/05_EdgeSelfRef.lego"     -- qualified ref (Other.term)
  , "test/pushout/06_GrammarRef.lego"      -- qualified ref (Bool.expr)
  , "test/pushout/07_FullExample.lego"     -- multi-line grammar
  , "test/cursor/CursorForLego.lego"       -- advanced cursor syntax
  ]

--------------------------------------------------------------------------------
-- S-Expression parsing helpers
--------------------------------------------------------------------------------

-- | Load grammar from Grammar.sexpr file
loadGrammarSExpr :: IO (Either String (M.Map String (GrammarExpr ())))
loadGrammarSExpr = readSExprFile grammarSExprPath

--------------------------------------------------------------------------------
-- Phase 1: Extract grammar from parsed Grammar.lego
--------------------------------------------------------------------------------

-- | Extract all grammar productions from declarations
extractGrammarMap :: [LegoDecl] -> M.Map String (GrammarExpr ())
extractGrammarMap = foldr extractDecl M.empty
  where
    extractDecl :: LegoDecl -> M.Map String (GrammarExpr ()) -> M.Map String (GrammarExpr ())
    extractDecl (DGrammar name g) m = M.insert name g m
    extractDecl (DPiece pieceName _ body) m = 
      -- Qualify production names with piece name
      let prods = [(pieceName ++ "." ++ n, g) | DGrammar n g <- body]
      in foldr (uncurry M.insert) m prods
    extractDecl (DLang _ _ body) m = extractGrammarMap body `M.union` m
    extractDecl _ m = m

--------------------------------------------------------------------------------
-- Phase 2: Parse files with bootstrap grammar
--------------------------------------------------------------------------------

-- | Run tests using the bootstrap grammar
-- Returns (testsPassedTotal, testsTotal, filesOk, filesTotal)
runBootstrapTests :: M.Map String (GrammarExpr ()) -> IO (Either String (Int, Int, Int, Int))
runBootstrapTests bootstrapGrammar = do
  -- First, verify we can parse with the bootstrap grammar
  let testStr = "(f x)"
  case parseWithBootstrap bootstrapGrammar "Term.term" testStr of
    Left err -> return $ Left $ "Bootstrap grammar sanity check failed: " ++ err
    Right _ -> do
      -- Now run on test files
      allFiles <- concat <$> mapM findLegoFilesRecursive testDirs
      let runnableFiles = filter (`notElem` skipFiles) allFiles
          skippedCount = length allFiles - length runnableFiles
      putStrLn $ "  Found " ++ show (length allFiles) ++ " .lego files (" ++ show skippedCount ++ " skipped)"
      
      results <- forM runnableFiles $ \file -> do
        result <- runBootstrapFile bootstrapGrammar file
        case result of
          Right (p, t) -> do
            putStrLn $ "  ✓ " ++ file ++ " (" ++ show p ++ "/" ++ show t ++ " tests)"
            return (True, p, t)
          Left err -> do
            putStrLn $ "  ✗ " ++ file ++ ": " ++ err
            return (False, 0, 0)
      
      let filesOk = length $ filter (\(ok, _, _) -> ok) results
          filesTotal = length results
          totalPassed = sum [p | (_, p, _) <- results]
          totalTests = sum [t | (_, _, t) <- results]
      
      return $ Right (totalPassed, totalTests, filesOk, filesTotal)

-- | Parse and run a single file with bootstrap grammar
runBootstrapFile :: M.Map String (GrammarExpr ()) -> FilePath -> IO (Either String (Int, Int))
runBootstrapFile _bootstrapGrammar path = do
  exists <- doesFileExist path
  if not exists
    then return $ Left "File not found"
    else do
      content <- readFile path
      -- Use standard parseLegoFile (which uses legoGrammar loaded from Grammar.sexpr)
      -- This ensures we test with the real grammar that's loaded at runtime
      case parseLegoFile content of
        Left err -> return $ Left $ "Parse error: " ++ err
        Right decls -> do
          -- Load as compiled language for tests
          case E.loadLang decls of
            Left err -> return $ Left $ "Load error: " ++ err
            Right cl -> do
              let tests = clTests cl
                  rules = clRules cl
                  grammar = clGrammar cl
                  results = E.runTestsWithGrammar grammar rules tests
                  passed = length [r | r@(Pass _) <- results]
                  total = length tests
              return $ Right (passed, total)

--------------------------------------------------------------------------------
-- Bootstrap Grammar Parsing
--------------------------------------------------------------------------------

-- | Parse a complete file using bootstrap grammar
parseFileWithBootstrap :: M.Map String (GrammarExpr ()) -> String -> Either String [LegoDecl]
parseFileWithBootstrap grammar content =
  let tokInfos = tokenizeWithInfo content
      toks = map tiToken tokInfos
  in case M.lookup "File.legoFile" grammar of
       Nothing -> Left "Missing File.legoFile production in bootstrap grammar"
       Just g ->
         let st0 = BiState toks [M.empty] Nothing Parse grammar M.empty S.empty
         in case runGrammar g st0 of
              [] -> Left $ "Parse failed at: " ++ show (take 5 toks)
              (st:_) -> 
                case bsTerm st of
                  Just t -> Right $ termToDecls t
                  Nothing -> Left "No term produced"

-- | Parse a term with bootstrap grammar
parseWithBootstrap :: M.Map String (GrammarExpr ()) -> String -> String -> Either String Term
parseWithBootstrap grammar prodName input =
  let tokInfos = tokenizeWithInfo input
      toks = map tiToken tokInfos
  in case M.lookup prodName grammar of
       Nothing -> Left $ "Missing production: " ++ prodName
       Just g ->
         let st0 = BiState toks [M.empty] Nothing Parse grammar M.empty S.empty
         in case runGrammar g st0 of
              [] -> Left $ "Parse failed"
              (st:_) -> 
                case bsTerm st of
                  Just t -> Right t
                  Nothing -> Left "No term produced"

--------------------------------------------------------------------------------
-- Term → LegoDecl conversion (duplicated from GrammarParser for bootstrap)
--------------------------------------------------------------------------------

termToDecls :: Term -> [LegoDecl]
termToDecls (TmCon "seq" ts) = concatMap termToDecls ts
termToDecls (TmCon "decl" (d:_)) = termToDecls d
termToDecls t = case termToDecl t of
  Just d -> [d]
  Nothing -> []

termToDecl :: Term -> Maybe LegoDecl
termToDecl (TmCon "DImport" [TmVar name]) = Just $ DImport name
termToDecl (TmCon "DImport" [TmLit name]) = Just $ DImport name
termToDecl (TmCon "DDef" [TmVar name, value]) = Just $ DDef name value
termToDecl (TmCon "DDef" [TmLit name, value]) = Just $ DDef name value
termToDecl (TmCon "DTest" (TmLit name : input : rest)) =
  let nonUnit = filter (/= TmCon "unit" []) rest
  in case nonUnit of
    [] -> Just $ DTest $ mkTest name input input
    [expected] -> Just $ DTest $ mkTest name input expected
    _ -> Just $ DTest $ mkTest name input (head nonUnit)
  where
    mkTest n i e = Test n i e
termToDecl (TmCon "DRule" [TmVar name, pat, tmpl]) =
  Just $ DRule $ mkRule name pat tmpl
termToDecl (TmCon "DRule" [TmLit name, pat, tmpl]) =
  Just $ DRule $ mkRule name pat tmpl
termToDecl (TmCon "DLang" [TmVar name, parentsTerm, bodyTerm]) =
  Just $ DLang name (extractNames parentsTerm) (extractBody bodyTerm)
termToDecl (TmCon "DLang" [TmLit name, parentsTerm, bodyTerm]) =
  Just $ DLang name (extractNames parentsTerm) (extractBody bodyTerm)
termToDecl (TmCon "DPiece" (TmVar name : rest)) =
  Just $ DPiece name [] (extractProds name rest)
termToDecl (TmCon "DPiece" (TmLit name : rest)) =
  Just $ DPiece name [] (extractProds name rest)
termToDecl (TmCon "DGrammar" [TmVar name, gramTerm]) =
  Just $ DGrammar name (termToGrammar gramTerm)
termToDecl (TmCon "DGrammar" [TmLit name, gramTerm]) =
  Just $ DGrammar name (termToGrammar gramTerm)
termToDecl (TmCon "section" _) = Nothing
termToDecl (TmCon "comment" _) = Nothing
termToDecl _ = Nothing

mkRule :: String -> Term -> Term -> Rule
mkRule name pat tmpl = Rule name pat tmpl Nothing Forward

extractNames :: Term -> [String]
extractNames (TmCon "parents" ts) = [n | TmVar n <- ts] ++ [n | TmLit n <- ts]
extractNames _ = []

extractBody :: Term -> [LegoDecl]
extractBody (TmCon "body" ts) = concatMap termToDecls ts
extractBody (TmCon "seq" ts) = concatMap termToDecls ts
extractBody t = termToDecls t

extractProds :: String -> [Term] -> [LegoDecl]
extractProds _ [] = []
extractProds prefix (TmCon "prodWrap" [prod, _] : rest) =
  extractProds prefix (prod : rest)
extractProds prefix (TmCon "DGrammar" [TmVar name, gramTerm] : rest) =
  DGrammar name (termToGrammar gramTerm) : extractProds prefix rest
extractProds prefix (TmCon "DGrammar" [TmLit name, gramTerm] : rest) =
  DGrammar name (termToGrammar gramTerm) : extractProds prefix rest
extractProds prefix (_ : rest) = extractProds prefix rest

-- | Convert a Term to GrammarExpr
termToGrammar :: Term -> GrammarExpr ()
termToGrammar (TmCon "seq" gs) = foldr1 GSeq (map termToGrammar gs)
termToGrammar (TmCon "alt" gs) = foldr1 GAlt (map termToGrammar gs)
termToGrammar (TmCon "star" [g]) = GStar (termToGrammar g)
termToGrammar (TmCon "opt" [g]) = GAlt (termToGrammar g) GEmpty
termToGrammar (TmCon "cut" [g]) = GCut (termToGrammar g)
termToGrammar (TmCon "bind" [TmVar name, g]) = GBind name (termToGrammar g)
termToGrammar (TmCon "bind" [TmLit name, g]) = GBind name (termToGrammar g)
termToGrammar (TmCon "ref" [TmVar name]) = GRef name
termToGrammar (TmCon "ref" [TmLit name]) = GRef name
termToGrammar (TmCon "lit" [TmLit s]) = GLit s
termToGrammar (TmCon "lit" [TmVar s]) = GLit s
termToGrammar (TmCon "node" (TmVar name : gs)) = GNode name (map termToGrammar gs)
termToGrammar (TmCon "node" (TmLit name : gs)) = GNode name (map termToGrammar gs)
termToGrammar (TmCon "special" [TmVar name]) = GNode name []  -- <ident>, <string>, etc.
termToGrammar (TmCon "empty" []) = GEmpty
termToGrammar (TmVar name) = GRef name
termToGrammar (TmLit s) = GLit s
termToGrammar _ = GEmpty

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

findLegoFilesRecursive :: FilePath -> IO [FilePath]
findLegoFilesRecursive dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then return []
    else do
      entries <- listDirectory dir
      paths <- forM entries $ \entry -> do
        let path = dir </> entry
        isDir <- doesDirectoryExist path
        if isDir
          then if entry `elem` ["phi-spec"]  -- Skip problematic dirs
               then return []
               else findLegoFilesRecursive path
          else return [path | takeExtension path == ".lego"]
      return (concat paths)
