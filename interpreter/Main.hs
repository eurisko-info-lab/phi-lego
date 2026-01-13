{-# LANGUAGE LambdaCase #-}
-- | Main: Lego interpreter test runner
-- Runs tests on .lego files
module Main where

import Lego
import qualified Lego.Eval as E
import System.Environment (getArgs)
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), takeExtension)
import Control.Monad (forM, forM_)

main :: IO ()
main = getArgs >>= \case
  []           -> runAllTests
  [file]       -> runFile file
  _            -> putStrLn "Usage: lego-test [<file>]"

-- | Run all tests
runAllTests :: IO ()
runAllTests = do
  putStrLn "═══════════════════════════════════════════════════════════════"
  putStrLn "Running Lego Language Tests"
  putStrLn "═══════════════════════════════════════════════════════════════"
  runLegoTests

-- | Run tests on .lego files
runLegoTests :: IO ()
runLegoTests = do
  -- Test files from examples and its subdirectories
  let legoDir = "examples"
  exists <- doesDirectoryExist legoDir
  if exists then do
    legoFiles <- findLegoFilesRecursive legoDir
    
    putStrLn $ "Found " ++ show (length legoFiles) ++ " .lego files in " ++ legoDir
    
    -- Accumulate totals and error count
    results <- forM legoFiles $ \file -> do
      putStrLn $ "  Testing: " ++ file
      result <- runLegoFile file
      case result of
        Right (stats, counts) -> do
          putStrLn $ "    " ++ stats
          return (counts, False)  -- (passed, total, rules, grammars), hadError
        Left err -> do
          putStrLn $ "    ERROR: " ++ err
          return ((0, 0, 0, 0), True)  -- (passed, total, rules, grammars), hadError
    
    -- Print totals
    let (totals, errors) = unzip results
        (totalPassed, totalTests, totalRules, totalGrammars) = 
          foldl (\(p1,t1,r1,g1) (p2,t2,r2,g2) -> (p1+p2,t1+t2,r1+r2,g1+g2)) (0,0,0,0) totals
        errorCount = length (filter id errors)
        totalFiles = length legoFiles
        successFiles = totalFiles - errorCount
    putStrLn "───────────────────────────────────────────────────────────────"
    putStrLn $ "Total: " ++ show totalPassed ++ "/" ++ show totalTests ++ " tests, "
            ++ show totalRules ++ " rules, " ++ show totalGrammars ++ " grammars"
            ++ " (" ++ show successFiles ++ "/" ++ show totalFiles ++ " files"
            ++ (if errorCount > 0 then ", " ++ show errorCount ++ " errors)" else ")")
  else
    putStrLn $ "Directory not found: " ++ legoDir

-- | Recursively find all .lego files in a directory
findLegoFilesRecursive :: FilePath -> IO [FilePath]
findLegoFilesRecursive dir = do
  entries <- listDirectory dir
  paths <- forM entries $ \entry -> do
    let path = dir </> entry
    isDir <- doesDirectoryExist path
    if isDir
      then if entry `elem` ["phi-spec"]  -- Skip phi-spec as it has unresolvable imports
           then return []
           else findLegoFilesRecursive path
      else return [path | takeExtension path == ".lego"]
  return (concat paths)

-- | Run tests embedded in a .lego file
-- Returns (formatted stats, (passed, total, rules, grammars))
runLegoFile :: FilePath -> IO (Either String (String, (Int, Int, Int, Int)))
runLegoFile path = do
  exists <- doesFileExist path
  if not exists
    then return $ Left "File not found"
    else do
      -- Load with import resolution
      result <- E.loadLangWithImports path
      case result of
        Left err -> return $ Left err
        Right cl -> do
          let tests = E.clTests cl
          let rules = E.clRules cl
          let grammar = E.clGrammar cl
          let results = E.runTestsWithGrammar grammar rules tests
          let (passed, failed) = partitionResults results
          -- Print failures
          forM_ failed $ \res -> case res of
            Fail name expected actual -> do
              putStrLn $ "    FAIL: " ++ name
              putStrLn $ "      Expected: " ++ show expected
              putStrLn $ "      Actual:   " ++ show actual
            Pass _ -> return ()  -- shouldn't happen since filtered
          let grammarCount = length (E.clGrammar cl)
          let ruleCount = length rules
          let passedCount = length passed
          let totalCount = length tests
          let stats = show passedCount ++ "/" ++ show totalCount ++ " tests, " 
                   ++ show ruleCount ++ " rules, " 
                   ++ show grammarCount ++ " grammars"
          return $ Right (stats, (passedCount, totalCount, ruleCount, grammarCount))

-- | Run a single file
runFile :: FilePath -> IO ()
runFile path = case takeExtension path of
  ".lego" -> do
    result <- runLegoFile path
    case result of
      Right (msg, _) -> putStrLn $ "OK: " ++ msg
      Left err       -> putStrLn $ "ERROR: " ++ err
  ext -> putStrLn $ "Unknown extension: " ++ ext

-- Helpers
partitionResults :: [TestResult] -> ([TestResult], [TestResult])
partitionResults = foldr f ([], [])
  where
    f r@(Pass _) (ps, fs) = (r:ps, fs)
    f r@(Fail _ _ _) (ps, fs) = (ps, r:fs)
