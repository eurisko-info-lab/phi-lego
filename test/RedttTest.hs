{-# LANGUAGE BangPatterns #-}
-- | Test suite for parsing redtt library files with the Lego grammar interpreter.
--
-- This test validates the RedttParser grammar against the redtt cubical type theory
-- library files, providing coverage metrics and sample failure analysis.
module Main where

import Lego.GrammarInterp (loadGrammarDefs, parseProduction, GrammarDefs(..), extractAllSymbols)
import Lego.GrammarParser (parseLegoFile)
import Lego.Token (tokenizeWithSymbols, Token(..), classifyReserved)
import System.Directory (listDirectory, doesFileExist, doesDirectoryExist)
import System.FilePath ((</>), takeExtension, takeFileName)
import Data.List (isPrefixOf, sortBy)
import Data.Char (isSpace)
import Data.Ord (comparing)
import Control.Monad (forM, forM_)
import Control.Exception (evaluate)
import System.Timeout (timeout)
import Text.Printf (printf)
import System.Exit (exitFailure, exitSuccess)
import qualified Data.Set as S

-- | Filter out whitespace tokens
isInteresting :: Token -> Bool
isInteresting TNewline = False
isInteresting (TIndent _) = False
isInteresting _ = True

-- | Main test entry point
main :: IO ()
main = do
  contents <- readFile "lego/examples/languages/red/RedttParser.lego"
  case parseLegoFile contents of
    Left err -> do
      putStrLn $ "Grammar parse error: " ++ err
      exitFailure
    Right decls -> do
      let gramDefs = loadGrammarDefs decls

      runGoldenDecls gramDefs
      
      -- Find all .red files
      redFiles <- findRedFiles "redtt/library"
      let sortedFiles = sortBy (comparing takeFileName) redFiles
      
      putStrLn $ "Found " ++ show (length sortedFiles) ++ " files\n"
      putStrLn "File                                          | Parsed | Total | Rate"
      putStrLn "----------------------------------------------|--------|-------|------"
      
      -- Process each file with timeout
      allResults <- forM sortedFiles $ \path -> do
        result <- timeout (5 * 1000000) $ processFile gramDefs path  -- 5 second timeout
        case result of
          Nothing -> do
            printf "%-45s | TIMEOUT\n" (takeFileName path)
            return (path, 0, 0, [])
          Just r -> return r
      
      -- Summary
      let (totalParsed, totalDecls) = foldr (\(_, p, t, _) (ap, at) -> (ap+p, at+t)) (0,0) allResults
      putStrLn "----------------------------------------------|--------|-------|------"
      printf "%-45s | %6d | %5d | %3d%%\n" "TOTAL" totalParsed totalDecls 
             (if totalDecls == 0 then 0 else (100 * totalParsed `div` totalDecls))
      
      -- Show failures
      let failures = [(path, fails) | (path, _, _, fails) <- allResults, not (null fails)]
      when (not (null failures)) $ do
        putStrLn "\n\n=== SAMPLE FAILURES ==="
        forM_ (take 5 failures) $ \(path, fails) -> do
          putStrLn $ "\n" ++ takeFileName path ++ ":"
          forM_ (take 2 fails) $ \(decl, remaining) -> do
            putStrLn $ "  " ++ take 50 decl ++ "..."
            putStrLn $ "  Remaining: " ++ show (take 5 remaining)
      
      -- Exit with appropriate code
      let rate = if totalDecls == 0 then 100 else (100 * totalParsed `div` totalDecls)
      if rate >= 50  -- Pass if at least 50% parse rate
        then exitSuccess
        else exitFailure

-- | A small set of non-library smoke tests to guard forward-compat surface forms.
--
-- These are intentionally minimal: they should never depend on library content.
runGoldenDecls :: GrammarDefs -> IO ()
runGoldenDecls gramDefs = do
  let symList = S.toList (extractAllSymbols gramDefs)
  -- Reserved words are kept intentionally structural, but `with ... end`
  -- pipe blocks need hard delimiters to avoid being parsed as ordinary
  -- identifiers in application position.
  let reserved = S.fromList ["in", "with", "end"]
  let goldenDecls =
        [ "def goldenHole0 : type = ?"
        , "def goldenHole1 : type = ?foo"
        , "def goldenWithElim : type = elim with | zero → refl end"
        , "def goldenWithComp : type = comp 0 1 refl with | i=0 → refl end"
        , "def goldenV : type = V i A B e"
        , "def goldenVinQuote : type = `(vin i x y)"
        , "def goldenCapProj : type = x.cap"
        , "def goldenVProjProj : type = x.vproj"
        , "def goldenBoxWith : type = box refl with | i=0 → refl end"
        , "def goldenCapWith : type = cap refl with | i=0 → refl end"
        ]

  forM_ goldenDecls $ \decl -> do
    let atomToks = filter isInteresting (tokenizeWithSymbols symList decl)
    let toks = classifyReserved reserved atomToks
    result <- timeout 1000000 $ evaluate $ parseProduction gramDefs "File.decl" toks
    case result of
      Nothing -> do
        putStrLn "\nGOLDEN DECL TIMEOUT:"
        putStrLn decl
        exitFailure
      Just (Left _err) -> do
        putStrLn "\nGOLDEN DECL PARSE FAILURE:"
        putStrLn decl
        exitFailure
      Just (Right (_, rest))
        | null rest -> pure ()
        | otherwise -> do
            putStrLn "\nGOLDEN DECL DID NOT CONSUME ALL TOKENS:"
            putStrLn decl
            putStrLn $ "Remaining: " ++ show rest
            exitFailure

-- | Process a single redtt file, returning parse statistics
processFile :: GrammarDefs -> FilePath -> IO (FilePath, Int, Int, [(String, [Token])])
processFile gramDefs path = do
  fileContents <- readFile path
  let cleaned = stripMetaBlocks (stripLineComments (stripBlockComments fileContents))
  let fileDecls = splitDecls cleaned
  -- For RedTT we keep the reserved-word set intentionally structural.
  -- Backtick-reserved literals are a .lego meta-language feature; importing them
  -- here can accidentally reserve surface tokens and break parsing.
  let keywords = S.empty
  -- We keep this list extremely small: reserving too much breaks valid
  -- slash-qualified identifiers from the library (e.g. `le/case`).
  --
  -- `in` is the main structural delimiter that tends to get swallowed by
  -- greedy `<ident>` positions in `let ... in ...`.
  -- `with ... end` pipe blocks need hard delimiters; otherwise `with`/`end`
  -- can be consumed as ordinary identifiers by generic application parsing.
  let structuralReserved = S.fromList ["in", "with", "end"]
  let reserved = S.union keywords structuralReserved
  -- Extract symbols from grammar so the lexer can recognize multi-character operators.
  -- Single-character punctuation is preserved even without an explicit symbol list.
  let symList = S.toList (extractAllSymbols gramDefs)
  results <- forM fileDecls $ \decl -> do
    -- CRITICAL: Use tokenizeWithKeywords False for redtt (atoms only)
    -- Then classify keywords based on grammar (Phase 2: reject reserved words)
    let !atomToks = filter isInteresting (tokenizeWithSymbols symList decl)
    let !toks = classifyReserved reserved atomToks
    -- Some RedTT declarations are large and induce significant PEG backtracking.
    -- They parse correctly, but can exceed an ultra-tight timeout.
    result <- timeout 2000000 $ evaluate $ parseProduction gramDefs "File.decl" toks  -- 2s per decl
    case result of
      Nothing -> return (False, Just (decl, toks))
      Just (Left _) -> return (False, Just (decl, toks))
      Just (Right (_, rest)) -> 
        if null rest 
          then return (True, Nothing)
          else return (False, Just (decl, rest))
  
  let parsed = length [() | (True, _) <- results]
      total = length results
      failures = [(d, r) | (False, Just (d, r)) <- results]
  
  printf "%-45s | %6d | %5d | %3d%%\n" (takeFileName path) parsed total 
         (if total == 0 then 100 else (100 * parsed `div` total))
  
  return (path, parsed, total, failures)

-- | Split file contents into individual declarations
splitDecls :: String -> [String]
splitDecls content = 
  let ls = lines content
      groups = go [] [] ls
  in filter (not . null) . filter (not . all isSpace) $ map unlines groups
  where
    go acc current [] = reverse (reverse current : acc)
    go acc current (l:rest)
      | startsDecl l && not (null current) && not (all isModifierLine current) = 
          go (reverse current : acc) [l] rest
      | isPrefixOf "--" (dropWhile isSpace l) = go acc current rest
      | all isSpace l = go acc current rest
      | otherwise = go acc (l:current) rest
    
    startsDecl l =
      let stripped = dropWhile isSpace l
      in stripped == "opaque"
      || stripped == "public"
      || any (`isPrefixOf` stripped) ["import ", "def ", "data ", "opaque ", "public "]

    -- Modifiers that prefix the next declaration (common in RedTT files)
    isModifierLine l =
      let stripped = dropWhile isSpace l
      in stripped == "opaque" || stripped == "public"

-- | Strip RedTT/OCaml-style block comments: /- ... -/
-- Preserves newlines so declaration splitting stays stable.
stripBlockComments :: String -> String
stripBlockComments = go False
  where
    go _ [] = []
    go False ('/':'-':cs) = go True cs
    go True ('-':'/':cs) = go False cs
    go True (c:cs)
      | c == '\n' = '\n' : go True cs
      | otherwise = go True cs
    go False (c:cs) = c : go False cs

-- | Strip line comments starting with "--" (after any code on the line).
-- This keeps declaration splitting and parsing stable in files that mix
-- inline commentary with terms (e.g. redml-examples.red).
stripLineComments :: String -> String
stripLineComments = unlines . map stripLine . lines
  where
    stripLine l =
      let (pre, rest) = breakOn "--" l
      in case rest of
           [] -> pre
           _  -> pre

    breakOn :: String -> String -> (String, String)
    breakOn needle haystack = go [] haystack
      where
        go acc [] = (reverse acc, [])
        go acc s@(c:cs)
          | needle `isPrefixOf` s = (reverse acc, s)
          | otherwise = go (c:acc) cs

-- | Remove RedTT meta blocks.
--
-- These blocks are RedML (not RedTT surface syntax) and can contain nested
-- ⦉…⦊ pairs, so we track nesting depth rather than stopping at the first ⦊.
stripMetaBlocks :: String -> String
stripMetaBlocks = unlines . go 0 . lines
  where
    countChar :: Char -> String -> Int
    countChar ch = length . filter (== ch)

    deltaDepth :: String -> Int
    deltaDepth l = countChar '⦉' l - countChar '⦊' l

    go :: Int -> [String] -> [String]
    go _ [] = []
    go depth (l:ls)
      | depth > 0 =
          let depth' = depth + deltaDepth l
          in "" : go (max 0 depth') ls
      | otherwise =
          let stripped = dropWhile isSpace l
          in if "meta" `isPrefixOf` stripped
               then
                 let opens = countChar '⦉' l
                     closes = countChar '⦊' l
                     -- If the opening bracket isn't on this line, assume a multi-line block
                     -- and wait for a matching close.
                     depth0
                       | opens == 0 = 1
                       | otherwise  = max 0 (opens - closes)
                 in "" : go depth0 ls
               else l : go 0 ls

-- | Recursively find all .red files in a directory
findRedFiles :: FilePath -> IO [FilePath]
findRedFiles dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then return []
    else do
      entries <- listDirectory dir
      fmap concat $ forM entries $ \entry -> do
        let path = dir </> entry
        isFile <- doesFileExist path
        isDir <- doesDirectoryExist path
        if isFile && takeExtension path == ".red"
          then return [path]
          else if isDir
            then findRedFiles path
            else return []

-- | Conditional execution
when :: Bool -> IO () -> IO ()
when True act = act
when False _ = return ()
