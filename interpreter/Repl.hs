{-# LANGUAGE LambdaCase #-}
-- | Lego REPL: Interactive Read-Eval-Print Loop for Lego languages
module Main where

import Lego
import Lego.GrammarInterp (parseTerm)
import qualified Lego.Eval as E
import System.IO (hFlush, stdout, hSetBuffering, BufferMode(..), stdin)
import System.Environment (getArgs)
import Control.Monad (when, unless, forM_)
import Data.List (isPrefixOf, intercalate)
import qualified Data.Map as M
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- REPL State
--------------------------------------------------------------------------------

data ReplState = ReplState
  { rsLang    :: Maybe E.CompiledLang  -- Currently loaded language
  , rsHistory :: [String]              -- Command history
  , rsVars    :: M.Map String Term     -- REPL variables
  , rsVerbose :: Bool                  -- Verbose mode
  } deriving (Show)

emptyState :: ReplState
emptyState = ReplState Nothing [] M.empty False

--------------------------------------------------------------------------------
-- Main Entry Point
--------------------------------------------------------------------------------

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stdin LineBuffering
  args <- getArgs
  case args of
    []     -> startRepl emptyState
    [file] -> do
      st <- loadFile emptyState file
      startRepl st
    _      -> putStrLn "Usage: lego-repl [file.lego]"

--------------------------------------------------------------------------------
-- REPL Loop
--------------------------------------------------------------------------------

startRepl :: ReplState -> IO ()
startRepl st = do
  putStrLn "╔═══════════════════════════════════════════════════════════════╗"
  putStrLn "║  Lego REPL - Interactive Language Workbench                   ║"
  putStrLn "║  Type :help for commands, :quit to exit                       ║"
  putStrLn "╚═══════════════════════════════════════════════════════════════╝"
  case rsLang st of
    Just lang -> putStrLn $ "Loaded: " ++ E.clName lang
    Nothing   -> putStrLn "No language loaded. Use :load <file.lego>"
  putStrLn ""
  repl st

repl :: ReplState -> IO ()
repl st = do
  prompt st
  line <- getLine
  case line of
    "" -> repl st
    _  -> do
      (continue, st') <- processLine st line
      when continue $ repl st'

prompt :: ReplState -> IO ()
prompt st = do
  let name = maybe "lego" E.clName (rsLang st)
  putStr $ name ++ "> "
  hFlush stdout

--------------------------------------------------------------------------------
-- Command Processing
--------------------------------------------------------------------------------

processLine :: ReplState -> String -> IO (Bool, ReplState)
processLine st line
  | ":quit" `isPrefixOf` line = return (False, st)
  | ":q" `isPrefixOf` line    = return (False, st)
  | ":help" `isPrefixOf` line = printHelp >> return (True, st)
  | ":h" `isPrefixOf` line    = printHelp >> return (True, st)
  | ":load " `isPrefixOf` line = do
      st' <- loadFile st (drop 6 line)
      return (True, st')
  | ":l " `isPrefixOf` line = do
      st' <- loadFile st (drop 3 line)
      return (True, st')
  | ":reload" `isPrefixOf` line = do
      st' <- reloadFile st
      return (True, st')
  | ":r" `isPrefixOf` line && not (":rules" `isPrefixOf` line) = do
      st' <- reloadFile st
      return (True, st')
  | ":info" `isPrefixOf` line = printInfo st >> return (True, st)
  | ":i" `isPrefixOf` line && not (":import" `isPrefixOf` line) = printInfo st >> return (True, st)
  | ":grammar" `isPrefixOf` line = printGrammar st >> return (True, st)
  | ":g" `isPrefixOf` line = printGrammar st >> return (True, st)
  | ":rules" `isPrefixOf` line = printRules st >> return (True, st)
  | ":tests" `isPrefixOf` line = runReplTests st >> return (True, st)
  | ":t" `isPrefixOf` line = runReplTests st >> return (True, st)
  | ":parse " `isPrefixOf` line = do
      parseLine st (drop 7 line)
      return (True, st)
  | ":p " `isPrefixOf` line = do
      parseLine st (drop 3 line)
      return (True, st)
  | ":eval " `isPrefixOf` line = do
      evalLine st (drop 6 line)
      return (True, st)
  | ":e " `isPrefixOf` line = do
      evalLine st (drop 3 line)
      return (True, st)
  | ":let " `isPrefixOf` line = do
      st' <- letBinding st (drop 5 line)
      return (True, st')
  | ":vars" `isPrefixOf` line = printVars st >> return (True, st)
  | ":v" `isPrefixOf` line = printVars st >> return (True, st)
  | ":verbose" `isPrefixOf` line = do
      let st' = st { rsVerbose = not (rsVerbose st) }
      putStrLn $ "Verbose mode: " ++ if rsVerbose st' then "on" else "off"
      return (True, st')
  | ":" `isPrefixOf` line = do
      putStrLn $ "Unknown command: " ++ line
      putStrLn "Type :help for available commands"
      return (True, st)
  | otherwise = do
      -- Default: parse and evaluate
      evalExpr st line
      return (True, st { rsHistory = line : rsHistory st })

--------------------------------------------------------------------------------
-- Commands Implementation
--------------------------------------------------------------------------------

printHelp :: IO ()
printHelp = putStrLn $ unlines
  [ "Commands:"
  , "  :load <file>    Load a .lego or .phi file"
  , "  :reload         Reload the current file"
  , "  :info           Show loaded language info"
  , "  :grammar        Show grammar productions"
  , "  :rules          Show rewrite rules"
  , "  :tests          Run embedded tests"
  , "  :parse <expr>   Parse expression (show AST)"
  , "  :eval <expr>    Evaluate expression"
  , "  :let x = <expr> Bind variable"
  , "  :vars           Show bound variables"
  , "  :verbose        Toggle verbose mode"
  , "  :help           Show this help"
  , "  :quit           Exit REPL"
  , ""
  , "Without a command prefix, input is parsed and evaluated."
  , ""
  , "Examples:"
  , "  :load lego/phi/Phi.lego"
  , "  :parse (app (lam x (var x)) (var y))"
  , "  (plus 1 2)"
  ]

loadFile :: ReplState -> String -> IO ReplState
loadFile st path = do
  let path' = trim path
  putStrLn $ "Loading: " ++ path'
  result <- E.loadLangWithImports path'
  case result of
    Left err -> do
      putStrLn $ "Error: " ++ err
      return st
    Right lang -> do
      putStrLn $ "Loaded: " ++ E.clName lang
      putStrLn $ "  " ++ show (M.size (E.clGrammar lang)) ++ " grammar productions"
      putStrLn $ "  " ++ show (length (E.clRules lang)) ++ " rules"
      putStrLn $ "  " ++ show (length (E.clTests lang)) ++ " tests"
      return st { rsLang = Just lang }

reloadFile :: ReplState -> IO ReplState
reloadFile st = case rsLang st of
  Nothing -> do
    putStrLn "No file loaded"
    return st
  Just lang -> loadFile st (E.clName lang ++ ".lego")  -- Attempt reload

printInfo :: ReplState -> IO ()
printInfo st = case rsLang st of
  Nothing -> putStrLn "No language loaded"
  Just lang -> do
    putStrLn $ "Language: " ++ E.clName lang
    putStrLn $ "Vocabulary: " ++ show (S.size (E.clVocab lang)) ++ " tokens"
    putStrLn $ "Grammar: " ++ show (M.size (E.clGrammar lang)) ++ " productions"
    putStrLn $ "Rules: " ++ show (length (E.clRules lang))
    putStrLn $ "Tests: " ++ show (length (E.clTests lang))
    unless (null (E.clImports lang)) $
      putStrLn $ "Imports: " ++ intercalate ", " (E.clImports lang)

printGrammar :: ReplState -> IO ()
printGrammar st = case rsLang st of
  Nothing -> putStrLn "No language loaded"
  Just lang -> do
    putStrLn "Grammar productions:"
    forM_ (M.toList (E.clGrammar lang)) $ \(name, g) ->
      putStrLn $ "  " ++ name ++ " ::= " ++ showGrammar g

showGrammar :: GrammarExpr a -> String
showGrammar GEmpty = "ε"
showGrammar (GLit s) = "\"" ++ s ++ "\""
showGrammar (GSyntax s) = "'" ++ s ++ "'"  -- Syntax uses single quotes
showGrammar (GKeyword s) = "`" ++ s ++ "`"  -- Reserved keywords use backticks
showGrammar (GRegex s) = "/" ++ s ++ "/"  -- Regex patterns
showGrammar (GChar s) = "'" ++ s ++ "'"  -- Char classes
showGrammar (GNode c gs) = "⟨" ++ c ++ concatMap ((' ':) . showGrammar) gs ++ "⟩"
showGrammar (GSeq g1 g2) = showGrammar g1 ++ " " ++ showGrammar g2
showGrammar (GAlt g1 g2) = "(" ++ showGrammar g1 ++ " | " ++ showGrammar g2 ++ ")"
showGrammar (GStar g) = "(" ++ showGrammar g ++ ")*"  -- Fixed: wrap in parens like Show instance
showGrammar (GRef r) = r
showGrammar (GBind x g) = x ++ ":" ++ showGrammar g
showGrammar (GVar x) = "$" ++ x
showGrammar GAny = "_"
showGrammar (GRec x g) = "μ" ++ x ++ "." ++ showGrammar g

printRules :: ReplState -> IO ()
printRules st = case rsLang st of
  Nothing -> putStrLn "No language loaded"
  Just lang -> do
    putStrLn "Rewrite rules:"
    forM_ (E.clRules lang) $ \rule ->
      putStrLn $ "  " ++ showRule rule

showRule :: Rule -> String
showRule (Rule _name pat templ guard dir) = 
  showPattern pat ++ " " ++ showDir dir ++ " " ++ showTemplate templ ++
  maybe "" ((" when " ++) . showGuard) guard
  where
    showGuard g = show g
    showDir Forward = "~>"
    showDir Backward = "<~"
    showDir Both = "<~>"

-- Pattern and Template are now unified with Term
-- Pattern variables have $ prefix
showPattern :: Term -> String
showPattern (TmVar ('$':x)) = "$" ++ x
showPattern (TmVar x) = x
showPattern (TmCon c ps) = "(" ++ c ++ concatMap ((' ':) . showPattern) ps ++ ")"
showPattern (TmLit l) = show l
showPattern t = show t

-- Template uses Term with $ for variables, (subst $x e body) for let-binding
showTemplate :: Term -> String
showTemplate (TmVar ('$':x)) = "$" ++ x
showTemplate (TmVar x) = x
showTemplate (TmCon "subst" [TmVar ('$':x), e, body]) = 
  "[" ++ x ++ " := " ++ showTemplate e ++ "] " ++ showTemplate body
showTemplate (TmCon c ts) = "(" ++ c ++ concatMap ((' ':) . showTemplate) ts ++ ")"
showTemplate (TmLit l) = show l
showTemplate t = show t

runReplTests :: ReplState -> IO ()
runReplTests st = case rsLang st of
  Nothing -> putStrLn "No language loaded"
  Just lang -> do
    let tests = E.clTests lang
        rules = E.clRules lang
        results = Lego.runTests rules tests
        (passed, failed) = partition results
    putStrLn $ show (length passed) ++ "/" ++ show (length tests) ++ " tests passed"
    forM_ failed $ \result -> case result of
      Fail name expected actual -> do
        putStrLn $ "  FAIL: " ++ name
        putStrLn $ "    Expected: " ++ show expected
        putStrLn $ "    Actual:   " ++ show actual
      Pass _ -> return ()  -- shouldn't happen in failed list
  where
    partition = foldr go ([], [])
    go r@(Pass _) (ps, fs) = (r:ps, fs)
    go r@(Fail _ _ _) (ps, fs) = (ps, r:fs)

parseLine :: ReplState -> String -> IO ()
parseLine st input = case rsLang st of
  Nothing -> do
    -- Parse as S-expression
    case parseTerm (trim input) of
      Left err -> putStrLn $ "Parse error: " ++ err
      Right term -> putStrLn $ "AST: " ++ show term
  Just lang -> do
    -- Parse using language grammar
    case E.parse lang (trim input) of
      Left err -> putStrLn $ "Parse error: " ++ err
      Right term -> putStrLn $ "AST: " ++ show term

evalLine :: ReplState -> String -> IO ()
evalLine st input = evalExpr st (trim input)

evalExpr :: ReplState -> String -> IO ()
evalExpr st input = do
  -- First parse
  let parseResult = case rsLang st of
        Nothing -> parseTerm input
        Just lang -> E.parse lang input
  case parseResult of
    Left err -> putStrLn $ "Parse error: " ++ err
    Right term -> do
      -- Substitute REPL variables
      let term' = substVars (rsVars st) term
      -- Evaluate
      let rules = maybe [] E.clRules (rsLang st)
      let result = normalize rules term'
      -- Show result
      when (rsVerbose st) $ do
        putStrLn $ "Parsed: " ++ show term
        putStrLn $ "After subst: " ++ show term'
      putStrLn $ show result

substVars :: M.Map String Term -> Term -> Term
substVars vars (TmVar x) = M.findWithDefault (TmVar x) x vars
substVars vars (TmCon c args) = TmCon c (map (substVars vars) args)
substVars _ t = t

letBinding :: ReplState -> String -> IO ReplState
letBinding st input = case break (== '=') input of
  (name, '=':rest) -> do
    let name' = trim name
    case parseTerm (trim rest) of
      Left err -> do
        putStrLn $ "Parse error: " ++ err
        return st
      Right term -> do
        let term' = case rsLang st of
              Nothing -> term
              Just lang -> normalize (E.clRules lang) term
        putStrLn $ name' ++ " = " ++ show term'
        return st { rsVars = M.insert name' term' (rsVars st) }
  _ -> do
    putStrLn "Syntax: :let name = expr"
    return st

printVars :: ReplState -> IO ()
printVars st = do
  putStrLn "Variables:"
  forM_ (M.toList (rsVars st)) $ \(name, term) ->
    putStrLn $ "  " ++ name ++ " = " ++ show term

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

trim :: String -> String
trim = dropWhile (== ' ') . reverse . dropWhile (== ' ') . reverse
