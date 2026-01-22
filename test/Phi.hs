{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
-- Phi: Term Rewriting CLI for CursorForLego
-- 
-- Full-featured term rewriting system with:
-- - Multiple proof assistant projections (cooltt, Agda, Lean4, Coq)
-- - REPL mode for interactive exploration
-- - DOT graph visualization
-- - JSON output for tooling
-- - Watch mode for auto-regeneration
-- - Import system
-- - Metrics and rule tracing

module Main where

import qualified Data.Map.Strict as Map
import Control.Monad (foldM, msum, when, forM_, forever, unless)
import Data.Maybe (fromMaybe, mapMaybe, catMaybes, isJust)
import Data.Char (isSpace, isDigit, isAlphaNum)
import Data.List (intercalate, isPrefixOf, sortBy, nub)
import Data.Ord (comparing)
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr, hFlush, stdout, hSetBuffering, BufferMode(..))
import System.Directory (doesFileExist, getModificationTime)
import Control.Exception (try, SomeException)
import Data.Time.Clock (UTCTime, getCurrentTime, diffUTCTime)
import Control.Concurrent (threadDelay)
import Text.Printf (printf)

--------------------------------------------------------------------------------
-- Term Data Type
--------------------------------------------------------------------------------

data Term = Var String       -- Object-level variable
          | MetaVar String   -- Pattern metavariable (for matching)
          | Str String       -- String literal
          | Num Int          -- Number
          | Node String [Term]
          deriving (Show, Eq, Ord)

type Env = Map.Map String (Either Term [Term])
type Rule = (String, Term, Term)

--------------------------------------------------------------------------------
-- Pattern Matching
--------------------------------------------------------------------------------

match :: Term -> Term -> Maybe Env
match (MetaVar v) t = Just (Map.singleton v (Left t))
match (Var v1) (Var v2) | v1 == v2 = Just Map.empty
match (Str s1) (Str s2) | s1 == s2 = Just Map.empty
match (Num n1) (Num n2) | n1 == n2 = Just Map.empty
match (Node l1 cs1) (Node l2 cs2) | l1 == l2 =
  let n = length cs1
      m = length cs2
  in if n == 0 
     then if m == 0 then Just Map.empty else Nothing 
     else if n > m 
          then Nothing
          else if n == m
               then foldM (\acc (p, t) -> union acc <$> match p t) Map.empty (zip cs1 cs2)
               else let prefix_len = n - 1
                        prefix_cs1 = take prefix_len cs1
                        prefix_cs2 = take prefix_len cs2
                        tail_cs2 = drop prefix_len cs2
                        last_p = last cs1
                        m_prefix = foldM (\acc (p, t) -> union acc <$> match p t) Map.empty (zip prefix_cs1 prefix_cs2)
                    in case last_p of
                         MetaVar v -> do
                           penv <- m_prefix
                           return (Map.insert v (Right tail_cs2) penv)
                         _ -> Nothing
match _ _ = Nothing

union :: Env -> Env -> Env
union = Map.union

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

substitute :: Env -> Term -> Term
substitute env (MetaVar v) = case Map.lookup v env of
  Just (Left t) -> substitute env t
  Just (Right _) -> error $ "List variable " ++ v ++ " used as scalar term"
  Nothing -> MetaVar v
substitute _ (Var v) = Var v
substitute _ (Str s) = Str s
substitute _ (Num n) = Num n
substitute env (Node l cs) = Node l (concatMap (subList env) cs)
  where
    subList env' (MetaVar v) = case Map.lookup v env' of
      Just (Left t) -> [substitute env' t]
      Just (Right ts) -> map (substitute env') ts
      Nothing -> [MetaVar v]
    subList env' other = [substitute env' other]

--------------------------------------------------------------------------------
-- Rewriting Engine with Metrics
--------------------------------------------------------------------------------

mv :: String -> Term
mv = MetaVar

data RewriteStep = RewriteStep
  { stepRule :: String
  , stepBefore :: Term
  , stepAfter :: Term
  } deriving (Show)

data RewriteResult = RewriteResult
  { resultTerm :: Term
  , resultSteps :: [RewriteStep]
  , resultFuelUsed :: Int
  , resultNormalized :: Bool
  } deriving (Show)

oneStep :: [Rule] -> Term -> Maybe (String, Term)
oneStep rs t = msum [(name,) <$> (substitute <$> match pattern t <*> pure template) 
                    | (name, pattern, template) <- rs]

-- Basic normalize
normalize :: [Rule] -> Term -> Term
normalize rs = resultTerm . normalizeWithMetrics rs

-- Normalize with full metrics
normalizeWithMetrics :: [Rule] -> Term -> RewriteResult
normalizeWithMetrics rs t0 = go 100 t0 []
  where
    go 0 t steps = RewriteResult t (reverse steps) 100 False
    go n t steps = case oneStep rs t of
      Nothing -> case t of
        Node l cs -> 
          let cs' = map (normalize rs) cs
              t' = Node l cs'
          in RewriteResult t' (reverse steps) (100 - n) True
        _ -> RewriteResult t (reverse steps) (100 - n) True
      Just (name, t') -> 
        let step = RewriteStep name t t'
        in go (n-1) t' (step:steps)

-- Verbose trace
normalizeVerbose :: [Rule] -> Term -> [(String, Term)]
normalizeVerbose rs = map (\s -> (stepRule s, stepAfter s)) . resultSteps . normalizeWithMetrics rs

--------------------------------------------------------------------------------
-- S-Expression Parser with Error Recovery
--------------------------------------------------------------------------------

data Token = TLParen | TRParen | TString String | TNum Int | TSym String
  deriving (Show, Eq)

data ParseError = ParseError
  { errorPos :: Int
  , errorMsg :: String
  } deriving (Show)

tokenize :: String -> [Token]
tokenize [] = []
tokenize ('(':xs) = TLParen : tokenize xs
tokenize (')':xs) = TRParen : tokenize xs
tokenize ('"':xs) = let (s, rest) = parseString xs in TString s : tokenize rest
tokenize (';':xs) = tokenize (dropWhile (/= '\n') xs)  -- Comments
tokenize (c:xs) | isSpace c = tokenize xs
tokenize ('-':c:xs) | isDigit c = 
  let (n, rest) = span isDigit (c:xs) in TNum (negate $ read n) : tokenize rest
tokenize (c:xs) | isDigit c = 
  let (n, rest) = span isDigit (c:xs) in TNum (read n) : tokenize rest
tokenize xs = let (s, rest) = span isSymChar xs in TSym s : tokenize rest
  where isSymChar c = isAlphaNum c || c `elem` "-_+*/<>=!?@#$%^&|~∧∨→λπΣ∀∃:.'"

parseString :: String -> (String, String)
parseString [] = ("", "")
parseString ('"':xs) = ("", xs)
parseString ('\\':'n':xs) = let (s, rest) = parseString xs in ('\n':s, rest)
parseString ('\\':'t':xs) = let (s, rest) = parseString xs in ('\t':s, rest)
parseString ('\\':c:xs) = let (s, rest) = parseString xs in (c:s, rest)
parseString (c:xs) = let (s, rest) = parseString xs in (c:s, rest)

parseTerm :: [Token] -> Maybe (Term, [Token])
parseTerm [] = Nothing
parseTerm (TLParen:TRParen:rest) = Just (Node "" [], rest)
parseTerm (TLParen:TSym name:rest) = do
  (args, rest') <- parseArgs rest
  pure (Node name args, rest')
parseTerm (TLParen:rest) = do
  (args, rest') <- parseArgs rest
  case args of
    (Var name:as) -> pure (Node name as, rest')
    _ -> Nothing
parseTerm (TString s:rest) = Just (Str s, rest)
parseTerm (TNum n:rest) = Just (Num n, rest)
parseTerm (TSym s:rest) = Just (Var s, rest)
parseTerm _ = Nothing

parseArgs :: [Token] -> Maybe ([Term], [Token])
parseArgs (TRParen:rest) = Just ([], rest)
parseArgs toks = do
  (t, rest) <- parseTerm toks
  (ts, rest') <- parseArgs rest
  pure (t:ts, rest')

-- Parse multiple terms (for multi-definition files)
parseMultiple :: [Token] -> [Term]
parseMultiple [] = []
parseMultiple toks = case parseTerm toks of
  Just (t, rest) -> t : parseMultiple rest
  Nothing -> []

parse :: String -> Either String Term
parse s = case parseTerm (tokenize s) of
  Just (t, []) -> Right t
  Just (_, toks) -> Left $ "Extra tokens: " ++ show (take 3 toks)
  Nothing -> Left "Parse error"

parseAll :: String -> Either String [Term]
parseAll s = 
  let terms = parseMultiple (tokenize s)
  in if null terms then Left "No terms found" else Right terms

--------------------------------------------------------------------------------
-- Import System
--------------------------------------------------------------------------------

resolveImports :: FilePath -> Term -> IO Term
resolveImports baseDir (Node "import" [Str path]) = do
  let fullPath = baseDir ++ "/" ++ path
  content <- readFile fullPath
  case parse content of
    Left err -> error $ "Import error in " ++ path ++ ": " ++ err
    Right t -> resolveImports baseDir t
resolveImports baseDir (Node l cs) = Node l <$> mapM (resolveImports baseDir) cs
resolveImports _ t = return t

--------------------------------------------------------------------------------
-- Pretty Printer
--------------------------------------------------------------------------------

pretty :: Term -> String
pretty (Var v) = v
pretty (MetaVar v) = "$" ++ v
pretty (Str s) = "\"" ++ escape s ++ "\""
pretty (Num n) = show n
pretty (Node l []) = "(" ++ l ++ ")"
pretty (Node l cs) = "(" ++ l ++ " " ++ unwords (map pretty cs) ++ ")"

prettyIndent :: Int -> Term -> String
prettyIndent n (Node l cs) | length cs > 2 = 
  "(" ++ l ++ "\n" ++ unlines (map ((replicate (n+2) ' ' ++) . prettyIndent (n+2)) cs) ++ replicate n ' ' ++ ")"
prettyIndent _ t = pretty t

escape :: String -> String
escape = concatMap (\c -> case c of
  '"' -> "\\\""
  '\n' -> "\\n"
  '\t' -> "\\t"
  _ -> [c])

--------------------------------------------------------------------------------
-- Diff Output
--------------------------------------------------------------------------------

data Diff = Added Term | Removed Term | Changed Term Term | Same Term
  deriving (Show, Eq)

diffTerms :: Term -> Term -> [Diff]
diffTerms t1 t2 | t1 == t2 = [Same t1]
diffTerms (Node l1 cs1) (Node l2 cs2) | l1 == l2 = 
  concatMap (uncurry diffTerms) (zip cs1 cs2) ++
  map Added (drop (length cs1) cs2) ++
  map Removed (drop (length cs2) cs1)
diffTerms t1 t2 = [Changed t1 t2]

showDiff :: Diff -> String
showDiff (Same t) = "  " ++ pretty t
showDiff (Added t) = "+ " ++ pretty t
showDiff (Removed t) = "- " ++ pretty t
showDiff (Changed t1 t2) = "- " ++ pretty t1 ++ "\n+ " ++ pretty t2

--------------------------------------------------------------------------------
-- DOT Graph Visualization
--------------------------------------------------------------------------------

termToDot :: Term -> String
termToDot t = unlines
  [ "digraph Term {"
  , "  rankdir=TB;"
  , "  node [shape=box, fontname=\"Helvetica\"];"
  , ""
  , nodesDot
  , edgesDot
  , "}"
  ]
  where
    (nodes, edges) = collectGraph t 0
    nodesDot = unlines [printf "  n%d [label=\"%s\"];" i (escDot lbl) | (i, lbl) <- nodes]
    edgesDot = unlines [printf "  n%d -> n%d;" src dst | (src, dst) <- edges]
    escDot = concatMap (\c -> if c == '"' then "\\\"" else [c])

collectGraph :: Term -> Int -> ([(Int, String)], [(Int, Int)])
collectGraph (Var v) n = ([(n, v)], [])
collectGraph (MetaVar v) n = ([(n, "$" ++ v)], [])
collectGraph (Str s) n = ([(n, "\"" ++ s ++ "\"")], [])
collectGraph (Num i) n = ([(n, show i)], [])
collectGraph (Node l cs) n = 
  let childStart = n + 1
      (allNodes, allEdges) = collectChildren childStart cs
  in ((n, l) : allNodes, [(n, childStart + i) | i <- [0 .. length cs - 1], not (null cs)] ++ allEdges)
  where
    collectChildren _ [] = ([], [])
    collectChildren start (c:rest) =
      let (ns, es) = collectGraph c start
          nextStart = start + length ns
          (restNs, restEs) = collectChildren nextStart rest
      in (ns ++ restNs, es ++ restEs)

--------------------------------------------------------------------------------
-- JSON Output
--------------------------------------------------------------------------------

termToJson :: Term -> String
termToJson (Var v) = printf "{\"type\":\"var\",\"name\":\"%s\"}" (escJson v)
termToJson (MetaVar v) = printf "{\"type\":\"metavar\",\"name\":\"%s\"}" (escJson v)
termToJson (Str s) = printf "{\"type\":\"string\",\"value\":\"%s\"}" (escJson s)
termToJson (Num n) = printf "{\"type\":\"number\",\"value\":%d}" n
termToJson (Node l cs) = printf "{\"type\":\"node\",\"label\":\"%s\",\"children\":[%s]}" 
  (escJson l) (intercalate "," (map termToJson cs))

escJson :: String -> String
escJson = concatMap (\c -> case c of
  '"' -> "\\\""
  '\\' -> "\\\\"
  '\n' -> "\\n"
  '\t' -> "\\t"
  _ -> [c])

resultToJson :: RewriteResult -> String
resultToJson RewriteResult{..} = printf
  "{\"term\":%s,\"steps\":%d,\"fuelUsed\":%d,\"normalized\":%s}"
  (termToJson resultTerm)
  (length resultSteps)
  resultFuelUsed
  (if resultNormalized then "true" else "false")

--------------------------------------------------------------------------------
-- Cooltt Projection
--------------------------------------------------------------------------------

coolttRules :: [Rule]
coolttRules =
  [ ("path_to_cooltt", Node "path" [mv "i", mv "a", mv "b"],
         Node "cooltt" [Str "ext", mv "i", Str "=>", Str "_", Str "with",
           Node "boundary" [Node "eq0" [mv "i", mv "a"], Node "eq1" [mv "i", mv "b"]]])
  , ("Path_to_cooltt", Node "Path" [mv "A", mv "a", mv "b"],
         Node "cooltt-path" [mv "A", mv "a", mv "b"])
  , ("lam_to_cooltt", Node "lam" [mv "x", mv "body"],
         Node "cooltt-lam" [mv "x", mv "body"])
  , ("pi_to_cooltt", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "cooltt-pi" [mv "x", mv "A", mv "B"])
  , ("app_to_cooltt", Node "app" [mv "f", mv "a"],
         Node "cooltt-app" [mv "f", mv "a"])
  , ("inv_to_cooltt", Node "path-inv" [mv "p"],
         Node "cooltt-symm" [mv "p"])
  , ("comp_to_cooltt", Node "path-comp" [mv "i", mv "p", mv "q"],
         Node "cooltt-trans" [mv "p", mv "q"])
  , ("refl_to_cooltt", Node "reflJ" [mv "t"],
         Node "cooltt-refl" [mv "t"])
  , ("hcom_to_cooltt", Node "hcom" [mv "A", mv "r", mv "s", mv "phi", mv "u"],
         Node "cooltt-hcom" [mv "A", mv "r", mv "s", mv "phi", mv "u"])
  , ("coe_to_cooltt", Node "coe" [mv "A", mv "r", mv "s", mv "a"],
         Node "cooltt-coe" [mv "A", mv "r", mv "s", mv "a"])
  , ("s1_to_cooltt", Node "S1" [], Node "cooltt" [Str "circle"])
  , ("base_to_cooltt", Node "base" [], Node "cooltt" [Str "base"])
  , ("loop_to_cooltt", Node "loop" [mv "i"], Node "cooltt-loop" [mv "i"])
  , ("def_to_cooltt", Node "define" [mv "n", mv "t", mv "b"],
         Node "cooltt-def" [mv "n", mv "t", mv "b"])
  , ("norm_to_cooltt", Node "normalize" [mv "t"],
         Node "cooltt-normalize" [mv "t"])
  , ("type_to_cooltt", Node "Type" [], Node "cooltt" [Str "type"])
  , ("unit_to_cooltt", Node "Unit" [], Node "cooltt" [Str "unit"])
  , ("star_to_cooltt", Node "star" [], Node "cooltt" [Str "★"])
  ]

showCooltt :: Term -> String
showCooltt (Node "cooltt" [Str s]) = s
showCooltt (Node "cooltt" parts) = unwords (map showCooltt parts)
showCooltt (Node "cooltt-path" [a, x, y]) =
  "path " ++ showCooltt a ++ " " ++ showCooltt x ++ " " ++ showCooltt y
showCooltt (Node "cooltt-lam" [x, body]) =
  termName x ++ " => " ++ showCooltt body
showCooltt (Node "cooltt-pi" [x, a, b]) =
  "(" ++ termName x ++ " : " ++ showCooltt a ++ ") → " ++ showCooltt b
showCooltt (Node "cooltt-app" [f, a]) =
  "{" ++ showCooltt f ++ " " ++ showCooltt a ++ "}"
showCooltt (Node "cooltt-symm" [p]) =
  "symm _ {i => " ++ showCooltt p ++ "}"
showCooltt (Node "cooltt-trans" [p, q]) =
  "trans _ {i => " ++ showCooltt p ++ "} {i => " ++ showCooltt q ++ "}"
showCooltt (Node "cooltt-refl" [t]) =
  "refl _ " ++ showCooltt t
showCooltt (Node "cooltt-hcom" [a, r, s, phi, u]) =
  "hcom " ++ showCooltt a ++ " " ++ showCooltt r ++ " " ++ showCooltt s ++
  " {" ++ showCooltt phi ++ "} {" ++ showCooltt u ++ "}"
showCooltt (Node "cooltt-coe" [a, r, s, x]) =
  "coe {i => " ++ showCooltt a ++ " i} " ++ showCooltt r ++ " " ++
  showCooltt s ++ " " ++ showCooltt x
showCooltt (Node "cooltt-loop" [i]) = "loop " ++ showCooltt i
showCooltt (Node "cooltt-def" [n, t, b]) =
  "def " ++ termName n ++ " : " ++ showCooltt t ++ " := " ++ showCooltt b
showCooltt (Node "cooltt-normalize" [t]) = "#normalize " ++ showCooltt t
showCooltt (Node "boundary" [Node "eq0" [i, a], Node "eq1" [_, b]]) =
  "[" ++ showCooltt i ++ "=0 => " ++ showCooltt a ++ " | " ++
  showCooltt i ++ "=1 => " ++ showCooltt b ++ "]"
showCooltt (Var x) = x
showCooltt (MetaVar x) = x
showCooltt (Str s) = s
showCooltt (Num n) = show n
showCooltt (Node l cs) = "(" ++ l ++ " " ++ unwords (map showCooltt cs) ++ ")"

termName :: Term -> String
termName (Var x) = x
termName (MetaVar x) = x
termName t = showCooltt t

toCooltt :: Term -> String
toCooltt t = showCooltt (normalize coolttRules t)

--------------------------------------------------------------------------------
-- Cubical Agda Projection
--------------------------------------------------------------------------------

agdaRules :: [Rule]
agdaRules =
  [ ("path_to_agda", Node "path" [mv "i", mv "a", mv "b"],
         Node "agda-path" [mv "i", mv "a", mv "b"])
  , ("Path_to_agda", Node "Path" [mv "A", mv "a", mv "b"],
         Node "agda-PathP" [mv "A", mv "a", mv "b"])
  , ("lam_to_agda", Node "lam" [mv "x", mv "body"],
         Node "agda-lam" [mv "x", mv "body"])
  , ("pi_to_agda", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "agda-pi" [mv "x", mv "A", mv "B"])
  , ("app_to_agda", Node "app" [mv "f", mv "a"],
         Node "agda-app" [mv "f", mv "a"])
  , ("refl_to_agda", Node "reflJ" [mv "t"],
         Node "agda-refl" [])
  , ("sym_to_agda", Node "path-inv" [mv "p"],
         Node "agda-sym" [mv "p"])
  , ("trans_to_agda", Node "path-comp" [mv "i", mv "p", mv "q"],
         Node "agda-trans" [mv "p", mv "q"])
  , ("hcom_to_agda", Node "hcom" [mv "A", mv "r", mv "s", mv "phi", mv "u"],
         Node "agda-hcomp" [mv "phi", mv "u"])
  , ("coe_to_agda", Node "coe" [mv "A", mv "r", mv "s", mv "a"],
         Node "agda-transp" [mv "A", mv "r", mv "a"])
  , ("s1_to_agda", Node "S1" [], Node "agda" [Str "S¹"])
  , ("base_to_agda", Node "base" [], Node "agda" [Str "base"])
  , ("loop_to_agda", Node "loop" [mv "i"], Node "agda-loop" [mv "i"])
  , ("def_to_agda", Node "define" [mv "n", mv "t", mv "b"],
         Node "agda-def" [mv "n", mv "t", mv "b"])
  , ("type_to_agda", Node "Type" [], Node "agda" [Str "Type"])
  ]

showAgda :: Term -> String
showAgda (Node "agda" [Str s]) = s
showAgda (Node "agda-path" [i, a, b]) =
  "PathP (λ " ++ showAgda i ++ " → _) " ++ showAgda a ++ " " ++ showAgda b
showAgda (Node "agda-PathP" [ty, a, b]) =
  "PathP " ++ showAgda ty ++ " " ++ showAgda a ++ " " ++ showAgda b
showAgda (Node "agda-lam" [x, body]) =
  "λ " ++ termName x ++ " → " ++ showAgda body
showAgda (Node "agda-pi" [x, a, b]) =
  "(" ++ termName x ++ " : " ++ showAgda a ++ ") → " ++ showAgda b
showAgda (Node "agda-app" [f, a]) =
  showAgda f ++ " " ++ showAgda a
showAgda (Node "agda-refl" []) = "refl"
showAgda (Node "agda-sym" [p]) = "sym " ++ showAgda p
showAgda (Node "agda-trans" [p, q]) = showAgda p ++ " ∙ " ++ showAgda q
showAgda (Node "agda-hcomp" [phi, u]) =
  "hcomp {φ = " ++ showAgda phi ++ "} " ++ showAgda u
showAgda (Node "agda-transp" [ty, r, a]) =
  "transp (λ i → " ++ showAgda ty ++ ") " ++ showAgda r ++ " " ++ showAgda a
showAgda (Node "agda-loop" [i]) = "loop " ++ showAgda i
showAgda (Node "agda-def" [n, t, b]) =
  termName n ++ " : " ++ showAgda t ++ "\n" ++ termName n ++ " = " ++ showAgda b
showAgda (Var x) = x
showAgda (MetaVar x) = x
showAgda (Str s) = s
showAgda (Num n) = show n
showAgda (Node l cs) = "(" ++ l ++ " " ++ unwords (map showAgda cs) ++ ")"

toAgda :: Term -> String
toAgda t = showAgda (normalize agdaRules t)

--------------------------------------------------------------------------------
-- Lean4 Projection
--------------------------------------------------------------------------------

lean4Rules :: [Rule]
lean4Rules =
  [ ("path_to_lean", Node "path" [mv "i", mv "a", mv "b"],
         Node "lean-path" [mv "a", mv "b"])
  , ("Path_to_lean", Node "Path" [mv "A", mv "a", mv "b"],
         Node "lean-Path" [mv "A", mv "a", mv "b"])
  , ("lam_to_lean", Node "lam" [mv "x", mv "body"],
         Node "lean-lam" [mv "x", mv "body"])
  , ("pi_to_lean", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "lean-pi" [mv "x", mv "A", mv "B"])
  , ("app_to_lean", Node "app" [mv "f", mv "a"],
         Node "lean-app" [mv "f", mv "a"])
  , ("refl_to_lean", Node "reflJ" [mv "t"],
         Node "lean-rfl" [])
  , ("sym_to_lean", Node "path-inv" [mv "p"],
         Node "lean-symm" [mv "p"])
  , ("trans_to_lean", Node "path-comp" [mv "i", mv "p", mv "q"],
         Node "lean-trans" [mv "p", mv "q"])
  , ("def_to_lean", Node "define" [mv "n", mv "t", mv "b"],
         Node "lean-def" [mv "n", mv "t", mv "b"])
  , ("type_to_lean", Node "Type" [], Node "lean" [Str "Type"])
  , ("s1_to_lean", Node "S1" [], Node "lean" [Str "Circle"])
  ]

showLean :: Term -> String
showLean (Node "lean" [Str s]) = s
showLean (Node "lean-path" [a, b]) = showLean a ++ " = " ++ showLean b
showLean (Node "lean-Path" [ty, a, b]) =
  "@Eq " ++ showLean ty ++ " " ++ showLean a ++ " " ++ showLean b
showLean (Node "lean-lam" [x, body]) =
  "fun " ++ termName x ++ " => " ++ showLean body
showLean (Node "lean-pi" [x, a, b]) =
  "(" ++ termName x ++ " : " ++ showLean a ++ ") → " ++ showLean b
showLean (Node "lean-app" [f, a]) =
  showLean f ++ " " ++ showLean a
showLean (Node "lean-rfl" []) = "rfl"
showLean (Node "lean-symm" [p]) = showLean p ++ ".symm"
showLean (Node "lean-trans" [p, q]) = showLean p ++ ".trans " ++ showLean q
showLean (Node "lean-def" [n, t, b]) =
  "def " ++ termName n ++ " : " ++ showLean t ++ " := " ++ showLean b
showLean (Var x) = x
showLean (MetaVar x) = x
showLean (Str s) = s
showLean (Num n) = show n
showLean (Node l cs) = "(" ++ l ++ " " ++ unwords (map showLean cs) ++ ")"

toLean :: Term -> String
toLean t = showLean (normalize lean4Rules t)

--------------------------------------------------------------------------------
-- Coq Projection
--------------------------------------------------------------------------------

coqRules :: [Rule]
coqRules =
  [ ("path_to_coq", Node "path" [mv "i", mv "a", mv "b"],
         Node "coq-path" [mv "a", mv "b"])
  , ("Path_to_coq", Node "Path" [mv "A", mv "a", mv "b"],
         Node "coq-paths" [mv "A", mv "a", mv "b"])
  , ("lam_to_coq", Node "lam" [mv "x", mv "body"],
         Node "coq-lam" [mv "x", mv "body"])
  , ("pi_to_coq", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "coq-forall" [mv "x", mv "A", mv "B"])
  , ("app_to_coq", Node "app" [mv "f", mv "a"],
         Node "coq-app" [mv "f", mv "a"])
  , ("refl_to_coq", Node "reflJ" [mv "t"],
         Node "coq-idpath" [mv "t"])
  , ("sym_to_coq", Node "path-inv" [mv "p"],
         Node "coq-inverse" [mv "p"])
  , ("trans_to_coq", Node "path-comp" [mv "i", mv "p", mv "q"],
         Node "coq-concat" [mv "p", mv "q"])
  , ("def_to_coq", Node "define" [mv "n", mv "t", mv "b"],
         Node "coq-def" [mv "n", mv "t", mv "b"])
  , ("type_to_coq", Node "Type" [], Node "coq" [Str "Type"])
  ]

showCoq :: Term -> String
showCoq (Node "coq" [Str s]) = s
showCoq (Node "coq-path" [a, b]) = showCoq a ++ " = " ++ showCoq b
showCoq (Node "coq-paths" [ty, a, b]) =
  "@paths " ++ showCoq ty ++ " " ++ showCoq a ++ " " ++ showCoq b
showCoq (Node "coq-lam" [x, body]) =
  "fun " ++ termName x ++ " => " ++ showCoq body
showCoq (Node "coq-forall" [x, a, b]) =
  "forall (" ++ termName x ++ " : " ++ showCoq a ++ "), " ++ showCoq b
showCoq (Node "coq-app" [f, a]) =
  "(" ++ showCoq f ++ " " ++ showCoq a ++ ")"
showCoq (Node "coq-idpath" [t]) = "idpath " ++ showCoq t
showCoq (Node "coq-inverse" [p]) = "inverse " ++ showCoq p
showCoq (Node "coq-concat" [p, q]) = "concat " ++ showCoq p ++ " " ++ showCoq q
showCoq (Node "coq-def" [n, t, b]) =
  "Definition " ++ termName n ++ " : " ++ showCoq t ++ " := " ++ showCoq b ++ "."
showCoq (Var x) = x
showCoq (MetaVar x) = x
showCoq (Str s) = s
showCoq (Num n) = show n
showCoq (Node l cs) = "(" ++ l ++ " " ++ unwords (map showCoq cs) ++ ")"

toCoq :: Term -> String
toCoq t = showCoq (normalize coqRules t)

--------------------------------------------------------------------------------
-- Lego Projection (output .lego files)
--------------------------------------------------------------------------------

legoRules :: [Rule]
legoRules =
  [ ("path_to_lego", Node "path" [mv "i", mv "a", mv "b"],
         Node "lego-path" [mv "i", mv "a", mv "b"])
  , ("Path_to_lego", Node "Path" [mv "A", mv "a", mv "b"],
         Node "lego-Path" [mv "A", mv "a", mv "b"])
  , ("lam_to_lego", Node "lam" [mv "x", mv "body"],
         Node "lego-lam" [mv "x", mv "body"])
  , ("lam2_to_lego", Node "lam" [mv "x", mv "t", mv "body"],
         Node "lego-lam2" [mv "x", mv "t", mv "body"])
  , ("pi_to_lego", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "lego-Pi" [mv "x", mv "A", mv "B"])
  , ("app_to_lego", Node "app" [mv "f", mv "a"],
         Node "lego-app" [mv "f", mv "a"])
  , ("refl_to_lego", Node "reflJ" [mv "t"],
         Node "lego-refl" [mv "t"])
  , ("def_to_lego", Node "define" [mv "n", mv "t", mv "b"],
         Node "lego-def" [mv "n", mv "t", mv "b"])
  , ("rule_to_lego", Node "rule" [mv "n", mv "lhs", mv "rhs"],
         Node "lego-rule" [mv "n", mv "lhs", mv "rhs"])
  , ("type_to_lego", Node "Type" [], Node "lego" [Str "Type"])
  , ("var_to_lego", Node "var" [mv "x"], Node "lego-var" [mv "x"])
  ]

showLego :: Term -> String
showLego (Node "lego" [Str s]) = s
showLego (Node "lego-path" [i, a, b]) = 
  "(path " ++ showLego i ++ " " ++ showLego a ++ " " ++ showLego b ++ ")"
showLego (Node "lego-Path" [ty, a, b]) =
  "(Path " ++ showLego ty ++ " " ++ showLego a ++ " " ++ showLego b ++ ")"
showLego (Node "lego-lam" [x, body]) =
  "(λ " ++ termName x ++ ". " ++ showLego body ++ ")"
showLego (Node "lego-lam2" [x, t, body]) =
  "(lam " ++ termName x ++ " " ++ showLego t ++ " " ++ showLego body ++ ")"
showLego (Node "lego-Pi" [x, a, b]) =
  "(Π (" ++ termName x ++ " : " ++ showLego a ++ "). " ++ showLego b ++ ")"
showLego (Node "lego-app" [f, a]) =
  "(app " ++ showLego f ++ " " ++ showLego a ++ ")"
showLego (Node "lego-refl" [t]) = "(refl " ++ showLego t ++ ")"
showLego (Node "lego-var" [x]) = "(var " ++ termName x ++ ")"
showLego (Node "lego-def" [n, t, b]) =
  "def " ++ termName n ++ " : " ++ showLego t ++ " := " ++ showLego b
showLego (Node "lego-rule" [n, lhs, rhs]) =
  "rule " ++ termName n ++ ":\n  " ++ showLego lhs ++ " ~> " ++ showLego rhs
showLego (Var x) = x
showLego (MetaVar x) = "$" ++ x
showLego (Str s) = "\"" ++ s ++ "\""
showLego (Num n) = show n
showLego (Node l cs) = "(" ++ l ++ " " ++ unwords (map showLego cs) ++ ")"

toLego :: Term -> String
toLego t = showLego (normalize legoRules t)

--------------------------------------------------------------------------------
-- Lego Parser (parse .lego files to Term)
--------------------------------------------------------------------------------

data LegoToken = LTLParen | LTRParen | LTString String | LTNum Int 
               | LTSym String | LTArrow | LTTilde | LTDot | LTColon
               | LTLambda | LTPi | LTSigma | LTDollar
  deriving (Show, Eq)

tokenizeLego :: String -> [LegoToken]
tokenizeLego [] = []
tokenizeLego ('-':'-':xs) = tokenizeLego (dropWhile (/= '\n') xs)  -- line comment
tokenizeLego ('(':xs) = LTLParen : tokenizeLego xs
tokenizeLego (')':xs) = LTRParen : tokenizeLego xs
tokenizeLego ('.':xs) = LTDot : tokenizeLego xs
tokenizeLego (':':xs) = LTColon : tokenizeLego xs
tokenizeLego ('$':xs) = LTDollar : tokenizeLego xs
tokenizeLego ('~':'>':xs) = LTTilde : tokenizeLego xs
tokenizeLego ('→':xs) = LTArrow : tokenizeLego xs
tokenizeLego ('-':'>':xs) = LTArrow : tokenizeLego xs
tokenizeLego ('λ':xs) = LTLambda : tokenizeLego xs
tokenizeLego ('\\':xs) = LTLambda : tokenizeLego xs
tokenizeLego ('Π':xs) = LTPi : tokenizeLego xs
tokenizeLego ('Σ':xs) = LTSigma : tokenizeLego xs
tokenizeLego ('"':xs) = let (s, rest) = parseString xs in LTString s : tokenizeLego rest
tokenizeLego (c:xs) | isSpace c = tokenizeLego xs
tokenizeLego (c:xs) | isDigit c = 
  let (n, rest) = span isDigit (c:xs) in LTNum (read n) : tokenizeLego rest
tokenizeLego xs = let (s, rest) = span isLegoSymChar xs in LTSym s : tokenizeLego rest
  where isLegoSymChar c = isAlphaNum c || c `elem` "_-'?!"

-- Parse a Lego term
parseLegoTerm :: [LegoToken] -> Maybe (Term, [LegoToken])
parseLegoTerm [] = Nothing
parseLegoTerm (LTLParen:LTLambda:rest) = do  -- (λ x. body)
  (x, rest1) <- parseLName rest
  rest2 <- expectDot rest1
  (body, rest3) <- parseLegoTerm rest2
  rest4 <- expectRParen rest3
  return (Node "lam" [Var x, body], rest4)
parseLegoTerm (LTLParen:LTPi:LTLParen:rest) = do  -- (Π (x : A). B)
  (x, rest1) <- parseLName rest
  rest2 <- expectColon rest1
  (a, rest3) <- parseLegoTerm rest2
  rest4 <- expectRParen rest3
  rest5 <- expectDot rest4
  (b, rest6) <- parseLegoTerm rest5
  rest7 <- expectRParen rest6
  return (Node "Pi" [Var x, a, b], rest7)
parseLegoTerm (LTLParen:LTSym name:rest) = do  -- (name args...)
  (args, rest') <- parseLegoArgs rest
  return (Node name args, rest')
parseLegoTerm (LTDollar:LTSym v:rest) = Just (MetaVar v, rest)
parseLegoTerm (LTString s:rest) = Just (Str s, rest)
parseLegoTerm (LTNum n:rest) = Just (Num n, rest)
parseLegoTerm (LTSym s:rest) = Just (Var s, rest)
parseLegoTerm _ = Nothing

parseLName :: [LegoToken] -> Maybe (String, [LegoToken])
parseLName (LTSym s:rest) = Just (s, rest)
parseLName _ = Nothing

expectDot :: [LegoToken] -> Maybe [LegoToken]
expectDot (LTDot:rest) = Just rest
expectDot _ = Nothing

expectColon :: [LegoToken] -> Maybe [LegoToken]
expectColon (LTColon:rest) = Just rest
expectColon _ = Nothing

expectRParen :: [LegoToken] -> Maybe [LegoToken]
expectRParen (LTRParen:rest) = Just rest
expectRParen _ = Nothing

parseLegoArgs :: [LegoToken] -> Maybe ([Term], [LegoToken])
parseLegoArgs (LTRParen:rest) = Just ([], rest)
parseLegoArgs toks = do
  (t, rest) <- parseLegoTerm toks
  (ts, rest') <- parseLegoArgs rest
  return (t:ts, rest')

-- Parse a rule: "rule name: lhs ~> rhs"
parseLegoRule :: [LegoToken] -> Maybe (Term, [LegoToken])
parseLegoRule (LTSym "rule":LTSym name:LTColon:rest) = do
  (lhs, rest1) <- parseLegoTerm rest
  rest2 <- expectTilde rest1
  (rhs, rest3) <- parseLegoTerm rest2
  return (Node "rule" [Var name, lhs, rhs], rest3)
  where expectTilde (LTTilde:r) = Just r
        expectTilde _ = Nothing
parseLegoRule _ = Nothing

-- Parse a piece
parseLegoDefOrRule :: [LegoToken] -> Maybe (Term, [LegoToken])
parseLegoDefOrRule toks@(LTSym "rule":_) = parseLegoRule toks
parseLegoDefOrRule toks@(LTSym "test":_) = parseLegoTest toks
parseLegoDefOrRule toks@(LTLParen:_) = parseLegoTerm toks  -- only parse if starts with (
parseLegoDefOrRule toks@(LTDollar:_) = parseLegoTerm toks  -- or $
parseLegoDefOrRule _ = Nothing  -- skip other tokens

parseLegoTest :: [LegoToken] -> Maybe (Term, [LegoToken])
parseLegoTest (LTSym "test":LTString name:LTColon:rest) = do
  (t, rest') <- parseLegoTerm rest
  return (Node "test" [Str name, t], rest')
parseLegoTest _ = Nothing

-- Parse multiple Lego items, with fuel to prevent infinite loops
parseLegoFile :: [LegoToken] -> [Term]
parseLegoFile toks = go toks (length toks + 1)
  where
    go [] _ = []
    go _ 0 = []  -- fuel exhausted
    go ts fuel = case parseLegoDefOrRule ts of
      Just (t, rest) -> t : go rest (fuel - 1)
      Nothing -> go (drop 1 ts) (fuel - 1)  -- skip token on error

-- Main Lego parser entry point
parseLego :: String -> Either String [Term]
parseLego s = 
  let terms = parseLegoFile (tokenizeLego s)
  in if null terms then Left "No valid Lego terms found" else Right terms

parseLegoSingle :: String -> Either String Term
parseLegoSingle s = case parseLegoTerm (tokenizeLego s) of
  Just (t, []) -> Right t
  Just (t, _) -> Right t  -- allow trailing
  Nothing -> Left "Lego parse error"

--------------------------------------------------------------------------------
-- LLM Integration: Context Budgeting & Prompt Generation
--------------------------------------------------------------------------------

-- Atom: a semantic unit with key, value, cost, relevance, priority
data Atom = Atom 
  { atomKey :: String
  , atomValue :: Term
  , atomCost :: Int       -- token cost
  , atomRelevance :: Int  -- 0-100 relevance score
  , atomPriority :: Int   -- priority level
  } deriving (Show, Eq)

-- Parse atoms from terms
termToAtom :: Term -> Maybe Atom
termToAtom (Node "atom" [Var k, v, Num c, Num r, Num p]) = 
  Just $ Atom k v c r p
termToAtom (Node "atom" [Str k, v, Num c, Num r, Num p]) = 
  Just $ Atom k v c r p
termToAtom _ = Nothing

-- Budget context by token limit
budgetContext :: Int -> [Atom] -> [Atom]
budgetContext maxTokens atoms = go 0 sorted
  where
    -- Sort by (relevance * priority) descending
    sorted = sortBy (flip $ comparing score) atoms
    score a = atomRelevance a * atomPriority a
    go _ [] = []
    go used (a:as)
      | used + atomCost a <= maxTokens = a : go (used + atomCost a) as
      | otherwise = go used as

-- Generate a prompt from atoms
generatePrompt :: String -> [Atom] -> String
generatePrompt task atoms = unlines $
  [ "# Task: " ++ task
  , ""
  , "## Context"
  , ""
  ] ++ map formatAtom atoms ++
  [ ""
  , "## Instructions"
  , "Please complete the task using the context above."
  ]
  where
    formatAtom a = "### " ++ atomKey a ++ "\n" ++ pretty (atomValue a) ++ "\n"

-- LLM rules for prompt generation
llmRules :: [Rule]
llmRules =
  [ ("context_to_prompt", Node "llm-context" [mv "task", mv "atoms"],
         Node "llm-prompt" [mv "task", mv "atoms"])
  , ("budget_context", Node "budget" [mv "limit", Node "context" [mv "atoms"]],
         Node "budgeted-context" [mv "limit", mv "atoms"])
  , ("prompt_header", Node "llm-prompt" [mv "task", mv "atoms"],
         Node "prompt-parts" [Node "header" [mv "task"], Node "body" [mv "atoms"]])
  ]

-- Estimate token count for a term (rough approximation)
estimateTokens :: Term -> Int
estimateTokens (Var s) = max 1 (length s `div` 4 + 1)
estimateTokens (MetaVar s) = max 1 (length s `div` 4 + 1)
estimateTokens (Str s) = length s `div` 4 + 1
estimateTokens (Num _) = 1
estimateTokens (Node l cs) = 1 + sum (map estimateTokens cs)

-- Format term for LLM (more readable than s-expr)
formatForLLM :: Term -> String
formatForLLM (Var x) = x
formatForLLM (MetaVar x) = "<" ++ x ++ ">"
formatForLLM (Str s) = "\"" ++ s ++ "\""
formatForLLM (Num n) = show n
formatForLLM (Node "lam" [x, body]) = "λ" ++ termName x ++ ". " ++ formatForLLM body
formatForLLM (Node "Pi" [x, a, b]) = "(" ++ termName x ++ " : " ++ formatForLLM a ++ ") → " ++ formatForLLM b
formatForLLM (Node "app" [f, a]) = formatForLLM f ++ " " ++ formatForLLM a
formatForLLM (Node "path" [_, a, b]) = formatForLLM a ++ " ≡ " ++ formatForLLM b
formatForLLM (Node "define" [n, t, b]) = 
  termName n ++ " : " ++ formatForLLM t ++ " := " ++ formatForLLM b
formatForLLM (Node "rule" [n, l, r]) = 
  termName n ++ ": " ++ formatForLLM l ++ " ↝ " ++ formatForLLM r
formatForLLM (Node l []) = l
formatForLLM (Node l cs) = l ++ "(" ++ intercalate ", " (map formatForLLM cs) ++ ")"

-- Generate context string for LLM
contextForLLM :: Int -> [Term] -> String
contextForLLM budget terms = 
  let atoms = mapMaybe termToAtom terms
      selected = budgetContext budget atoms
  in unlines $ map (\a -> "- " ++ atomKey a ++ ": " ++ formatForLLM (atomValue a)) selected

-- Parse LLM response (extract code blocks)
parseLLMResponse :: String -> [Term]
parseLLMResponse response = 
  let blocks = extractCodeBlocks response
  in mapMaybe (either (const Nothing) Just . parse) blocks

extractCodeBlocks :: String -> [String]
extractCodeBlocks s = go (lines s) False []
  where
    go [] _ acc = reverse acc
    go (l:ls) False acc
      | "```" `isPrefixOf` l = go ls True []
      | otherwise = go ls False acc
    go (l:ls) True acc
      | "```" `isPrefixOf` l = go ls False (unlines (reverse acc) : [])
      | otherwise = go ls True (l:acc)

--------------------------------------------------------------------------------
-- Core Rewrite Rules
--------------------------------------------------------------------------------

coreRules :: [Rule]
coreRules =
  [ ("tokenize_scoped", Node "tokenize" [mv "piece", mv "t"], 
         Node "viz-node" [mv "t", mv "piece", Num 0, Num 0])
  , ("syntax_literal_ok", Node "literal" [mv "x", Var "syntax"], mv "x")
  , ("content_literal_strict", Node "literal" [mv "x", Var "content"], 
         Node "viz-node" [mv "x", Var "error", Num 0, Num 0])
  , ("pushout_tokens", Node "pushout" [mv "p1", mv "p2", mv "p3"], 
         Node "token-scope" [mv "p3", Node "merge" [Node "token-scope" [mv "p1"], Node "token-scope" [mv "p2"]]])
  , ("select_context", Node "select-context" [Node "budget" [mv "b"], Node "context" [mv "atoms"]], 
         Node "context" [Node "filter-by-budget" [mv "b", mv "atoms"]])
  , ("ide_to_prompt", Node "ide" [mv "g", mv "ctx", mv "focus"], Node "prompt" [mv "ctx"])
  , ("apply_answer", Node "apply" [Node "answer" [mv "t"], Node "ide" [mv "g", mv "ctx", mv "focus"]], 
         Node "ide" [mv "g", mv "ctx", mv "t"])
  , ("step_rewrite", Node "step" [Node "rewrite" [mv "p", mv "t"]], Node "step" [mv "t"])
  , ("normalize_step", Node "normal" [Node "step" [mv "t"]], Node "normal" [mv "t"])
  , ("normalize_done", Node "normal" [mv "t"], Node "nf" [mv "t"])
  , ("atom_cost", Node "atom" [mv "k", mv "v", mv "c", mv "r", mv "p"], 
         Node "weighted" [Node "atom-costed" [mv "k", mv "v"], mv "c"])
  , ("edit_is_path", Node "edit" [mv "t1", mv "t2"], Node "path" [Var "i", mv "t1", mv "t2"])
  , ("apply_path_i0", Node "@" [Node "path" [mv "i", mv "t1", mv "t2"], Var "i0"], mv "t1")
  , ("apply_path_i1", Node "@" [Node "path" [mv "i2", mv "t3", mv "t4"], Var "i1"], mv "t4")
  , ("path_comp_def", Node "path-comp" [mv "j", Node "path" [mv "j2", mv "a", mv "b"], Node "path" [mv "j3", mv "b2", mv "c"]], 
         Node "path" [mv "j", mv "a", mv "c"])
  , ("path_inv_def", Node "path-inv" [Node "path" [mv "i", mv "a", mv "b"]], 
         Node "path" [mv "i", mv "b", mv "a"])
  , ("Eq_refl", Node "reflJ" [mv "t"], Node "path" [Var "i", mv "t", mv "t"])
  ]

--------------------------------------------------------------------------------
-- File Generation
--------------------------------------------------------------------------------

generateCoolttFile :: [Term] -> String
generateCoolttFile ts = unlines $
  [ "-- Generated by phi from CursorForLego"
  , "-- https://github.com/RedPRL/cooltt"
  , ""
  ] ++ map toCooltt ts

generateAgdaFile :: [Term] -> String
generateAgdaFile ts = unlines $
  [ "{-# OPTIONS --cubical #-}"
  , "-- Generated by phi from CursorForLego"
  , ""
  , "open import Cubical.Core.Everything"
  , "open import Cubical.Foundations.Prelude"
  , ""
  ] ++ map toAgda ts

generateLeanFile :: [Term] -> String
generateLeanFile ts = unlines $
  [ "-- Generated by phi from CursorForLego"
  , ""
  , "import Mathlib"
  , ""
  ] ++ map toLean ts

generateCoqFile :: [Term] -> String
generateCoqFile ts = unlines $
  [ "(* Generated by phi from CursorForLego *)"
  , ""
  , "Require Import HoTT."
  , ""
  ] ++ map toCoq ts

generateLegoFile :: [Term] -> String
generateLegoFile ts = unlines $
  [ "-- Generated by phi"
  , ""
  , "lang Generated :="
  , ""
  ] ++ map toLego ts

generateLLMPrompt :: String -> Int -> [Term] -> String
generateLLMPrompt task budget terms = unlines $
  [ "# Task: " ++ task
  , ""
  , "## Context (budget: " ++ show budget ++ " tokens)"
  , ""
  , contextForLLM budget terms
  , ""
  , "## Instructions"
  , "Complete the task using the context above. Return your answer as s-expressions."
  ]

--------------------------------------------------------------------------------
-- Watch Mode
--------------------------------------------------------------------------------

watchFile :: FilePath -> (String -> IO ()) -> IO ()
watchFile path action = do
  putStrLn $ "Watching " ++ path ++ " for changes (Ctrl+C to stop)..."
  mtime <- getModificationTime path
  loop mtime
  where
    loop lastMtime = do
      threadDelay 1000000  -- 1 second
      newMtime <- getModificationTime path
      when (newMtime > lastMtime) $ do
        putStrLn $ "\n[" ++ show newMtime ++ "] File changed, regenerating..."
        content <- readFile path
        action content
      loop newMtime

--------------------------------------------------------------------------------
-- REPL
--------------------------------------------------------------------------------

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "phi REPL - Type expressions or commands"
  putStrLn "Commands: :q :h :rules :cooltt :agda :lean :coq :lego :dot :json :trace :llm :tokens"
  putStrLn ""
  replLoop Nothing
  where
    replLoop :: Maybe Term -> IO ()
    replLoop lastTerm = do
      putStr "φ> "
      hFlush stdout
      line <- getLine
      case words line of
        [":q"] -> putStrLn "Bye!"
        [":quit"] -> putStrLn "Bye!"
        [":h"] -> showHelp >> replLoop lastTerm
        [":help"] -> showHelp >> replLoop lastTerm
        [":rules"] -> showRules >> replLoop lastTerm
        [":cooltt"] -> maybe (putStrLn "No term") (putStrLn . toCooltt) lastTerm >> replLoop lastTerm
        [":agda"] -> maybe (putStrLn "No term") (putStrLn . toAgda) lastTerm >> replLoop lastTerm
        [":lean"] -> maybe (putStrLn "No term") (putStrLn . toLean) lastTerm >> replLoop lastTerm
        [":coq"] -> maybe (putStrLn "No term") (putStrLn . toCoq) lastTerm >> replLoop lastTerm
        [":lego"] -> maybe (putStrLn "No term") (putStrLn . toLego) lastTerm >> replLoop lastTerm
        [":dot"] -> maybe (putStrLn "No term") (putStrLn . termToDot) lastTerm >> replLoop lastTerm
        [":json"] -> maybe (putStrLn "No term") (putStrLn . termToJson) lastTerm >> replLoop lastTerm
        [":tokens"] -> maybe (putStrLn "No term") (putStrLn . show . estimateTokens) lastTerm >> replLoop lastTerm
        [":llm"] -> maybe (putStrLn "No term") (putStrLn . formatForLLM) lastTerm >> replLoop lastTerm
        [":trace"] -> case lastTerm of
          Nothing -> putStrLn "No term" >> replLoop lastTerm
          Just t -> do
            let steps = resultSteps (normalizeWithMetrics coreRules t)
            forM_ (zip [1..] steps) $ \(i, s) ->
              putStrLn $ show (i::Int) ++ ". " ++ stepRule s ++ ": " ++ pretty (stepAfter s)
            replLoop lastTerm
        [":diff"] -> case lastTerm of
          Nothing -> putStrLn "No term" >> replLoop lastTerm
          Just t -> do
            let t' = normalize coreRules t
            mapM_ (putStrLn . showDiff) (diffTerms t t')
            replLoop lastTerm
        [":metrics"] -> case lastTerm of
          Nothing -> putStrLn "No term" >> replLoop lastTerm
          Just t -> do
            let r = normalizeWithMetrics coreRules t
            putStrLn $ "Steps: " ++ show (length (resultSteps r))
            putStrLn $ "Fuel used: " ++ show (resultFuelUsed r)
            putStrLn $ "Normalized: " ++ show (resultNormalized r)
            replLoop lastTerm
        [] -> replLoop lastTerm
        _ | null line -> replLoop lastTerm
          | otherwise -> case parse line of
              Left err -> putStrLn ("Parse error: " ++ err) >> replLoop lastTerm
              Right t -> do
                let t' = normalize coreRules t
                putStrLn $ "  → " ++ pretty t'
                replLoop (Just t)
    
    showHelp = putStrLn $ unlines
      [ "Commands:"
      , "  :q, :quit     Exit REPL"
      , "  :h, :help     Show this help"
      , "  :rules        List available rules"
      , "  :cooltt       Project last term to cooltt"
      , "  :agda         Project last term to Agda"
      , "  :lean         Project last term to Lean4"
      , "  :coq          Project last term to Coq"
      , "  :lego         Project last term to Lego"
      , "  :dot          Output DOT graph"
      , "  :json         Output JSON"
      , "  :trace        Show rewrite trace"
      , "  :diff         Show diff from original"
      , "  :metrics      Show rewrite metrics"
      , "  :tokens       Estimate token count"
      , "  :llm          Format for LLM"
      , ""
      , "Enter any s-expression to evaluate"
      ]
    
    showRules = forM_ coreRules $ \(name, pat, _) ->
      putStrLn $ "  " ++ name ++ ": " ++ pretty pat

--------------------------------------------------------------------------------
-- CLI
--------------------------------------------------------------------------------

usage :: String
usage = unlines
  [ "phi - Term Rewriting CLI for CursorForLego"
  , ""
  , "USAGE:"
  , "  phi <command> [options] [file]"
  , ""
  , "COMMANDS:"
  , "  rewrite <file>              Apply rewrite rules, show result"
  , "  rewrite -v <file>           Verbose: show each rewrite step"
  , "  to-cooltt <file>            Project to cooltt syntax"
  , "  to-agda <file>              Project to Cubical Agda syntax"
  , "  to-lean <file>              Project to Lean4 syntax"
  , "  to-coq <file>               Project to Coq/HoTT syntax"
  , "  to-lego <file>              Project to Lego syntax"
  , "  parse <file>                Parse s-expr and pretty-print"
  , "  parse-lego <file>           Parse Lego s-expr (λ, Π syntax)"
  , "  dot <file>                  Output DOT graph"
  , "  json <file>                 Output JSON"
  , "  gen-cooltt <file> -o <out>  Generate cooltt file"
  , "  gen-agda <file> -o <out>    Generate Agda file"
  , "  gen-lean <file> -o <out>    Generate Lean4 file"
  , "  gen-coq <file> -o <out>     Generate Coq file"
  , "  gen-lego <file> -o <out>    Generate Lego file"
  , "  eval '<expr>'               Evaluate inline expression"
  , "  diff <file1> <file2>        Show diff between files"
  , "  metrics <file>              Show rewrite metrics"
  , "  tokens <file>               Estimate token count for LLM"
  , "  llm-prompt <task> <file>    Generate LLM prompt with context"
  , "  llm-format <file>           Format term for LLM readability"
  , "  watch <file> -o <out>       Watch and regenerate"
  , "  repl                        Interactive REPL"
  , "  test                        Run built-in tests"
  , ""
  , "OPTIONS:"
  , "  -v, --verbose               Show detailed output"
  , "  -o <file>                   Output file"
  , "  --budget <n>                Token budget for LLM context"
  , "  --json                      Output as JSON"
  , ""
  , "FILE FORMATS:"
  , "  .sexp  S-expressions: (node arg1 arg2 ...)"
  , "  .lego  Lego syntax: lang Name := piece Foo ..."
  , ""
  , "EXAMPLES:"
  , "  phi repl"
  , "  phi eval '(path i a b)'"
  , "  phi to-cooltt path.sexp"
  , "  phi parse-lego Lambda.lego"
  , "  phi gen-cooltt defs.sexp -o defs.cooltt"
  , "  phi llm-prompt 'prove symmetry' context.sexp"
  , "  phi tokens context.sexp"
  , "  phi watch defs.sexp -o defs.cooltt"
  ]

main :: IO ()
main = getArgs >>= \case
  [] -> putStrLn usage
  ["help"] -> putStrLn usage
  ["--help"] -> putStrLn usage
  ["-h"] -> putStrLn usage
  
  ["repl"] -> repl
  ["test"] -> runTests
  
  ["parse", file] -> readAndParse file >>= putStrLn . pretty
  
  ["parse-lego", file] -> do
    content <- readFile file
    case parseLego content of
      Left err -> die err
      Right ts -> mapM_ (putStrLn . pretty) ts
  
  ["rewrite", file] -> readAndParse file >>= putStrLn . pretty . normalize coreRules
  
  ["rewrite", "-v", file] -> do
    t <- readAndParse file
    let steps = resultSteps (normalizeWithMetrics coreRules t)
    forM_ (zip [0..] ((RewriteStep "input" t t) : steps)) $ \(i, s) ->
      putStrLn $ show (i::Int) ++ ". " ++ stepRule s ++ ":\n   " ++ pretty (stepAfter s)
  
  ["to-cooltt", file] -> readAndParse file >>= putStrLn . toCooltt
  ["to-agda", file] -> readAndParse file >>= putStrLn . toAgda
  ["to-lean", file] -> readAndParse file >>= putStrLn . toLean
  ["to-coq", file] -> readAndParse file >>= putStrLn . toCoq
  ["to-lego", file] -> readAndParse file >>= putStrLn . toLego
  
  ["dot", file] -> readAndParse file >>= putStrLn . termToDot
  
  ["json", file] -> readAndParse file >>= putStrLn . termToJson
  ["json", "-r", file] -> do
    t <- readAndParse file
    putStrLn $ resultToJson (normalizeWithMetrics coreRules t)
  
  ["tokens", file] -> do
    t <- readAndParse file
    putStrLn $ "Estimated tokens: " ++ show (estimateTokens t)
  
  ["llm-format", file] -> readAndParse file >>= putStrLn . formatForLLM
  
  ["llm-prompt", task, file] -> do
    ts <- readAndParseAll file
    putStrLn $ generateLLMPrompt task 4000 ts
  
  ["llm-prompt", task, file, "--budget", budgetStr] -> do
    ts <- readAndParseAll file
    let budget = read budgetStr :: Int
    putStrLn $ generateLLMPrompt task budget ts
  
  ["metrics", file] -> do
    t <- readAndParse file
    let r = normalizeWithMetrics coreRules t
    putStrLn $ "Steps taken:  " ++ show (length (resultSteps r))
    putStrLn $ "Fuel used:    " ++ show (resultFuelUsed r)
    putStrLn $ "Normalized:   " ++ show (resultNormalized r)
    putStrLn $ "Rules fired:  " ++ intercalate ", " (nub $ map stepRule (resultSteps r))
  
  ["diff", file1, file2] -> do
    t1 <- readAndParse file1
    t2 <- readAndParse file2
    mapM_ (putStrLn . showDiff) (diffTerms t1 t2)
  
  ["gen-cooltt", file, "-o", outFile] -> do
    ts <- readAndParseAll file
    writeFile outFile (generateCoolttFile ts)
    putStrLn $ "Generated: " ++ outFile
  
  ["gen-agda", file, "-o", outFile] -> do
    ts <- readAndParseAll file
    writeFile outFile (generateAgdaFile ts)
    putStrLn $ "Generated: " ++ outFile
  
  ["gen-lean", file, "-o", outFile] -> do
    ts <- readAndParseAll file
    writeFile outFile (generateLeanFile ts)
    putStrLn $ "Generated: " ++ outFile
  
  ["gen-coq", file, "-o", outFile] -> do
    ts <- readAndParseAll file
    writeFile outFile (generateCoqFile ts)
    putStrLn $ "Generated: " ++ outFile
  
  ["gen-lego", file, "-o", outFile] -> do
    ts <- readAndParseAll file
    writeFile outFile (generateLegoFile ts)
    putStrLn $ "Generated: " ++ outFile
  
  ["watch", file, "-o", outFile] -> do
    let ext = reverse $ takeWhile (/= '.') (reverse outFile)
    let gen = case ext of
          "cooltt" -> generateCoolttFile
          "agda" -> generateAgdaFile
          "lean" -> generateLeanFile
          "v" -> generateCoqFile
          _ -> generateCoolttFile
    watchFile file $ \content -> case parseAll content of
      Left err -> putStrLn $ "Error: " ++ err
      Right ts -> do
        writeFile outFile (gen ts)
        putStrLn $ "Regenerated: " ++ outFile
  
  ["eval", expr] -> case parse expr of
    Left err -> die err
    Right t -> do
      putStrLn $ "Input:   " ++ pretty t
      let r = normalizeWithMetrics coreRules t
      putStrLn $ "Rewrite: " ++ pretty (resultTerm r)
      putStrLn $ "Cooltt:  " ++ toCooltt t
      putStrLn $ "Agda:    " ++ toAgda t
      putStrLn $ "Lean4:   " ++ toLean t
      putStrLn $ "Coq:     " ++ toCoq t
      putStrLn $ "Steps:   " ++ show (length (resultSteps r))
  
  args -> die $ "Unknown command: " ++ unwords args ++ "\nRun 'phi help' for usage."

readAndParse :: FilePath -> IO Term
readAndParse file = do
  content <- readFile file
  case parse content of
    Left err -> die err
    Right t -> return t

readAndParseAll :: FilePath -> IO [Term]
readAndParseAll file = do
  content <- readFile file
  case parseAll content of
    Left err -> die err
    Right ts -> return ts

die :: String -> IO a
die msg = hPutStrLn stderr ("Error: " ++ msg) >> exitFailure

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

runTests :: IO ()
runTests = do
  putStrLn "=== Running Tests ===\n"
  
  testSection "Parser"
  test "parse simple" $ parse "(foo bar)" == Right (Node "foo" [Var "bar"])
  test "parse nested" $ parse "(a (b c))" == Right (Node "a" [Node "b" [Var "c"]])
  test "parse string" $ parse "\"hello\"" == Right (Str "hello")
  test "parse number" $ parse "42" == Right (Num 42)
  test "parse neg num" $ parse "-5" == Right (Num (-5))
  test "parse comment" $ parse "; comment\n(foo)" == Right (Node "foo" [])
  test "parse multi" $ length (parseMultiple (tokenize "(a)(b)(c)")) == 3
  
  testSection "Rewrites"
  let tokenTest = Node "tokenize" [Var "Interval", Var "∧"]
  test "tokenize" $ normalize coreRules tokenTest == 
    Node "viz-node" [Var "∧", Var "Interval", Num 0, Num 0]
  
  let literalSyn = Node "literal" [Str "(", Var "syntax"]
  test "literal syntax" $ normalize coreRules literalSyn == Str "("
  
  let literalCon = Node "literal" [Str "x", Var "content"]
  test "literal content" $ case normalize coreRules literalCon of
    Node "viz-node" _ -> True
    _ -> False
  
  testSection "Paths"
  let pathTest = Node "path" [Var "i", Var "a", Var "b"]
  test "path i0" $ normalize coreRules (Node "@" [pathTest, Var "i0"]) == Var "a"
  test "path i1" $ normalize coreRules (Node "@" [pathTest, Var "i1"]) == Var "b"
  
  testSection "Cooltt Projection"
  test "path to cooltt" $ toCooltt pathTest == "ext i => _ with [i=0 => a | i=1 => b]"
  test "lam to cooltt" $ toCooltt (Node "lam" [Var "x", Var "x"]) == "x => x"
  test "pi to cooltt" $ toCooltt (Node "Pi" [Var "A", Node "Type" [], Var "A"]) == 
    "(A : type) → A"
  test "refl to cooltt" $ toCooltt (Node "reflJ" [Var "a"]) == "refl _ a"
  
  testSection "Agda Projection"
  test "path to agda" $ toAgda pathTest == "PathP (λ i → _) a b"
  test "lam to agda" $ toAgda (Node "lam" [Var "x", Var "x"]) == "λ x → x"
  test "refl to agda" $ toAgda (Node "reflJ" [Var "a"]) == "refl"
  
  testSection "Lean4 Projection"
  test "path to lean" $ toLean pathTest == "a = b"
  test "lam to lean" $ toLean (Node "lam" [Var "x", Var "x"]) == "fun x => x"
  test "refl to lean" $ toLean (Node "reflJ" [Var "a"]) == "rfl"
  
  testSection "Coq Projection"
  test "path to coq" $ toCoq pathTest == "a = b"
  test "lam to coq" $ toCoq (Node "lam" [Var "x", Var "x"]) == "fun x => x"
  test "refl to coq" $ toCoq (Node "reflJ" [Var "a"]) == "idpath a"
  
  testSection "Lego Projection"
  test "lam to lego" $ toLego (Node "lam" [Var "x", Var "x"]) == "(λ x. x)"
  test "pi to lego" $ toLego (Node "Pi" [Var "A", Node "Type" [], Var "A"]) == 
    "(Π (A : Type). A)"
  test "path to lego" $ toLego pathTest == "(path i a b)"
  
  testSection "Lego Parser"
  test "lego parse lam" $ case parseLegoSingle "(λ x. x)" of
    Right (Node "lam" [Var "x", Var "x"]) -> True
    _ -> False
  test "lego parse app" $ case parseLegoSingle "(app f x)" of
    Right (Node "app" [Var "f", Var "x"]) -> True
    _ -> False
  test "lego parse metavar" $ case parseLegoSingle "$foo" of
    Right (MetaVar "foo") -> True
    _ -> False
  
  testSection "LLM Integration"
  test "estimate tokens" $ estimateTokens (Node "app" [Var "f", Var "x"]) > 0
  test "format for LLM" $ formatForLLM (Node "lam" [Var "x", Var "x"]) == "λx. x"
  let testAtom = Node "atom" [Str "test", Var "value", Num 10, Num 80, Num 5]
  test "parse atom" $ isJust (termToAtom testAtom)
  test "budget context" $ 
    let atoms = [Atom "a" (Var "x") 5 100 10, Atom "b" (Var "y") 100 50 5]
    in length (budgetContext 10 atoms) == 1
  
  testSection "DOT Output"
  test "dot output" $ "digraph" `isPrefixOf` termToDot (Var "x")
  
  testSection "JSON Output"
  test "json var" $ termToJson (Var "x") == "{\"type\":\"var\",\"name\":\"x\"}"
  test "json num" $ termToJson (Num 42) == "{\"type\":\"number\",\"value\":42}"
  
  testSection "Metrics"
  let atom = Node "atom" [Var "g", Var "g1", Num 5, Num 10, Num 8]
  let r = normalizeWithMetrics coreRules atom
  test "metrics steps" $ length (resultSteps r) >= 1  -- at least one step
  test "metrics normalized" $ resultNormalized r
  
  testSection "Diff"
  test "diff same" $ diffTerms (Var "x") (Var "x") == [Same (Var "x")]
  test "diff changed" $ case diffTerms (Var "x") (Var "y") of
    [Changed _ _] -> True
    _ -> False
  
  putStrLn "\n=== All tests completed ==="

testSection :: String -> IO ()
testSection name = putStrLn $ "\n-- " ++ name ++ " --"

test :: String -> Bool -> IO ()
test name True = putStrLn $ "✓ " ++ name
test name False = putStrLn $ "✗ " ++ name ++ " FAILED"
