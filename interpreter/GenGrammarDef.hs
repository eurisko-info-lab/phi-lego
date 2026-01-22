{-# LANGUAGE PatternSynonyms #-}
-- | Grammar.sexpr Generator
--
-- Bootstrap tool: Uses current Grammar.sexpr to parse Grammar.lego
-- and generates a new Grammar.sexpr
--
-- NOTE: The generated output is close to but not identical to the hand-crafted
-- Grammar.sexpr. The hand-crafted version includes additional AST node wrappers
-- (like DLaw, DImport) that aren't directly specified in Grammar.lego.
--
-- Usage: cabal run gen-grammar-def -- prelude/lego/Grammar.lego > prelude/lego/Grammar.sexpr.new
--
-- To compare: diff prelude/lego/Grammar.sexpr prelude/lego/Grammar.sexpr.new
--
module Main where

import Lego (GrammarExpr, pattern GEmpty, pattern GLit,
             pattern GRegex, pattern GChar, pattern GNode, pattern GSeq, pattern GAlt,
             pattern GStar, pattern GRec, pattern GRef, pattern GBind, pattern GCut, pattern GAny)
import Lego.GrammarParser (parseLegoFile, LegoDecl(..))
import Lego.SExpr (printSExpr, grammarToSExpr)
import System.Environment (getArgs)
import System.IO (stderr, hPutStrLn)
import qualified Data.Map as M
import Data.Char (toUpper)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> hPutStrLn stderr "Usage: gen-grammar-def <Grammar.lego>" 
    (path:_) -> do
      content <- readFile path
      case parseLegoFile content of
        Left err -> hPutStrLn stderr $ "Parse error: " ++ err
        Right decls -> do
          let grammarDecls = extractGrammarDecls decls
              -- Qualify unqualified references and add syntax/node wrappers
              transformed = [(name, transformGrammar name g) | (name, g) <- grammarDecls]
              grammarMap = M.fromList transformed
          if M.null grammarMap
            then hPutStrLn stderr "No grammar declarations found"
            else putStr $ formatGrammar grammarMap

-- | Extract all DGrammar declarations from parsed file
-- Handles top-level, piece, and lang declarations
extractGrammarDecls :: [LegoDecl] -> [(String, GrammarExpr ())]
extractGrammarDecls = concatMap extractFromDecl

extractFromDecl :: LegoDecl -> [(String, GrammarExpr ())]
extractFromDecl (DGrammar name g) = [(name, g)]
extractFromDecl (DPiece _ _ body) = extractGrammarDecls body
extractFromDecl (DLang _ _ body) = extractGrammarDecls body
extractFromDecl _ = []

-- | Transform grammar for output:
-- 1. Qualify references with piece names (ident → Atom.ident)
-- 2. Wrap File.*Decl productions in node D* constructors
-- 3. Distinguish syntax keywords from literals
-- 4. Convert "$ nodeName" suffix annotations to (node nodeName ...) wrappers
transformGrammar :: String -> GrammarExpr () -> GrammarExpr ()
transformGrammar prodName g = wrapIfDecl prodName (transform prodName (convertNodeAnnotations g))

-- | Wrap file declarations in node constructors
-- File.importDecl → (node DImport ...)
-- File.langDecl → (node DLang ...)
-- EXCEPT fileDecl itself which is just an alternation
wrapIfDecl :: String -> GrammarExpr () -> GrammarExpr ()
wrapIfDecl prodName g
  | prodName `elem` noWrapDecls = g  -- These don't get wrapped
  | "File." `isPrefixOf` prodName && "Decl" `isSuffixOf` prodName =
      let baseName = drop 5 (take (length prodName - 4) prodName)  -- remove "File." and "Decl"
          nodeName = "D" ++ capitalize baseName
      in GNode nodeName [g]
  | otherwise = g
  where
    capitalize [] = []
    capitalize (c:cs) = toUpper c : cs
    -- These File.*Decl productions don't get node wrappers
    noWrapDecls = ["File.fileDecl", "File.grammarDecl", "File.pieceDecl", "File.fileDeclWithWs"]

-- | Check if a string is a prefix of another
isPrefixOf :: String -> String -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (p:ps) (s:ss) = p == s && isPrefixOf ps ss

-- | Check if a string is a suffix of another
isSuffixOf :: String -> String -> Bool
isSuffixOf suf str = reverse suf `isPrefixOf` reverse str

-- | Convert "$ nodeName" suffix annotations to (node nodeName ...) wrappers
-- 
-- Grammar.lego uses:   "(" "λ" ident "." term ")" $ lam
-- Which parses as:     (seq (lit "(") (lit λ) ... (bind lam (any)))
-- Should become:       (node lam (seq (lit "(") (lit λ) ...))
--
-- This detects GSeq ending with GBind name GAny and wraps in GNode
convertNodeAnnotations :: GrammarExpr () -> GrammarExpr ()
convertNodeAnnotations = goTop
  where
    -- Top-level handler - process alternatives and sequences
    goTop :: GrammarExpr () -> GrammarExpr ()
    goTop (GAlt g1 g2) = GAlt (goTop g1) (goTop g2)
    goTop g = case extractNodeAnnotation g of
      Just (nodeName, body) 
        -- Special case: "constr" needs old-style (node constructor argGram) format
        -- for the special handler in GrammarInterp
        | nodeName == "constr" -> 
            case extractConstrArg body of
              Just argGram -> GNode "constructor" [convertNodeAnnotations argGram]
              Nothing -> GNode nodeName [convertNodeAnnotations body]
        | otherwise -> GNode nodeName [convertNodeAnnotations body]
      Nothing -> goOther g
    
    -- Extract the argument grammar from a constr pattern: "(" ident arg* ")" -> arg
    extractConstrArg :: GrammarExpr () -> Maybe (GrammarExpr ())
    extractConstrArg g = 
      let parts = flattenSeq g
      in case parts of
           [GLit "(", GRef _, GStar argGram, GLit ")"] -> Just argGram
           _ -> Nothing
    
    -- Flatten a sequence into a list of parts
    flattenSeq :: GrammarExpr () -> [GrammarExpr ()]
    flattenSeq (GSeq g1 g2) = flattenSeq g1 ++ flattenSeq g2
    flattenSeq g = [g]
    
    -- For non-node-annotated expressions, recurse into structure
    goOther :: GrammarExpr () -> GrammarExpr ()
    goOther GEmpty = GEmpty
    goOther (GLit s) = GLit s
    goOther (GRegex s) = GRegex s
    goOther (GChar s) = GChar s
    goOther (GRef s) = GRef s
    goOther (GSeq g1 g2) = GSeq (goOther g1) (goOther g2)
    goOther (GAlt g1 g2) = GAlt (goTop g1) (goTop g2)  -- re-enter top for alts
    goOther (GStar g) = GStar (goOther g)
    goOther (GRec x g) = GRec x (goOther g)
    goOther (GBind x g) = GBind x (goOther g)
    goOther (GCut g) = GCut (goOther g)
    goOther (GNode name gs) = GNode name (map goOther gs)
    goOther GAny = GAny
    goOther _ = GEmpty
    
    -- Extract node annotation from a sequence ending with (bind name (any))
    -- Returns (nodeName, bodyGrammar) if found
    extractNodeAnnotation :: GrammarExpr () -> Maybe (String, GrammarExpr ())
    extractNodeAnnotation g = 
      let (parts, mAnnot) = collectSeqParts g []
      in case mAnnot of
           Just name | not (null parts) -> Just (name, rebuildSeq parts)
           _ -> Nothing
    
    -- Collect all parts of a right-associative sequence, looking for trailing (bind name (any))
    collectSeqParts :: GrammarExpr () -> [GrammarExpr ()] -> ([GrammarExpr ()], Maybe String)
    collectSeqParts (GSeq g1 (GBind name GAny)) acc = (reverse (g1 : acc), Just name)
    collectSeqParts (GSeq g1 g2) acc = collectSeqParts g2 (g1 : acc)
    collectSeqParts g acc = (reverse (g : acc), Nothing)
    
    -- Rebuild a flat list of grammars into nested GSeq
    rebuildSeq :: [GrammarExpr ()] -> GrammarExpr ()
    rebuildSeq [] = GEmpty
    rebuildSeq [g] = g
    rebuildSeq (g:gs) = GSeq g (rebuildSeq gs)

transform :: String -> GrammarExpr () -> GrammarExpr ()
transform prodName = go
  where
    -- Piece prefix for this production (e.g., "Atom" from "Atom.ident")
    piecePrefix = case break (== '.') prodName of
                    (p, _:_) -> p
                    _ -> ""
    
    go :: GrammarExpr () -> GrammarExpr ()
    go GEmpty = GEmpty
    go (GLit s) = GLit s
    go (GRegex s) = GRegex s
    go (GChar s) = GChar s
    go (GRef s) = GRef (qualifyRef piecePrefix s)
    go (GSeq g1 g2) = GSeq (go g1) (go g2)
    go (GAlt g1 g2) = GAlt (go g1) (go g2)
    go (GStar g) = GStar (go g)
    go (GRec x g) = GRec x (go g)
    go (GBind x g) = GBind x (go g)
    go (GCut g) = GCut (go g)
    go (GNode name gs) = GNode name (map go gs)
    go GAny = GAny
    go _ = GEmpty

-- | Qualify unqualified references
-- "ident" → "Atom.ident" if in Atom piece
-- "term" → "Term.term" if in Term piece  
qualifyRef :: String -> String -> String
qualifyRef piecePrefix ref
  | '.' `elem` ref = ref  -- Already qualified
  | ref `elem` atomRefs = "Atom." ++ ref
  | ref `elem` termRefs = "Term." ++ ref
  | ref `elem` fileRefs = "File." ++ ref
  | ref `elem` grammarRefs = "GrammarExpr." ++ ref
  | ref `elem` patternRefs = "Pattern." ++ ref
  | ref `elem` templateRefs = "Template." ++ ref
  | ref `elem` ruleRefs = "Rule." ++ ref
  | ref `elem` testRefs = "Test." ++ ref
  | ref `elem` lawRefs = "Law." ++ ref
  | not (null piecePrefix) = piecePrefix ++ "." ++ ref
  | otherwise = ref
  where
    atomRefs = ["ident", "string", "regex", "char", "number", "chars", "metavar"]
    termRefs = ["term", "typedBinder"]
    fileRefs = ["whitespace", "fileDecl", "fileDeclWithWs", "legoFile", "langDecl", "importDecl",
                "grammarDecl", "pieceDecl", "ruleDecl", "ruleStub", "testDecl", "lawDecl",
                "inheritDecl", "autocutDecl", "defDecl", "langParents", "langParentsOpt",
                "langDirectBody", "langItemWithWs", "langItem", "pieceItem", "productionWithWs",
                "grammarProd", "sectionMarker", "sectionName", "qualIdent", "testExpected",
                "testExpectedArrow", "testExpectedDouble", "wsItem", "emptyParents", "moreParents",
                "lawOp", "commentDecl", "commentText"]
    grammarRefs = ["grammarExpr", "grammarAlt", "grammarSeq", "grammarSuffix", "grammarAtom",
                   "altBranch", "seqHead", "production", "grammarExprFull", "grammarExprTerm",
                   "grammarAtomTerm", "grammarSeqTerm", "grammarAltTerm", "grammarSuffixTerm",
                   "grammarWhitespace", "productionNode", "altContinuation"]
    patternRefs = ["pattern"]
    templateRefs = ["template"]
    ruleRefs = ["rule", "forwardRule", "backwardRule", "bidiRule", "guard"]
    testRefs = ["test", "fullTest", "parseTest"]
    lawRefs = ["law"]

-- | Check if a string is a keyword (should use syntax instead of lit)

-- | Format grammar map as sexpr with nice formatting
formatGrammar :: M.Map String (GrammarExpr ()) -> String
formatGrammar m = unlines $
  ["(grammar"] ++
  [formatProd name g | (name, g) <- M.toList m] ++
  [")"]
  where
    formatProd name g = "  (prod " ++ show name ++ " " ++ printSExpr (grammarToSExpr g) ++ ")"

