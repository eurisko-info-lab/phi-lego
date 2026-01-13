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

import Lego (GrammarExpr, pattern GEmpty, pattern GLit, pattern GSyntax, pattern GKeyword,
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
transformGrammar :: String -> GrammarExpr () -> GrammarExpr ()
transformGrammar prodName g = wrapIfDecl prodName (transform prodName g)

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

transform :: String -> GrammarExpr () -> GrammarExpr ()
transform prodName = go
  where
    -- Piece prefix for this production (e.g., "Atom" from "Atom.ident")
    piecePrefix = case break (== '.') prodName of
                    (p, _:_) -> p
                    _ -> ""
    
    go :: GrammarExpr () -> GrammarExpr ()
    go GEmpty = GEmpty
    go (GLit s) 
      | isKeyword s = GSyntax s  -- Keywords become syntax
      | otherwise = GLit s       -- Regular literals stay as lit
    go (GSyntax s) = GSyntax s
    go (GKeyword s) = GSyntax s
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
isKeyword :: String -> Bool
isKeyword s = s `elem` keywords
  where
    keywords = ["lang", "import", "grammar", "piece", "rule", "test", "def", "law", "inherit",
                "@autocut", ":=", "::=", "~>", "<~", "<~>", "~~>", "==>", ":", ".", ",",
                "(", ")", "[", "]", "{", "}", "|", "*", "+", "?", "=", "==", "≅",
                "prelude", "code", "when", "λ", "\\", "λᵢ", "Π", "Σ", "∀", "$", "?",
                "μ", "ε", "<", ">"]

-- | Format grammar map as sexpr with nice formatting
formatGrammar :: M.Map String (GrammarExpr ()) -> String
formatGrammar m = unlines $
  ["(grammar"] ++
  [formatProd name g | (name, g) <- M.toList m] ++
  [")"]
  where
    formatProd name g = "  (prod " ++ show name ++ " " ++ printSExpr (grammarToSExpr g) ++ ")"

