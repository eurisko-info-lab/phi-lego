{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | S-Expression representation for GrammarExpr
--
-- This module provides a simple, portable serialization format for grammars.
-- S-expressions are the algebraic/canonical form - easy to parse, print, and transform.
--
-- == Algebra
--
-- SExpr forms a free algebra with two constructors:
--   Atom: leaf values (strings)
--   List: sequences of S-expressions
--
-- Grammar → SExpr is a homomorphism (structure-preserving)
-- SExpr → Grammar is the inverse (when well-formed)
--
-- == Format
--
-- @
-- (grammar
--   (prod "Atom.ident" (node "identifier"))
--   (prod "Term.lam" (seq (lit "(") (lit "λ") (ref "Atom.ident") (lit ".") (ref "Term.term") (lit ")"))))
-- @
--
module Lego.SExpr
  ( -- * S-Expression Type
    SExpr(..)
    -- * Parsing
  , parseSExpr
  , parseSExprs
    -- * Printing
  , printSExpr
  , printSExprs
    -- * Grammar Conversion
  , grammarToSExpr
  , grammarMapToSExpr
  , sexprToGrammar
  , sexprToGrammarMap
  , formatGrammarSExpr
    -- * File I/O
  , readSExprFile
  , writeSExprFile
  ) where

import Lego (GrammarExpr, pattern GEmpty, pattern GLit,
             pattern GRegex, pattern GChar, pattern GNode, pattern GSeq, pattern GAlt,
             pattern GStar, pattern GRec, pattern GRef, pattern GBind, pattern GCut, pattern GAny)
import qualified Data.Map as M
import Data.Char (isSpace, isAlphaNum)

--------------------------------------------------------------------------------
-- S-Expression Type
--------------------------------------------------------------------------------

-- | S-Expression: the universal data format
--
-- Laws:
--   parse . print = id  (on valid SExprs)
--   print . parse = id  (on valid strings, modulo whitespace)
data SExpr
  = Atom String        -- ^ Leaf: identifier or string literal
  | List [SExpr]       -- ^ Compound: list of sub-expressions
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Parsing S-Expressions
--------------------------------------------------------------------------------

-- | Skip whitespace and comments (;; style)
skipWsAndComments :: String -> String
skipWsAndComments s = case dropWhile isSpace s of
  ';':';':rest -> skipWsAndComments (dropWhile (/= '\n') rest)
  s' -> s'

-- | Parse a single S-expression from a string
parseSExpr :: String -> Either String (SExpr, String)
parseSExpr s = case skipWsAndComments s of
  "" -> Left "Unexpected end of input"
  '(':rest -> parseList rest
  '"':rest -> parseString rest ""
  s' -> parseAtom s'

-- | Parse multiple S-expressions
parseSExprs :: String -> Either String [SExpr]
parseSExprs s = case skipWsAndComments s of
  "" -> Right []
  s' -> do
    (expr, rest) <- parseSExpr s'
    exprs <- parseSExprs rest
    Right (expr : exprs)

parseList :: String -> Either String (SExpr, String)
parseList s = go [] s
  where
    go acc str = case skipWsAndComments str of
      "" -> Left "Unexpected end of input in list"
      ')':rest -> Right (List (reverse acc), rest)
      str' -> do
        (expr, rest) <- parseSExpr str'
        go (expr : acc) rest

parseString :: String -> String -> Either String (SExpr, String)
parseString [] _ = Left "Unterminated string"
parseString ('"':rest) acc = Right (Atom (reverse acc), rest)
parseString ('\\':'"':rest) acc = parseString rest ('"':acc)
parseString ('\\':'n':rest) acc = parseString rest ('\n':acc)
parseString ('\\':'t':rest) acc = parseString rest ('\t':acc)
parseString ('\\':'\\':rest) acc = parseString rest ('\\':acc)
parseString (c:rest) acc = parseString rest (c:acc)

parseAtom :: String -> Either String (SExpr, String)
parseAtom s = 
  let (atom, rest) = span isAtomChar s
  in if null atom
     then Left $ "Expected atom at: " ++ take 20 s
     else Right (Atom atom, rest)
  where
    -- Extended character set for atoms - excludes () and whitespace
    -- but includes most operator characters
    isAtomChar c = isAlphaNum c || c `elem` "_.-:/<>*+?$@λΠΣ∀ᵢ=\\|~^!#%&',`[]{};→≅"

--------------------------------------------------------------------------------
-- Printing S-Expressions
--------------------------------------------------------------------------------

-- | Print a single S-expression
printSExpr :: SExpr -> String
printSExpr (Atom s)
  | needsQuotes s = "\"" ++ escapeString s ++ "\""
  | otherwise = s
printSExpr (List es) = "(" ++ unwords (map printSExpr es) ++ ")"

-- | Print multiple S-expressions with formatting
printSExprs :: [SExpr] -> String
printSExprs = unlines . map printSExpr

-- | Check if string needs quoting (contains spaces or special chars)
needsQuotes :: String -> Bool
needsQuotes [] = True
needsQuotes s = any (\c -> isSpace c || c `elem` "()\"\\") s

-- | Escape special characters in string
escapeString :: String -> String
escapeString = concatMap escape
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape '\n' = "\\n"
    escape '\t' = "\\t"
    escape c = [c]

--------------------------------------------------------------------------------
-- Grammar → S-Expression Conversion
--------------------------------------------------------------------------------

-- | Convert a single grammar expression to S-expression
grammarToSExpr :: GrammarExpr a -> SExpr
grammarToSExpr GEmpty = List [Atom "empty"]
grammarToSExpr (GLit s) = List [Atom "lit", Atom s]
grammarToSExpr (GRegex s) = List [Atom "regex", Atom s]
grammarToSExpr (GChar s) = List [Atom "char", Atom s]
grammarToSExpr (GRef s) = List [Atom "ref", Atom s]
grammarToSExpr (GSeq g1 g2) = 
  -- Flatten nested sequences
  let gs = flattenSeq g1 ++ flattenSeq g2
  in List (Atom "seq" : map grammarToSExpr gs)
grammarToSExpr (GAlt g1 g2) =
  -- Flatten nested alternatives
  let gs = flattenAlt g1 ++ flattenAlt g2
  in List (Atom "alt" : map grammarToSExpr gs)
grammarToSExpr (GStar g) = List [Atom "star", grammarToSExpr g]
grammarToSExpr (GRec x g) = List [Atom "rec", Atom x, grammarToSExpr g]
grammarToSExpr (GBind x g) = List [Atom "bind", Atom x, grammarToSExpr g]
grammarToSExpr (GCut g) = List [Atom "cut", grammarToSExpr g]
grammarToSExpr (GNode name gs) = 
  List (Atom "node" : Atom name : map grammarToSExpr gs)
grammarToSExpr GAny = List [Atom "any"]
grammarToSExpr _ = List [Atom "??"]  -- Fallback for unhandled cases

-- | Flatten nested sequences for cleaner output
flattenSeq :: GrammarExpr a -> [GrammarExpr a]
flattenSeq (GSeq g1 g2) = flattenSeq g1 ++ flattenSeq g2
flattenSeq g = [g]

-- | Flatten nested alternatives for cleaner output
flattenAlt :: GrammarExpr a -> [GrammarExpr a]
flattenAlt (GAlt g1 g2) = flattenAlt g1 ++ flattenAlt g2
flattenAlt g = [g]

-- | Convert a grammar map to S-expression
grammarMapToSExpr :: M.Map String (GrammarExpr a) -> SExpr
grammarMapToSExpr m = 
  List (Atom "grammar" : 
        [List [Atom "prod", Atom name, grammarToSExpr g] 
        | (name, g) <- M.toList m])

--------------------------------------------------------------------------------
-- S-Expression → Grammar Conversion
--------------------------------------------------------------------------------

-- | Parse a grammar expression from S-expression
sexprToGrammar :: SExpr -> Either String (GrammarExpr ())
sexprToGrammar (Atom s) = Right (GRef s)  -- Bare atom = reference
sexprToGrammar (List [Atom "empty"]) = Right GEmpty
sexprToGrammar (List [Atom "lit", Atom s]) = Right (GLit s)
sexprToGrammar (List [Atom "syntax", Atom s]) = Right (GLit s)  -- syntax is just lit
sexprToGrammar (List [Atom "keyword", Atom s]) = Right (GLit s)  -- keyword is just lit
sexprToGrammar (List [Atom "regex", Atom s]) = Right (GRegex s)
sexprToGrammar (List [Atom "char", Atom s]) = Right (GChar s)
sexprToGrammar (List [Atom "ref", Atom s]) = Right (GRef s)
sexprToGrammar (List (Atom "seq" : gs)) = do
  gs' <- mapM sexprToGrammar gs
  case gs' of
    [] -> Right GEmpty
    [g] -> Right g
    _ -> Right $ foldr1 GSeq gs'  -- foldr1 avoids trailing GEmpty
sexprToGrammar (List (Atom "alt" : gs)) = do
  gs' <- mapM sexprToGrammar gs
  case gs' of
    [] -> Right GEmpty
    [g] -> Right g
    _ -> Right $ foldr1 GAlt gs'
sexprToGrammar (List [Atom "star", g]) = do
  g' <- sexprToGrammar g
  Right (GStar g')
sexprToGrammar (List [Atom "rec", Atom x, g]) = do
  g' <- sexprToGrammar g
  Right (GRec x g')
sexprToGrammar (List [Atom "bind", Atom x, g]) = do
  g' <- sexprToGrammar g
  Right (GBind x g')
sexprToGrammar (List [Atom "cut", g]) = do
  g' <- sexprToGrammar g
  Right (GCut g')
sexprToGrammar (List (Atom "node" : Atom name : gs)) = do
  gs' <- mapM sexprToGrammar gs
  Right (GNode name gs')
sexprToGrammar (List [Atom "any"]) = Right GAny
sexprToGrammar e = Left $ "Invalid grammar S-expression: " ++ show e

-- | Parse a grammar map from S-expression
sexprToGrammarMap :: SExpr -> Either String (M.Map String (GrammarExpr ()))
sexprToGrammarMap (List (Atom "grammar" : prods)) = do
  pairs <- mapM parseProd prods
  Right $ M.fromList pairs
  where
    parseProd (List [Atom "prod", Atom name, g]) = do
      g' <- sexprToGrammar g
      Right (name, g')
    parseProd e = Left $ "Invalid production: " ++ show e
sexprToGrammarMap e = Left $ "Expected (grammar ...), got: " ++ show e

--------------------------------------------------------------------------------
-- File I/O
--------------------------------------------------------------------------------

-- | Read grammar map from .sexpr file
readSExprFile :: FilePath -> IO (Either String (M.Map String (GrammarExpr ())))
readSExprFile path = do
  content <- readFile path
  case parseSExpr content of
    Left err -> return $ Left $ "Parse error in " ++ path ++ ": " ++ err
    Right (sexpr, _) -> return $ sexprToGrammarMap sexpr

-- | Write grammar map to .sexpr file
writeSExprFile :: FilePath -> M.Map String (GrammarExpr a) -> IO ()
writeSExprFile path m = writeFile path (formatGrammarSExpr m)

-- | Format grammar S-expression with nice indentation
formatGrammarSExpr :: M.Map String (GrammarExpr a) -> String
formatGrammarSExpr m = unlines $
  ["(grammar"] ++
  [formatProd name g | (name, g) <- M.toList m] ++
  [")"]
  where
    formatProd name g = "  (prod " ++ show name ++ " " ++ printSExpr (grammarToSExpr g) ++ ")"
