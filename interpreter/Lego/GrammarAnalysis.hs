{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Grammar Analysis: Scanning and Production Naming
--
-- This module provides grammar analysis functions that work with
-- GrammarExpr from Lego.hs. It builds on Vocabulary.hs but adds
-- functions that require access to the grammar AST.
--
-- == Usage
--
-- @
--   import Lego (GrammarExpr, Lang(..))
--   import Lego.Vocabulary (Vocabulary, VarConvention(..))
--   import Lego.GrammarAnalysis
--   
--   -- Build vocabulary from a language's grammar
--   vocab = buildVocabFromGrammar "MyLang" LambdaStyle (langGrammar myLang)
--   
--   -- Check for naming issues
--   issues = checkProductionNaming (langGrammar myLang)
-- @
--
module Lego.GrammarAnalysis
  ( -- * Grammar Scanning
    scanGrammar
  , collectLiterals
  , collectKeywords
    -- * Vocabulary Building
  , buildVocabFromGrammar
    -- * Vocabulary Inference
  , InferredVocab(..)
  , inferVocab
  , inferCutPoints
  , CutPoint(..)
    -- * Auto-Cut Application
  , applyAutoCuts
  , applyAutoCutsToProduction
    -- * Production Analysis
  , scanProductions
  , checkProductionNaming
  , analyzeProduction
  , ProductionInfo(..)
  , NamingIssue(..)
  ) where

import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Lego
  ( GrammarExpr
  , pattern GEmpty, pattern GLit, pattern GNode
  , pattern GSeq, pattern GAlt, pattern GStar, pattern GRec, pattern GRef
  , pattern GBind, pattern GCut, pattern GAny
  )

import Lego.Vocabulary
  ( Vocabulary(..)
  , VarConvention(..)
  , ProductionInfo(..)
  , NamingIssue(..)
  , isSymbol
  , keywordContext
  )

--------------------------------------------------------------------------------
-- Grammar Scanning
--------------------------------------------------------------------------------

-- | Scan a grammar to extract vocabulary
--
-- Walks the grammar tree, collecting all GLit nodes.
-- Returns (symbols, keywords) where keywords are word-like literals.
scanGrammar :: Map String (GrammarExpr a) -> (Set String, Set String)
scanGrammar grammar = 
  let allLits = concatMap collectLiterals (M.elems grammar)
      (syms, kwds) = partition isSymbol allLits
  in (S.fromList syms, S.fromList kwds)

-- | Collect all literal strings from a grammar expression
collectLiterals :: GrammarExpr a -> [String]
collectLiterals g = case g of
  GLit s -> [s]
  GSeq g1 g2 -> collectLiterals g1 ++ collectLiterals g2
  GAlt g1 g2 -> collectLiterals g1 ++ collectLiterals g2
  GStar g' -> collectLiterals g'
  GRec _ g' -> collectLiterals g'
  GBind _ g' -> collectLiterals g'
  GCut g' -> collectLiterals g'  -- cut passes through
  GNode _ gs -> concatMap collectLiterals gs
  GEmpty -> []
  GRef _ -> []
  GAny -> []
  _ -> []  -- Catch any future extensions

--------------------------------------------------------------------------------
-- Vocabulary Building
--------------------------------------------------------------------------------

-- | Build a complete vocabulary from grammar analysis
buildVocabFromGrammar :: String -> VarConvention -> Map String (GrammarExpr a) -> Vocabulary
buildVocabFromGrammar name conv grammar =
  let (syms, kwds) = scanGrammar grammar
      kwdMap = M.fromList [(k, keywordContext k) | k <- S.toList kwds]
  in Vocabulary
    { vocabSymbols = syms
    , vocabKeywords = kwdMap
    , vocabConvention = conv
    , vocabSpecial = M.empty
    , vocabSource = name
    }

--------------------------------------------------------------------------------
-- Vocabulary Inference
--------------------------------------------------------------------------------

-- | Inferred vocabulary from grammar analysis
--
-- This is computed automatically by scanning the grammar for:
--   - GLit: literal matches
data InferredVocab = InferredVocab
  { ivKeywords   :: Set String  -- Reserved words
  , ivSymbols    :: Set String  -- Single-char operators and punctuation
  , ivLiterals   :: Set String  -- All literals (for lexer hints)
  , ivCutPoints  :: [CutPoint]  -- Where to auto-insert cuts
  } deriving (Show, Eq)

-- | A point where a cut should be inserted for better error recovery
data CutPoint = CutPoint
  { cpProduction :: String  -- Production name
  , cpKeyword    :: String  -- Keyword after which to cut
  , cpPosition   :: Int     -- Position in production (for multi-keyword prods)
  } deriving (Show, Eq)

-- | Infer vocabulary from grammar by scanning all productions
--
-- This replaces manual vocab: declarations in most cases.
-- The grammar itself declares what's reserved via GLit.
--
-- Keywords: alphabetic identifiers (if, while, let, rule, etc.)
-- Symbols: operators and punctuation (~>, ::=, +, etc.)
inferVocab :: Map String (GrammarExpr a) -> InferredVocab
inferVocab grammar = InferredVocab
  { ivKeywords  = S.fromList keywords
  , ivSymbols   = S.fromList symbolsOnly
  , ivLiterals  = S.fromList allLits
  , ivCutPoints = inferCutPoints grammar
  }
  where
    allLits = concatMap collectLiterals (M.elems grammar)
    keywords = concatMap collectKeywords (M.elems grammar)
    symbolsOnly = filter isSymbol allLits

-- | Collect keyword-like literals (alphabetic identifiers, not symbols)
-- Keywords are strings that look like identifiers (alphabetic chars + underscores)
collectKeywords :: GrammarExpr a -> [String]
collectKeywords = \case
  GLit s | isKeywordLike s -> [s]
  GSeq g1 g2 -> collectKeywords g1 ++ collectKeywords g2
  GAlt g1 g2 -> collectKeywords g1 ++ collectKeywords g2
  GStar g -> collectKeywords g
  GRec _ g -> collectKeywords g
  GBind _ g -> collectKeywords g
  GCut g -> collectKeywords g
  GNode _ gs -> concatMap collectKeywords gs
  _ -> []
  where
    isKeywordLike s = not (null s) && all isAlphaLike s
    isAlphaLike c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['_'] ++ ['0'..'9'])

-- | Infer where cuts should be inserted for error recovery
--
-- Strategy: A cut should follow any keyword that STARTS a production alternative.
-- This commits the parse after seeing the keyword, preventing backtracking.
--
-- Example:
--   ruleDecl ::= "rule" name ":" pattern "~>" template
--   After seeing "rule", we commit - if the rest fails, don't try other alts.
inferCutPoints :: Map String (GrammarExpr a) -> [CutPoint]
inferCutPoints grammar = 
  concatMap (uncurry findCutPoints) (M.toList grammar)

-- | Find cut points in a single production
findCutPoints :: String -> GrammarExpr a -> [CutPoint]
findCutPoints prodName = go 0
  where
    go pos g = case g of
      -- A literal at the start of a production is a cut point
      GLit kw | isKeywordLike kw -> [CutPoint prodName kw pos]
      
      -- Alternatives: find cut points in each branch
      GAlt g1 g2 -> go pos g1 ++ go pos g2
      
      -- Sequence: only look at the first element
      GSeq g1 _ -> go pos g1
      
      -- Recurse through structure
      GRec _ g' -> go pos g'
      GBind _ g' -> go pos g'
      
      -- Already has cut - don't duplicate
      GCut _ -> []
      
      _ -> []
    
    -- Keywords are alphabetic identifiers (not symbols)
    isKeywordLike s = not (null s) && all isAlphaLike s
    isAlphaLike c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

--------------------------------------------------------------------------------
-- Auto-Cut Application
--------------------------------------------------------------------------------

-- | Apply automatic cuts to all productions in a grammar
--
-- For each production-initial keyword, insert a cut after it.
-- This improves error recovery by committing after seeing the keyword.
--
-- Example transformation:
--   ruleDecl ::= "rule" name ":" pattern "~>" template
--   becomes:
--   ruleDecl ::= !"rule" name ":" pattern "~>" template
applyAutoCuts :: Map String (GrammarExpr a) -> Map String (GrammarExpr a)
applyAutoCuts grammar = M.map applyAutoCutsToProduction grammar

-- | Apply auto-cuts to a single production
--
-- Insert cuts after production-initial keywords (alphabetic literals).
applyAutoCutsToProduction :: GrammarExpr a -> GrammarExpr a
applyAutoCutsToProduction = go True
  where
    -- 'atStart' tracks whether we're at the start of a production/alternative
    go atStart g = case g of
      -- Keyword at start of production -> wrap in cut
      GLit kw | atStart && isKeywordLike kw -> GCut g
      
      -- Alternatives: apply to each branch (each alt is a "start")
      GAlt g1 g2 -> GAlt (go True g1) (go True g2)
      
      -- Sequence: first element is start, rest is not
      GSeq g1 g2 -> GSeq (go atStart g1) (go False g2)
      
      -- Recurse through structure, preserving start position
      GRec n g' -> GRec n (go atStart g')
      GBind n g' -> GBind n (go atStart g')
      GStar g' -> GStar (go False g')  -- Star contents not at start
      
      -- Already has cut - don't double-wrap
      GCut _ -> g
      
      -- Everything else passes through
      _ -> g
    
    isKeywordLike s = not (null s) && all isAlphaLike s
    isAlphaLike c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

--------------------------------------------------------------------------------
-- Production Naming Analysis
--------------------------------------------------------------------------------

-- | Scan productions to extract naming information
--
-- For each production, analyze its alternatives to derive constructor names.
-- A well-formed grammar should have clear constructor mappings.
scanProductions :: Map String (GrammarExpr a) -> [ProductionInfo]
scanProductions = map (uncurry analyzeProduction) . M.toList

-- | Analyze a single production
analyzeProduction :: String -> GrammarExpr a -> ProductionInfo
analyzeProduction name grammar = ProductionInfo
  { piName = name
  , piAlts = enumerateAlts grammar
  , piConstructor = deriveConstructor name grammar
  }
  where
    enumerateAlts g = zip [0..] (altNames g)
    
    altNames :: GrammarExpr a -> [String]
    altNames = \case
      GAlt g1 g2 -> altNames g1 ++ altNames g2
      g -> [suggestName g]
    
    suggestName :: GrammarExpr a -> String
    suggestName = \case
      GLit s -> s
      GNode n _ -> n
      GSeq g' _ -> suggestName g'
      GBind n _ -> n
      _ -> "<anonymous>"
    
    deriveConstructor :: String -> GrammarExpr a -> Maybe String
    deriveConstructor prodName g = case altNames g of
      [single] | single /= "<anonymous>" -> Just single
      _ -> Just (lastComponent prodName)
    
    lastComponent = reverse . takeWhile (/= '.') . reverse

-- | Check all productions for naming issues
checkProductionNaming :: Map String (GrammarExpr a) -> [NamingIssue]
checkProductionNaming grammar = 
  let prods = scanProductions grammar
      unnamed = [ UnnamedAlternative (piName p) i 
                | p <- prods
                , (i, n) <- piAlts p
                , n == "<anonymous>" 
                ]
      missing = [ MissingConstructor (piName p)
                | p <- prods
                , piConstructor p == Nothing
                ]
      -- Check for duplicate constructor names across different productions
      allConstrs = [ (c, piName p) 
                   | p <- prods
                   , Just c <- [piConstructor p]
                   ]
      grouped = M.toList $ M.fromListWith (++) [(c, [n]) | (c, n) <- allConstrs]
      dups = [ DuplicateName c ns | (c, ns) <- grouped, length ns > 1 ]
  in unnamed ++ missing ++ dups
