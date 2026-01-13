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
    -- * Vocabulary Building
  , buildVocabFromGrammar
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
  , pattern GEmpty, pattern GLit, pattern GSyntax, pattern GNode
  , pattern GSeq, pattern GAlt, pattern GStar, pattern GRec, pattern GRef
  , pattern GBind, pattern GAny
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
-- Walks the grammar tree, collecting all GLit and GSyntax nodes.
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
  GSyntax s -> [s]
  GSeq g1 g2 -> collectLiterals g1 ++ collectLiterals g2
  GAlt g1 g2 -> collectLiterals g1 ++ collectLiterals g2
  GStar g' -> collectLiterals g'
  GRec _ g' -> collectLiterals g'
  GBind _ g' -> collectLiterals g'
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
      GSyntax s -> s
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
