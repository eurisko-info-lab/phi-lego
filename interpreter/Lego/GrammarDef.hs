{-# LANGUAGE PatternSynonyms #-}
-- | Grammar Definitions loaded from Grammar.sexpr
--
-- This module provides the Lego grammar loaded from the portable
-- Grammar.sexpr file. The .sexpr file is the source of truth.
--
-- == Bootstrap
--
-- Grammar.sexpr is generated from Grammar.lego using:
--   cabal run gen-grammar-def -- lego/prelude/lego/Grammar.lego > Grammar.sexpr
--
-- == Usage
--
-- @
-- import Lego.GrammarDef (legoGrammar)
-- 
-- -- Full grammar definitions
-- case M.lookup "Term.term" legoGrammar of ...
-- @
--
module Lego.GrammarDef
  ( -- * Complete Grammar
    legoGrammar
    -- * Subsets (filtered from legoGrammar)
  , termGrammar
  , atomGrammar
  ) where

import Lego (GrammarExpr)
import Lego.SExpr (readSExprFile)
import qualified Data.Map as M
import System.IO.Unsafe (unsafePerformIO)
import System.Directory (doesFileExist)

--------------------------------------------------------------------------------
-- Grammar Loading
--------------------------------------------------------------------------------

-- | Known locations for Grammar.sexpr (searched in order)
grammarSExprPaths :: [FilePath]
grammarSExprPaths = 
  [ "lego/prelude/lego/Grammar.sexpr"          -- from workspace root
  , "prelude/lego/Grammar.sexpr"               -- from lego/
  , "../prelude/lego/Grammar.sexpr"            -- from lego/interpreter/
  ]

-- | Load grammar from first available .sexpr file
{-# NOINLINE loadGrammarFromSExpr #-}
loadGrammarFromSExpr :: M.Map String (GrammarExpr ())
loadGrammarFromSExpr = unsafePerformIO $ tryLoad grammarSExprPaths
  where
    tryLoad [] = error $ "Grammar.sexpr not found in: " ++ show grammarSExprPaths
    tryLoad (p:ps) = do
      exists <- doesFileExist p
      if exists
        then do
          result <- readSExprFile p
          case result of
            Right g | M.size g > 0 -> return g
            Right _ -> tryLoad ps
            Left err -> error $ "Failed to parse " ++ p ++ ": " ++ err
        else tryLoad ps

--------------------------------------------------------------------------------
-- Exported Grammars
--------------------------------------------------------------------------------

-- | Complete Lego grammar (all productions)
legoGrammar :: M.Map String (GrammarExpr ())
legoGrammar = loadGrammarFromSExpr

-- | Term grammar (Term.* and Atom.* productions)
termGrammar :: M.Map String (GrammarExpr ())
termGrammar = M.filterWithKey (\k _ -> "Term." `isPrefixOf` k) legoGrammar
  where isPrefixOf p s = take (length p) s == p

-- | Atom grammar (Atom.* productions)  
atomGrammar :: M.Map String (GrammarExpr ())
atomGrammar = M.filterWithKey (\k _ -> "Atom." `isPrefixOf` k) legoGrammar
  where isPrefixOf p s = take (length p) s == p
