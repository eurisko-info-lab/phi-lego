{-# LANGUAGE LambdaCase #-}
-- | Vocabulary Analysis: Symbols, Keywords, and Identifiers
--
-- This module provides systematic classification of lexical elements,
-- supporting:
--   1. Grammar-driven tokenization (no hardcoded keywords)
--   2. Context-sensitive keywords (e.g., "rule" only at indent 0)
--   3. Variable convention modes (Prolog-style caps vs Lambda-style lowercase)
--   4. Pushout-aware vocabulary composition with conflict detection
--
-- == Philosophy
--
-- The vocabulary is DERIVED from the grammar, not predefined:
--   - Scan grammar to find all quoted literals
--   - Classify as Symbol (operators) vs Keyword (word-like)
--   - Track context sensitivity (top-level only vs anywhere)
--
-- == Variable Conventions
--
-- Different language traditions use different conventions:
--
-- @
--   Lambda:  lowercase = variable, Uppercase = constructor
--   Prolog:  Uppercase = variable, lowercase = atom
--   Haskell: lowercase = value/type var, Uppercase = constructor/type
-- @
--
-- We make this configurable per-language via 'VarConvention'.
--
module Lego.Vocabulary
  ( -- * Vocabulary Types
    Vocabulary(..)
  , emptyVocab
  , LexClass(..)
  , VarConvention(..)
  , ContextLevel(..)
    -- * Literal Classification
  , classifyLiteral
  , isSymbol
  , isKeywordLike
    -- * Vocabulary Operations
  , mergeVocab
  , poVocab
  , vocabConflicts
  , VocabConflict(..)
    -- * Context-sensitive Keywords
  , topLevelKeywords
  , sectionKeywords
  , anyLevelKeywords
  , keywordContext
    -- * Named Productions
  , ProductionInfo(..)
  , NamingIssue(..)
    -- * Regex Patterns
  , identPattern
  , varPattern
  , constrPattern
    -- * Building vocabulary from literal lists
  , buildVocabFromLiterals
  ) where

import Data.Char (isAlpha, isAlphaNum)
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Lexical Classification
--------------------------------------------------------------------------------

-- | Lexical class of a token
data LexClass
  = LCSymbol        -- ^ Operator/punctuation: +, ~>, ::=, (, )
  | LCKeyword       -- ^ Reserved word: rule, test, lang, import
  | LCIdent         -- ^ Identifier (not reserved)
  | LCVariable      -- ^ Variable (per convention: $x, X, x)
  | LCConstructor   -- ^ Constructor (per convention: Cons, cons, ~)
  | LCLiteral       -- ^ String/number literal
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Context level where a keyword is active
data ContextLevel
  = TopLevel        -- ^ Only at indent 0 (file declarations)
  | SectionLevel    -- ^ Inside a section (grammar:, rules:, etc.)
  | AnyLevel        -- ^ Anywhere in the file
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Variable naming convention
data VarConvention
  = LambdaStyle     -- ^ lowercase = var, Uppercase = constr (ML, Haskell values)
  | PrologStyle     -- ^ Uppercase = var, lowercase = atom (Prolog, Erlang)
  | PrefixStyle     -- ^ $x = var, others by context (Lego default)
  | MixedStyle      -- ^ Both conventions via different markers
  deriving (Eq, Ord, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Vocabulary
--------------------------------------------------------------------------------

-- | Complete vocabulary for a language
--
-- Derived from grammar scanning, used for tokenization and validation.
data Vocabulary = Vocabulary
  { vocabSymbols    :: Set String                 -- ^ Operator symbols
  , vocabKeywords   :: Map String ContextLevel    -- ^ Keywords with context
  , vocabConvention :: VarConvention              -- ^ Variable convention
  , vocabSpecial    :: Map String LexClass        -- ^ Special tokens (e.g., "~" as constr)
  , vocabSource     :: String                     -- ^ Source language name
  } deriving (Eq, Show)

emptyVocab :: Vocabulary
emptyVocab = Vocabulary S.empty M.empty PrefixStyle M.empty ""

--------------------------------------------------------------------------------
-- Literal Classification
--------------------------------------------------------------------------------

-- | Classify a quoted literal from grammar
--
-- Rules:
--   1. All-punctuation → Symbol
--   2. Starts with letter, all alphanumeric → Keyword candidate
--   3. Mixed → Symbol (unless special-cased)
--
-- Examples:
--   "~>"   → LCSymbol
--   "rule" → LCKeyword
--   "λ"    → LCSymbol (Unicode operator)
--   "λᵢ"   → LCSymbol (path abstraction)
--   "i0"   → LCKeyword (cubical endpoint)
--   "~"    → LCSymbol (but special as constructor in Cubical)
classifyLiteral :: String -> LexClass
classifyLiteral s
  | null s = LCLiteral
  | isKeywordLike s = LCKeyword
  | otherwise = LCSymbol

-- | Is this a symbol (operator/punctuation)?
isSymbol :: String -> Bool
isSymbol s = not (null s) && not (isKeywordLike s)

-- | Is this keyword-like (starts with letter, alphanumeric)?
isKeywordLike :: String -> Bool
isKeywordLike [] = False
isKeywordLike (c:cs) = isAlpha c && all isIdChar cs
  where isIdChar x = isAlphaNum x || x == '_' || x == '-' || x == '\''

--------------------------------------------------------------------------------
-- Building Vocabulary from Literals
--------------------------------------------------------------------------------

-- | Build vocabulary from a list of literals
--
-- This is the main entry point for vocabulary construction.
-- Grammar modules should extract their literals and call this.
buildVocabFromLiterals :: String -> VarConvention -> [String] -> Vocabulary
buildVocabFromLiterals name conv literals =
  let (syms, kwds) = partition isSymbol literals
      kwdMap = M.fromList [(k, keywordContext k) | k <- kwds]
  in Vocabulary
    { vocabSymbols = S.fromList syms
    , vocabKeywords = kwdMap
    , vocabConvention = conv
    , vocabSpecial = M.empty
    , vocabSource = name
    }

--------------------------------------------------------------------------------
-- Context-Sensitive Keywords
--------------------------------------------------------------------------------

-- | Top-level keywords (only valid at indent 0)
topLevelKeywords :: Set String
topLevelKeywords = S.fromList
  [ "lang", "import", "piece", "rule", "test", "def", "prelude", "code"
  ]

-- | Section keywords (valid inside language body)
sectionKeywords :: Set String
sectionKeywords = S.fromList
  [ "prelude", "code", "piece", "rule", "test", "def"
  ]

-- | Keywords valid anywhere
anyLevelKeywords :: Set String
anyLevelKeywords = S.fromList
  [ "when", "in", "let", "where", "case", "of", "if", "then", "else", "match"
  ]

-- | Determine context level for a keyword
keywordContext :: String -> ContextLevel
keywordContext kw
  | kw `S.member` topLevelKeywords = TopLevel
  | kw `S.member` sectionKeywords = SectionLevel
  | kw `S.member` anyLevelKeywords = AnyLevel
  | otherwise = AnyLevel  -- Default to anywhere

--------------------------------------------------------------------------------
-- Vocabulary Composition (Pushout)
--------------------------------------------------------------------------------

-- | Conflict when merging vocabularies
data VocabConflict
  = SymbolKeywordConflict String String String  -- ^ Same literal, different classes
  | ContextConflict String ContextLevel ContextLevel  -- ^ Same keyword, different contexts
  | ConventionConflict VarConvention VarConvention    -- ^ Incompatible var conventions
  | SpecialConflict String LexClass LexClass          -- ^ Same special, different classes
  deriving (Eq, Show)

-- | Detect conflicts between two vocabularies
vocabConflicts :: Vocabulary -> Vocabulary -> [VocabConflict]
vocabConflicts v1 v2 = concat
  [ symKwdConflicts
  , contextConflicts
  , conventionConflicts
  , specialConflicts
  ]
  where
    -- Symbol in one, keyword in other
    symKwdConflicts = 
      [ SymbolKeywordConflict s (vocabSource v1) (vocabSource v2)
      | s <- S.toList (vocabSymbols v1)
      , s `M.member` vocabKeywords v2
      ] ++
      [ SymbolKeywordConflict s (vocabSource v2) (vocabSource v1)
      | s <- S.toList (vocabSymbols v2)
      , s `M.member` vocabKeywords v1
      ]
    
    -- Same keyword, different context levels
    contextConflicts =
      [ ContextConflict k c1 c2
      | (k, c1) <- M.toList (vocabKeywords v1)
      , Just c2 <- [M.lookup k (vocabKeywords v2)]
      , c1 /= c2
      ]
    
    -- Incompatible variable conventions
    conventionConflicts
      | vocabConvention v1 /= vocabConvention v2 
      , vocabConvention v1 /= MixedStyle
      , vocabConvention v2 /= MixedStyle
      = [ConventionConflict (vocabConvention v1) (vocabConvention v2)]
      | otherwise = []
    
    -- Same special token, different classes
    specialConflicts =
      [ SpecialConflict k c1 c2
      | (k, c1) <- M.toList (vocabSpecial v1)
      , Just c2 <- [M.lookup k (vocabSpecial v2)]
      , c1 /= c2
      ]

-- | Merge vocabularies (simple union, ignoring conflicts)
mergeVocab :: Vocabulary -> Vocabulary -> Vocabulary
mergeVocab v1 v2 = Vocabulary
  { vocabSymbols = S.union (vocabSymbols v1) (vocabSymbols v2)
  , vocabKeywords = M.union (vocabKeywords v1) (vocabKeywords v2)
  , vocabConvention = mergeConvention (vocabConvention v1) (vocabConvention v2)
  , vocabSpecial = M.union (vocabSpecial v1) (vocabSpecial v2)
  , vocabSource = vocabSource v1 ++ "_" ++ vocabSource v2
  }
  where
    mergeConvention c1 c2
      | c1 == c2 = c1
      | otherwise = MixedStyle

-- | Pushout of vocabularies WITH conflict detection
--
-- Returns (merged, conflicts). Caller should handle conflicts appropriately.
poVocab :: Vocabulary -> Vocabulary -> (Vocabulary, [VocabConflict])
poVocab v1 v2 = (mergeVocab v1 v2, vocabConflicts v1 v2)

--------------------------------------------------------------------------------
-- Production Naming Analysis
--------------------------------------------------------------------------------

-- | Information about a grammar production
data ProductionInfo = ProductionInfo
  { piName        :: String           -- ^ Production name (e.g., "Term.term")
  , piAlts        :: [(Int, String)]  -- ^ (index, suggested name) for each alternative
  , piConstructor :: Maybe String     -- ^ Derived constructor name (if unambiguous)
  } deriving (Eq, Show)

-- | Issues with production naming
data NamingIssue
  = UnnamedAlternative String Int     -- ^ Production has unnamed alt at index
  | AmbiguousConstructor String [String]  -- ^ Multiple possible constructor names
  | MissingConstructor String         -- ^ No constructor derivable
  | DuplicateName String [String]     -- ^ Same name used in multiple places
  deriving (Eq, Show)

-- NOTE: Grammar scanning functions (scanProductions, checkProductionNaming)
-- are provided in Lego.GrammarAnalysis module which can import from Lego.hs
-- to access the GrammarExpr type and pattern synonyms.

--------------------------------------------------------------------------------
-- Regex Patterns for Variable Conventions
--------------------------------------------------------------------------------

-- | Regex pattern for general identifiers
--
-- Matches: letter followed by alphanumeric, _, -, '
identPattern :: String
identPattern = "[a-zA-Z][a-zA-Z0-9_\\-']*"

-- | Regex pattern for variables (depends on convention)
varPattern :: VarConvention -> String
varPattern = \case
  LambdaStyle -> "[a-z][a-zA-Z0-9_']*"       -- lowercase start
  PrologStyle -> "[A-Z][a-zA-Z0-9_']*"       -- uppercase start
  PrefixStyle -> "\\$[a-zA-Z][a-zA-Z0-9_']*" -- $ prefix
  MixedStyle  -> "\\$?[a-zA-Z][a-zA-Z0-9_']*" -- optional $

-- | Regex pattern for constructors (depends on convention)
constrPattern :: VarConvention -> String
constrPattern = \case
  LambdaStyle -> "[A-Z][a-zA-Z0-9_']*"       -- uppercase start
  PrologStyle -> "[a-z][a-zA-Z0-9_']*"       -- lowercase start
  PrefixStyle -> "[a-zA-Z][a-zA-Z0-9_']*"    -- any ident without $
  MixedStyle  -> "[a-zA-Z~][a-zA-Z0-9_']*"   -- includes ~ for Cubical
