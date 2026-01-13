{-# LANGUAGE LambdaCase #-}
-- | Lego Tokenizer: Token type and tokenization
--
-- This module is separate from Parser to avoid circular imports:
-- both Parser.hs and GrammarParser.hs need tokens.
--
-- == Token Classification
--
-- Tokens are classified into categories based on lexical structure:
--   - TIdent: identifiers (start with letter, alphanumeric/underscore/dash/quote)
--   - TKeyword: context-sensitive keywords (word-like, reserved at certain indent levels)
--   - TSym: symbols (operators, punctuation, Unicode)
--   - TString: quoted strings
--   - TNewline/TIndent: whitespace structure
--
-- == Context-Sensitive Keywords
--
-- Keywords like "rule", "piece", "test" are only keywords at top-level (indent 0).
-- Inside expressions they are treated as regular identifiers.
-- This allows: "rule" as keyword in "rule foo:", but identifier in "(rule x)".
--
-- == Variable Conventions
--
-- The tokenizer is convention-agnostic. Variable classification happens later:
--   - PrefixStyle (default): $x is variable, x is ident/constructor
--   - LambdaStyle: lowercase = var, Uppercase = constructor
--   - PrologStyle: Uppercase = var, lowercase = atom
--
module Lego.Token
  ( -- * Token Type
    Token(..)
  , TokenInfo(..)
    -- * Tokenization
  , tokenize
  , tokenizeWithInfo
  , tokenizeWithKeywords
  , tokenizeWithSymbols
  , classifyKeywords
  , classifyReserved
    -- * Vocabulary (for external use - DEPRECATED for composed languages)
  , keywords
  , legoKeywords
  , topLevelKeywords
  , sectionKeywords
  , exprKeywords
  , symbols
  , cubicalSymbols
  , linearSymbols
    -- * Token predicates (for .lego files only)
  , isKeywordAt
  , isTopLevelKeyword
  ) where

import Data.Char (isAlphaNum, isAlpha, isSpace, isDigit)
import Data.List (isPrefixOf)
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Token Type
--------------------------------------------------------------------------------

-- | Token: TWO-LAYER design for pushout-friendly tokenization
--
-- Layer 1: Atoms (universal, no reservation)
--   - TIdent: word-like lexemes (no keyword classification yet)
--   - TSym: operator-like lexemes
--   - TString, TNewline, TIndent: structural
--
-- Layer 2: Refined tokens (grammar-scoped)
--   - TKeyword: refined by grammar piece (context-dependent)
--   - Refinement happens DURING grammar execution, not during lexing
--
-- Key insight: Lexer produces atoms. Grammar refines atoms into keywords.
-- This makes tokenization parametric over vocabulary (enabling pushout).
data Token
  = TIdent String    -- ^ Atom: identifier (no classification yet)
  | TString String   -- ^ Atom: string literal: "..."
  | TRegex String    -- ^ Atom: regex literal: /.../
  | TReserved String -- ^ Atom: reserved literal: `...` (used in .lego grammars)
  | TChar String     -- ^ Atom: character literal: '...'
  | TSym String      -- ^ Atom: symbol/operator
  | TKeyword String  -- ^ Refined: keyword (grammar-scoped, not lexer-classified)
  | TNewline         -- ^ Structure: significant newline
  | TIndent Int      -- ^ Structure: indentation level (spaces after newline)
  deriving (Eq, Show)

-- | Extended token info for error reporting
data TokenInfo = TokenInfo
  { tiToken  :: Token
  , tiLine   :: Int
  , tiColumn :: Int
  , tiIndent :: Int    -- ^ Current indentation context
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Vocabulary: Keywords
--------------------------------------------------------------------------------

-- | Vocabulary: Keywords (DEPRECATED - for backward compatibility only)
--
-- WARNING: These global keyword lists violate compositionality.
-- They are kept for existing .lego file parsing but should NOT be used
-- for composed languages (like redtt).
--
-- New approach: Keywords are grammar-scoped, refined during parse.
-- See GrammarInterp's token refinement for the compositional approach.

-- | All keywords (union of all contexts)
keywords :: [String]
keywords = legoKeywords

-- | Lego meta-language keywords (only for .lego files)
legoKeywords :: [String]
legoKeywords =
  -- Top-level declarations (indent 0)
  [ "lang"      -- language definition
  , "import"    -- import declaration
  , "piece"     -- piece (grammar fragment)
  , "rule"      -- rewrite rule
  , "test"      -- test declaration
  , "def"       -- definition
  -- Sections (any indent)
  , "code"
  , "prelude"
  -- Expression keywords (any indent)
  , "when", "in", "let", "where", "case", "of", "if", "then", "else", "match"
  ]

-- DEPRECATED: Split keyword lists (kept for isKeywordAt)
topLevelKeywords :: [String]
topLevelKeywords = 
  [ "lang", "import", "piece", "rule", "test", "def" ]

sectionKeywords :: [String]
sectionKeywords =
  [ "code", "prelude"
  ]

exprKeywords :: [String]
exprKeywords =
  [ "when", "in", "let", "where", "case", "of", "if", "then", "else", "match"
  ]

-- NOTE: Cubical keywords removed from global list
-- They should be grammar-scoped (redtt, cubical pieces define them)

--------------------------------------------------------------------------------
-- Vocabulary: Symbols
--------------------------------------------------------------------------------

-- | All symbols (union of all categories)
-- Note: longer symbols must come before shorter ones for correct matching
symbols :: [String]
symbols = coreSymbols ++ arrowSymbols ++ cubicalSymbols ++ linearSymbols ++ greekSymbols

-- | Core symbols (always available)
coreSymbols :: [String]
coreSymbols =
  [ "::=", ":="          -- definition/assignment
  , "(", ")", "[", "]", "{", "}"  -- brackets
  , ":", ".", ",", ";"   -- punctuation
  , "$"                  -- metavariable prefix
  , "<", ">"             -- angle brackets (also for comparisons)
  , "=", "===", "!="     -- equality
  , "|", "*", "+", "-"   -- operators
  , "@"                  -- application (cubical path apply)
  , "\\"                 -- lambda (ASCII)
  ]

-- | Arrow symbols for rules and types
arrowSymbols :: [String]
arrowSymbols =
  [ "<~~>"               -- bidirectional test (both directions)
  , "!!!>"               -- expect error test
  , "<~>"                -- bidirectional rule
  , "~~>"                -- test arrow (parse then eval)
  , "=!>"                -- expect no change test
  , "<~"                 -- backward rule
  , "~>"                 -- forward rule
  , "->"                 -- function type (ASCII)
  , "=>"                 -- implication/match arrow
  , "→"                  -- function type (Unicode)
  , "←"                  -- reverse arrow
  , "↦"                  -- mapsto
  , "⇒"                  -- double arrow
  , "↔"                  -- bidirectional
  ]

-- | Cubical type theory symbols
cubicalSymbols :: [String]
cubicalSymbols =
  [ "λᵢ"                 -- path abstraction
  , "∧", "∨"             -- interval meet/join
  , "~"                  -- interval reversal (also negation)
  , "∙"                  -- path composition
  ]

-- | Linear type theory symbols
linearSymbols :: [String]
linearSymbols =
  [ "·"                  -- multiplication
  , "⊸"                  -- linear arrow (lollipop)
  , "⊗"                  -- tensor product
  , "&"                  -- with (additive conjunction)
  , "⊕"                  -- additive disjunction
  , "!"                  -- bang (exponential)
  , "★"                  -- star (unrestricted)
  ]

-- | Greek and mathematical symbols
greekSymbols :: [String]
greekSymbols =
  [ "λ"                  -- lambda
  , "Π", "Σ"             -- dependent types
  , "∀", "∃"             -- quantifiers
  , "μ"                  -- fixed point
  , "ε"                  -- empty
  , "¬"                  -- negation
  , "⊔"                  -- pushout/join
  , "<>"                 -- diamond (modal)
  , "⟨", "⟩"             -- angle brackets (Unicode)
  , "∘"                  -- composition
  , "⊛"                  -- circled asterisk
  , ":<"                 -- subtype
  , "⁻¹"                 -- inverse (superscript -1, HoTT path inverse)
  , "≃"                  -- equivalence (HoTT)
  -- Redtt/cubical symbols
  , "×"                  -- sigma/product type
  , "∂"                  -- boundary (as in ∂[i])
  , "𝕀"                  -- interval type
  , "⊢"                  -- turnstile (context judgment)
  , "^"                  -- universe levels (type^1)
  , "/"                  -- slash (for recursive binders)
  , "#"                  -- hash (for primitives)
  , "?"                  -- hole/metavariable
  ]

--------------------------------------------------------------------------------
-- Context-Sensitive Keyword Checking
--------------------------------------------------------------------------------

-- | Set of top-level keywords for fast lookup
topLevelKeywordSet :: S.Set String
topLevelKeywordSet = S.fromList topLevelKeywords

-- | Set of all keywords for fast lookup
allKeywordSet :: S.Set String
allKeywordSet = S.fromList (sectionKeywords ++ exprKeywords)

-- | Check if a word is a Lego meta-language keyword at the given indentation level
--
-- ONLY FOR .lego FILES. Composed languages should NOT use this.
-- Top-level keywords (lang, rule, test, etc.) are only keywords at indent 0.
-- Other keywords are reserved everywhere.
isKeywordAt :: Int -> String -> Bool
isKeywordAt indent word
  | word `S.member` topLevelKeywordSet = indent == 0
  | word `S.member` allKeywordSet = True
  | otherwise = False

-- | Check if a word is a top-level-only keyword
isTopLevelKeyword :: String -> Bool
isTopLevelKeyword = (`S.member` topLevelKeywordSet)

--------------------------------------------------------------------------------
-- Tokenization
--------------------------------------------------------------------------------

-- | Tokenize: Layer 1 (universal atoms, no keyword classification)
--
-- This lexer produces ATOMS, not refined tokens:
--   - All word-like lexemes become TIdent (no TKeyword yet)
--   - Keyword refinement happens in grammar (layer 2)
--
-- For .lego files: isKeywordAt is used for backward compatibility
-- For composed languages: ALL identifiers stay as TIdent (grammar refines them)
tokenize :: String -> [Token]
tokenize = tokenizeWithKeywords True

-- | Tokenize with optional keyword classification (for migration)
tokenizeWithKeywords :: Bool -> String -> [Token]
tokenizeWithKeywords doClassify = tokenizeWithSymbolList doClassify symbols

-- | Tokenize using an explicit symbol list (for composed languages).
--
-- This keeps the lexer "atom-first" (no keyword classification), while allowing
-- callers to supply a symbol vocabulary so multi-character operators are
-- tokenized correctly.
tokenizeWithSymbols :: [String] -> String -> [Token]
tokenizeWithSymbols = tokenizeWithSymbolList False

-- | Internal: tokenize with an explicit symbol list and optional .lego keyword classification.
tokenizeWithSymbolList :: Bool -> [String] -> String -> [Token]
tokenizeWithSymbolList doClassify symbolList input =
  go 0 0 input
  where
    go _ _ [] = []
    go _col _ind ('\n':cs) = TNewline : goIndent 0 cs
    go col ind (c:cs) | isSpace c = go (col+1) ind cs
    -- RedTT/OCaml-style block comments: /- ... -/
    -- We treat them as whitespace and skip entirely.
    go col ind ('/':'-':cs) =
      let rest = dropBlockComment cs
      in go (col + 2) ind rest
    -- Backticks have two distinct meanings:
    --   - In `.lego` files (doClassify=True), they delimit reserved literals: `foo`.
    --   - In RedTT surface syntax, backtick is a standalone token used for quotation.
    -- For composed languages we must NOT treat backticks as a delimiter.
    go col ind ('`':cs)
      | doClassify =
          let (s, rest) = span (/= '`') cs
          in TReserved s : go (col + length s + 2) ind (drop 1 rest)
      | otherwise = TSym "`" : go (col + 1) ind cs
    go col ind ('"':cs) = let (s, rest) = span (/= '"') cs
                          in TString s : go (col + length s + 2) ind (drop 1 rest)
    -- Single quotes only interpreted as char delimiters in .lego files (doClassify=True)
    -- In RedTT and other surface languages, ' is often part of identifiers (primes)
    go col ind ('\'':cs)
      | doClassify =
          let (s, rest) = span (/= '\'') cs
          in TChar s : go (col + length s + 2) ind (drop 1 rest)
      | otherwise = TSym "'" : go (col + 1) ind cs
    -- Slash: never tokenize as regex delimiter. / is used in qualified names (RedTT)
    -- and as operators in .lego files. Regex support can be added via grammar if needed.
    go col ind ('-':'-':cs) = go col ind (dropWhile (/= '\n') cs)  -- comment
    go col ind ('$':cs) = let (ident, rest) = span isIdChar cs
                          in TSym "$" : (if null ident then id else (TIdent ident :)) (go (col + length ident + 1) ind rest)
    go col ind cs | Just (sym, rest) <- matchSym cs = TSym sym : go (col + length sym) ind rest
    go col ind cs@(c:_) | isAlpha c || c == '_' =
      let (ident, rest) = span isIdChar cs
          -- Only classify keywords for .lego files (backward compat)
          tok = if doClassify && isKeywordAt ind ident 
                then TKeyword ident 
                else TIdent ident
      in tok : go (col + length ident) ind rest
    go col ind cs@(c:_) | isDigit c =
      let (num, rest) = span isDigit cs
      in TIdent num : go (col + length num) ind rest
    -- Fallback: preserve any other non-space character as a single-character symbol.
    -- This avoids silently dropping unseen Unicode operators.
    go col ind (c:cs) = TSym [c] : go (col+1) ind cs

    dropBlockComment [] = []
    dropBlockComment ('-':'/':rest) = rest
    dropBlockComment (_:rest) = dropBlockComment rest
    
    goIndent n (' ':cs) = goIndent (n+1) cs
    goIndent n cs = TIndent n : go n n cs  -- Update indent context
    
    -- Identifier characters: alphanumeric, underscore, hyphen, apostrophe,
    -- plus some Unicode symbols that redtt allows in identifiers:
    --   ∘ (composition)
    -- Note: / and → are NOT included because they have syntactic meaning
    -- (path separator and function arrow). Identifiers like iso/refl and
    -- biinv-equiv→iso are handled by qualident in the grammar.
    isIdChar c = isAlphaNum c || c == '_' || c == '-' || c == '\'' 
                 || c == '∘'
    
    -- Match longest symbol first
    matchSym cs = foldr (\s acc -> if s `isPrefixOf` cs then Just (s, drop (length s) cs) else acc) Nothing sortedSymbols
    sortedSymbols = reverse $ sortBy (compare `on` length) symbolList
    sortBy cmp = foldr (insertBy cmp) []
    insertBy _ x [] = [x]
    insertBy cmp x (y:ys) = case cmp x y of
      GT -> y : insertBy cmp x ys
      _  -> x : y : ys
    on f g x y = f (g x) (g y)

-- | Tokenize with full location information
tokenizeWithInfo :: String -> [TokenInfo]
tokenizeWithInfo = go 1 1 0  -- (line, column, indent)
  where
    go _ _ _ [] = []
    go ln _col ind ('\n':cs) = 
      TokenInfo TNewline ln _col ind : goIndent (ln+1) 1 cs
    go ln col ind (c:cs) | isSpace c = go ln (col+1) ind cs
    -- RedTT/OCaml-style block comments: /- ... -/
    go ln col ind ('/':'-':cs) =
      let rest = dropBlockComment cs
      in go ln (col + 2) ind rest
    go ln col ind ('`':cs) =
      let (s, rest) = span (/= '`') cs
      in TokenInfo (TReserved s) ln col ind : go ln (col + length s + 2) ind (drop 1 rest)
    go ln col ind ('"':cs) = 
      let (s, rest) = span (/= '"') cs
      in TokenInfo (TString s) ln col ind : go ln (col + length s + 2) ind (drop 1 rest)
    go ln col ind ('-':'-':cs) = go ln col ind (dropWhile (/= '\n') cs)
    go ln col ind ('$':cs) = 
      let (ident, rest) = span isIdChar cs
          toks = TokenInfo (TSym "$") ln col ind : 
                 if null ident then [] else [TokenInfo (TIdent ident) ln (col+1) ind]
      in toks ++ go ln (col + length ident + 1) ind rest
    go ln col ind cs | Just (sym, rest) <- matchSym cs = 
      TokenInfo (TSym sym) ln col ind : go ln (col + length sym) ind rest
    go ln col ind cs@(c:_) | isAlpha c || c == '_' =
      let (ident, rest) = span isIdChar cs
          tok = if isKeywordAt ind ident then TKeyword ident else TIdent ident
      in TokenInfo tok ln col ind : go ln (col + length ident) ind rest
    go ln col ind cs@(c:_) | isDigit c =
      let (num, rest) = span isDigit cs
      in TokenInfo (TIdent num) ln col ind : go ln (col + length num) ind rest
    -- Preserve any other character as a single-character symbol.
    go ln col ind (c:cs) = TokenInfo (TSym [c]) ln col ind : go ln (col+1) ind cs

    dropBlockComment [] = []
    dropBlockComment ('-':'/':rest) = rest
    dropBlockComment (_:rest) = dropBlockComment rest
    
    goIndent ln n (' ':cs) = goIndent ln (n+1) cs
    goIndent ln n cs = TokenInfo (TIndent n) ln 1 n : go ln n n cs
    
    -- Identifier characters: alphanumeric, underscore, hyphen, apostrophe,
    -- plus some Unicode symbols that redtt allows in identifiers:
    --   ∘ (composition)
    -- Note: / and → are NOT included because they have syntactic meaning
    isIdChar c = isAlphaNum c || c == '_' || c == '-' || c == '\''
                 || c == '∘'
    matchSym cs = foldr (\s acc -> if s `isPrefixOf` cs then Just (s, drop (length s) cs) else acc) Nothing sortedSymbols
    sortedSymbols = reverse $ sortBy (compare `on` length) symbols
    sortBy cmp = foldr (insertBy cmp) []
    insertBy _ x [] = [x]
    insertBy cmp x (y:ys) = case cmp x y of GT -> y : insertBy cmp x ys; _ -> x : y : ys
    on f g x y = f (g x) (g y)
-- | Classify TIdent tokens as TKeyword based on a keyword set
-- This allows grammar-driven keyword classification (compositional)
classifyKeywords :: S.Set String -> [Token] -> [Token]
classifyKeywords kws = map classify
  where
    classify (TIdent s) | S.member s kws = TKeyword s
    classify t = t

-- | Classify TIdent tokens as TReserved based on a reserved set.
--
-- Reserved words are the ones that <ident> should never match (Phase 2), so we
-- keep this distinct from soft keyword classification.
classifyReserved :: S.Set String -> [Token] -> [Token]
classifyReserved reserved = map classify
  where
    classify (TIdent s) | S.member s reserved = TReserved s
    classify t = t