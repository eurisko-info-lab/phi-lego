{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Grammar Interpreter: Bidirectional parsing/printing from grammar definitions
--
-- This module interprets Lego grammar definitions for:
--   - Parse: tokens → AST
--   - Print: AST → tokens
--   - Check: validation
--
-- == Architecture
--
-- Grammar is treated as an EXPRESSION (data), not a procedure (code).
-- The same GrammarExpr drives all three modes via modal interpretation.
--
-- @
--                   ┌─────────────────┐
--   tokens ──Parse──►│   GrammarExpr   │──Print──► tokens
--                   │  (bidirectional) │
--   AST ◄───────────│                 │◄──────── AST
--                   └─────────────────┘
-- @
--
-- == Algebraic Foundation
--
-- GrammarExpr forms a semiring:
--   (+) = GAlt  (alternation, coproduct)
--   (*) = GSeq  (sequence, monoidal)
--   0   = empty Alt (failure)
--   1   = GEmpty (success, unit)
--
-- Kleene star: GStar g = μX. (g · X) + 1
--
module Lego.GrammarInterp
  ( -- * Grammar Loading
    loadGrammarDefs
  , GrammarDefs(..)
  , extractKeywords
  , extractSymbols
  , extractAllKeywords
  , extractAllSymbols
    -- * Parsing (Grammar → Parser)
  , parseWith
  , parseProduction
    -- * Printing (Grammar → Printer)
  , printWith
  , printProduction
    -- * Bidirectional (unified)
  , Mode(..)
  , BiState(..)
  , runGrammar
    -- * Convenience parsing
  , parseTerm
  , termGrammarDefs
  ) where

import Lego (GrammarExpr, pattern GEmpty, pattern GLit, pattern GRegex, pattern GChar, pattern GNode,
             pattern GSeq, pattern GAlt, pattern GStar, pattern GRec, pattern GRef,
             pattern GBind, pattern GCut, pattern GVar, pattern GAny,
             Term, pattern TmVar, pattern TmCon, pattern TmLit, pattern TmRegex, pattern TmChar,
             Rule(..), LegoDecl(..), Mode(..), BiState(..),
             lookupBind, insertBind, pushScope, popScope, flattenBinds)
import Lego.Token (Token(..), tokenize)
import Lego.GrammarDef (termGrammar, atomGrammar)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, maybeToList)
import Data.Char (isAlphaNum, isDigit, isLetter, generalCategory, GeneralCategory(..))
import Data.List (minimumBy, intercalate)
import Data.Ord (comparing)
import Control.Monad (guard)

-- | Check if all characters are digits
isDigitChar :: Char -> Bool
isDigitChar = isDigit

-- | Check if string is a symbol (not alphanumeric identifier)
-- Symbols are things like ~, ∧, ∨, @, λᵢ, etc.
isSymbol :: String -> Bool
isSymbol [] = False
isSymbol (c:_) = not (isAlphaNum c) && c /= '_'

-- | Check if a symbol can be used as an identifier (e.g., node names)
-- Valid identifier-like symbols:
--   - Greek letters: λ, Π, Σ, λᵢ, μ, etc.
--   - Math symbols used as type names: ∀, ∃, etc.
-- Invalid (structural): (, ), [, ], {, }, <, >, →, ×, etc.
-- Note: ? and . are NOT identifier-like; they are punctuation/operators.
-- Note: < and > are NOT identifier-like; they're used for <ident> syntax.
-- Note: → and ← are NOT identifier-like; they're used for arrows in patterns/types.
-- Note: × is NOT identifier-like; it's used for sigma/product types.
isIdentLikeSym :: String -> Bool
isIdentLikeSym [] = False
isIdentLikeSym s@(c:_) = isNodeNameChar c && s `notElem` structuralSymbols
  where
    -- Accept letters (including Greek) and math symbols (∀, ∃, ⊗, ⊕, ⊛)
    -- EXCEPT < and > which are grammar delimiters for <ident> syntax
    -- EXCEPT → and ← which are arrow operators
    -- EXCEPT × which is the sigma/product type operator
    isNodeNameChar ch = (isLetter ch || isMathSymbol ch) && ch `notElem` "<>→←×"
    isMathSymbol ch = generalCategory ch == MathSymbol
    structuralSymbols = ["(", ")", "[", "]", "{", "}", ",", ";", ":", "::=", "|", "*", "+", "~>", "<~", "<~>", "~~>", "==>", "<", ">", "=", "?", "→", "←", "×"]


-- | Check if symbol is an infix operator (not parentheses or other structural symbols)
-- Used for parsing infix binary patterns like (arg1 · arg2)
isInfixOp :: String -> Bool
isInfixOp s = isSymbol s && s `notElem` ["(", ")", "[", "]", "{", "}", ",", ";", ":", "~>", "<~", "<~>", "~~>"]

--------------------------------------------------------------------------------
-- Token/Term Extraction Helpers
--------------------------------------------------------------------------------

-- | Extract token name from various token types
getTokenName :: Token -> Maybe String
getTokenName (TIdent s) = Just s
getTokenName (TKeyword s) = Just s
getTokenName (TReserved s) = Just s
getTokenName _ = Nothing

-- | Extract token name but exclude reserved words
-- Used for <identifier> which rejects TReserved
getIdentName :: Token -> Maybe String
getIdentName (TIdent s) = Just s
getIdentName (TKeyword s) = Just s
getIdentName _ = Nothing

-- | Extract constructor name from token (TIdent, TKeyword, or TSym with constraints)
-- Excludes structural symbols that aren't valid constructor names
getConstrName :: Token -> Maybe String
getConstrName (TIdent s) = Just s
getConstrName (TKeyword s) = Just s
getConstrName (TSym s) | s `notElem` ["(", ")", "$"] = Just s
getConstrName _ = Nothing

-- | Helper for Print mode: pattern match on bsTerm and emit tokens
-- Takes a function that extracts tokens from the term, returns updated state or empty list
printSimple :: (Term -> Maybe [Token]) -> BiState Token Term -> [BiState Token Term]
printSimple f st = case bsTerm st of
  Just term | Just toks <- f term ->
    [st { bsTokens = bsTokens st ++ toks, bsTerm = Nothing }]
  _ -> []

--------------------------------------------------------------------------------
-- Grammar Definitions
--------------------------------------------------------------------------------

-- | Collection of grammar definitions from a .lego file
data GrammarDefs = GrammarDefs
  { gdKeywords    :: S.Set String           -- vocabulary keywords
  , gdSymbols     :: S.Set String           -- vocabulary symbols
  , gdProductions :: M.Map String (GrammarExpr ())  -- name → grammar
  , gdRules       :: [Rule]                 -- semantic rules
  } deriving (Show)

emptyGrammarDefs :: GrammarDefs
emptyGrammarDefs = GrammarDefs S.empty S.empty M.empty []

-- | Generic fold over grammar expressions (catamorphism)
-- The function handles GLit; recursion handles everything else
foldGrammarLits :: (String -> S.Set String) -> GrammarExpr () -> S.Set String
foldGrammarLits f = go
  where
    go GEmpty = S.empty
    go (GLit s) = f s
    go (GRegex _) = S.empty
    go (GChar _) = S.empty
    go (GNode _ gs) = S.unions (map go gs)
    go (GSeq g1 g2) = S.union (go g1) (go g2)
    go (GAlt g1 g2) = S.union (go g1) (go g2)
    go (GStar g) = go g
    go (GRec _ g) = go g
    go (GRef _) = S.empty
    go (GBind _ g) = go g
    go (GCut g) = go g
    go (GVar _) = S.empty
    go GAny = S.empty

-- | Extract all keyword literals from a grammar expression
extractKeywords :: GrammarExpr () -> S.Set String
extractKeywords = foldGrammarLits S.singleton

-- | Extract symbol literals from a grammar expression.
extractSymbols :: GrammarExpr () -> S.Set String
extractSymbols = foldGrammarLits (\s -> if isSymbol s then S.singleton s else S.empty)

-- | Extract all keywords from grammar definitions
extractAllKeywords :: GrammarDefs -> S.Set String
extractAllKeywords gd = 
  let fromGrammars = S.unions (map extractKeywords (M.elems (gdProductions gd)))
      fromVocab = gdKeywords gd
  in S.union fromGrammars fromVocab

-- | Extract all symbol literals from grammar definitions.
-- Includes both explicit 'vocab:' symbols (if present) and symbols appearing
-- in productions.
extractAllSymbols :: GrammarDefs -> S.Set String
extractAllSymbols gd =
  let fromGrammars = S.unions (map extractSymbols (M.elems (gdProductions gd)))
      fromVocab = gdSymbols gd
  in S.union fromGrammars fromVocab

-- | Extract grammar definitions from parsed declarations  
-- Call parseLegoFile first, then pass the result here
loadGrammarDefs :: [LegoDecl] -> GrammarDefs
loadGrammarDefs decls = 
  -- Two-pass: first collect all pieces, then resolve inheritance
  let allDecls = decls
      -- Build a map of piece name -> (parents, body)
      pieceMap = buildPieceMap allDecls M.empty
      -- Resolve inheritance (topological order via fixpoint)
      resolved = resolvePieces pieceMap
  in extractGrammarDefs' resolved allDecls

-- | Build map of piece name -> (parents, body declarations)
-- Recursively processes nested pieces inside DLang and DPiece bodies
buildPieceMap :: [LegoDecl] -> M.Map String ([String], [LegoDecl]) -> M.Map String ([String], [LegoDecl])
buildPieceMap [] m = m
buildPieceMap (DPiece name parents body : rest) m = 
  -- Add this piece, then recursively process its body for nested pieces
  let m' = M.insert name (parents, body) m
      m'' = buildPieceMap body m'  -- Process nested pieces
  in buildPieceMap rest m''
buildPieceMap (DLang name parents body : rest) m = 
  -- Treat DLang as DPiece with its parents, and recursively process body
  let m' = M.insert name (parents, body) m
      m'' = buildPieceMap body m'  -- Process nested pieces
  in buildPieceMap rest m''
buildPieceMap (_ : rest) m = buildPieceMap rest m

-- | Resolve piece inheritance: expand parents' declarations into each piece
resolvePieces :: M.Map String ([String], [LegoDecl]) -> M.Map String [LegoDecl]
resolvePieces pieceMap = fixpointResolve pieceMap M.empty 100
  where
    -- Fixpoint: keep expanding until no change or fuel exhausted
    fixpointResolve :: M.Map String ([String], [LegoDecl]) -> M.Map String [LegoDecl] -> Int -> M.Map String [LegoDecl]
    fixpointResolve _ resolved 0 = resolved  -- fuel exhausted
    fixpointResolve pm resolved fuel = 
      let resolved' = M.mapWithKey (expandPiece pm resolved) pm
          -- Extract just the declarations
          resolved'' = M.map snd resolved'
      in if resolved'' == resolved 
         then resolved
         else fixpointResolve pm resolved'' (fuel - 1)
    
    -- Expand a piece by prepending parent declarations
    expandPiece :: M.Map String ([String], [LegoDecl]) -> M.Map String [LegoDecl] -> String -> ([String], [LegoDecl]) -> ([String], [LegoDecl])
    expandPiece pm resolved _name (parents, body) =
      let parentDecls = concatMap (lookupParent pm resolved) parents
      in (parents, parentDecls ++ body)
    
    -- Look up parent's resolved declarations
    lookupParent :: M.Map String ([String], [LegoDecl]) -> M.Map String [LegoDecl] -> String -> [LegoDecl]
    lookupParent pm resolved parent = 
      case M.lookup parent resolved of
        Just decls -> decls
        Nothing -> case M.lookup parent pm of
          Just (_, body) -> body
          Nothing -> []  -- Unknown parent, ignore

-- | Extract grammar definitions with resolved pieces
extractGrammarDefs' :: M.Map String [LegoDecl] -> [LegoDecl] -> GrammarDefs
extractGrammarDefs' resolved = foldr (addDecl resolved) emptyGrammarDefs
  where
    addDecl _ (DVocab kws syms) gd = 
      gd { gdKeywords = S.union (S.fromList kws) (gdKeywords gd)
         , gdSymbols = S.union (S.fromList syms) (gdSymbols gd) }
    addDecl _ (DGrammar name g) gd =
      gd { gdProductions = M.insert name g (gdProductions gd) }
    addDecl _ (DRule r) gd =
      gd { gdRules = r : gdRules gd }
    addDecl res (DPiece name _ _) gd = 
      -- Use resolved piece declarations
      case M.lookup name res of
        Just body -> extractGrammarDefs' res body `mergeGD` gd
        Nothing -> gd
    addDecl res (DLang name _ body) gd = 
      -- Use resolved piece declarations if available
      case M.lookup name res of
        Just resolved' -> extractGrammarDefs' res resolved' `mergeGD` gd
        Nothing -> extractGrammarDefs' res body `mergeGD` gd
    addDecl _ _ gd = gd
    
    mergeGD gd1 gd2 = GrammarDefs
      { gdKeywords = S.union (gdKeywords gd1) (gdKeywords gd2)
      , gdSymbols = S.union (gdSymbols gd1) (gdSymbols gd2)
      , gdProductions = M.union (gdProductions gd1) (gdProductions gd2)
      , gdRules = gdRules gd1 ++ gdRules gd2 }

--------------------------------------------------------------------------------
-- Bidirectional Interpretation
--------------------------------------------------------------------------------

-- | Run grammar in specified mode
-- Returns list of possible states (non-deterministic)
-- Uses packrat memoization for GRef lookups
runGrammar :: GrammarExpr () -> BiState Token Term -> [BiState Token Term]
runGrammar = go
  where
    go :: GrammarExpr () -> BiState Token Term -> [BiState Token Term]
    
    -- Empty: always succeeds
    go GEmpty st = [st]
    
    -- Regex literal: consume/produce regex token
    go (GRegex s) st = case bsMode st of
      Parse -> case bsTokens st of
        (TRegex t : ts) | t == s -> [st { bsTokens = ts }]
        _ -> []
      Print -> [st { bsTokens = bsTokens st ++ [TRegex s] }]
      Check -> [st]
    
    -- Content literal: consume/produce token (strict match for print)
    go (GLit s) st = case bsMode st of
      Parse -> case bsTokens st of
        (TIdent t : ts) | t == s -> [st { bsTokens = ts }]
        (TKeyword t : ts) | t == s -> [st { bsTokens = ts }]
        (TReserved t : ts) | t == s -> [st { bsTokens = ts }]
        (TSym t : ts) | t == s -> [st { bsTokens = ts }]
        (TString t : ts) | t == s -> [st { bsTokens = ts }]
        (TRegex t : ts) | t == s -> [st { bsTokens = ts }]
        _ -> []  -- no match
      Print -> [st { bsTokens = bsTokens st ++ [TIdent s] }]
      Check -> [st]
    
    -- Char class literal: match char token
    go (GChar s) st = case bsMode st of
      Parse -> case bsTokens st of
        (TChar t : ts) | t == s -> [st { bsTokens = ts }]
        _ -> []
      Print -> [st { bsTokens = bsTokens st ++ [TChar s] }]
      Check -> [st]
    
    -- Sequence: chain interpretations
    go (GSeq g1 g2) st = do
      st1 <- go g1 st
      go g2 st1
    
    -- Alternative: try branches (PEG-style: first success wins in parse mode)
    go (GAlt g1 g2) st = case bsMode st of
      Parse -> case go g1 st of
        [] -> go g2 st  -- PEG: try second only if first fails
        results -> results
      _ -> go g1 st ++ go g2 st  -- non-deterministic for print/check
    
    -- Kleene star: zero or more
    -- In Parse mode: greedy (PEG semantics) - match as many as possible
    -- In Print/Check mode: non-deterministic - try all possibilities
    go (GStar g) st = case bsMode st of
      Parse -> greedyStar g st
      _ -> st : do  -- non-deterministic for print/check
        st1 <- go g st
        guard (bsTokens st1 /= bsTokens st)
        go (GStar g) st1
    
    -- Recursion: bind name and recurse
    go (GRec x g) st = go g (st { bsGrammar = M.insert x g (bsGrammar st) })
    
    -- Reference: lookup and interpret with packrat memoization
    -- Memoization key: (production name, token count) for Parse mode
    go (GRef x) st = case bsMode st of
      Parse -> 
        let stRefined = refineAtRef x st
            pos = length (bsTokens stRefined)
            key = (x, pos)
        in case M.lookup key (bsMemo stRefined) of
          Just cached -> 
            -- Reconstruct states from cached entries
            [ stRefined { bsTokens = drop consumed (bsTokens stRefined)
                        , bsTerm = mterm
                        , bsBinds = mbinds }
            | (mterm, consumed, mbinds) <- cached ]
          Nothing ->
            -- Cache miss: compute and store
            case resolveRef x stRefined of
              Nothing -> []  -- undefined reference
              Just g ->
                let results = go g stRefined
                    -- Extract cacheable info from results
                    entries = [ (bsTerm r, pos - length (bsTokens r), bsBinds r) | r <- results ]
                    -- Store in memo and return results with updated memo
                    newMemo = M.insert key entries (bsMemo stRefined)
                in map (\r -> r { bsMemo = newMemo }) results
      _ -> 
        -- No memoization for Print/Check modes (different semantics)
        case resolveRef x st of
          Nothing -> []
          Just g -> go g st
    
    -- Bind: capture token/field (into current scope only)
    -- Also preserves bsTerm from inner grammar for structural composition
    go (GBind name g) st = case bsMode st of
      Parse -> do
        st1 <- go g st
        -- Capture the consumed portion as a term into current scope
        let consumed = length (bsTokens st) - length (bsTokens st1)
        let captured = take consumed (bsTokens st)
        let term = tokensToTerm captured
        -- Preserve bsTerm from inner grammar (important for tokConstr args)
        [st1 { bsBinds = insertBind name term (bsBinds st1) }]
      Print -> do
        case lookupBind name (bsBinds st) of
          Just term -> 
            let toks = termToTokens term
            in [st { bsTokens = bsTokens st ++ toks }]
          Nothing -> go g st
      Check -> go g st
    
    -- Cut: commit point - if g succeeds, no backtracking past this point
    -- In Parse mode: acts as a commit - returns only the first success
    -- This is the PEG "cut" operator for better error recovery
    go (GCut g) st = case bsMode st of
      Parse -> case go g st of
        []      -> []         -- cut failed: normal failure
        (r:_)   -> [r]        -- cut succeeded: commit to first result only
      _ -> go g st            -- no-op for print/check
    
    -- Variable: use captured value (lexical lookup)
    go (GVar x) st = case bsMode st of
      Parse -> case lookupBind x (bsBinds st) of
        Just _ -> [st]
        Nothing -> []
      Print -> case lookupBind x (bsBinds st) of
        Just term -> [st { bsTokens = bsTokens st ++ termToTokens term }]
        Nothing -> []
      Check -> [st]
    
    -- Node: semantic marker for AST construction, OR special token type
    -- Special token types: "ident", "digits", "string", "chars", "constructor", "patvar", "anglevar"
    -- These set both bsBinds (for backward compatibility) and bsTerm (for GNode arg collection)
    go (GNode con []) st = case bsMode st of
      Parse -> case con of
        -- Match identifier token
        -- <ident> rejects reserved words (TReserved).
        --
        -- Soft keywords (TKeyword) are allowed as identifiers to avoid breaking
        -- contexts where a word-like token can be both a keyword and an ident.
        "ident" -> case bsTokens st of
          (TIdent s : ts) -> [st { bsTokens = ts
                                 , bsBinds = insertBind "_ident" (TmVar s) (bsBinds st)
                                 , bsTerm = Just (TmVar s) }]
          (TKeyword s : ts) -> [st { bsTokens = ts
                                   , bsBinds = insertBind "_ident" (TmVar s) (bsBinds st)
                                   , bsTerm = Just (TmVar s) }]
          -- Accept TSym for identifier when it's a valid identifier-like symbol
          -- This allows Unicode symbols like λᵢ, Π, Σ to be used as node names
          (TSym s : ts) | isIdentLikeSym s -> 
            [st { bsTokens = ts
                , bsBinds = insertBind "_ident" (TmVar s) (bsBinds st)
                , bsTerm = Just (TmVar s) }]
          _ -> []
        -- Match number/digits token (both <number> and <digits> work)
        _ | con `elem` ["number", "digits"] -> case bsTokens st of
          (TIdent s : ts) | all isDigitChar s -> 
            [st { bsTokens = ts
                , bsBinds = insertBind "_number" (TmLit s) (bsBinds st)
                , bsTerm = Just (TmLit s) }]
          _ -> []
        -- Match string token
        "string" -> case bsTokens st of
          (TString s : ts) -> [st { bsTokens = ts
                                  , bsBinds = insertBind "_string" (TmLit s) (bsBinds st)
                                  , bsTerm = Just (TmLit s) }]
          _ -> []
        -- Match regex token
        "regex" -> case bsTokens st of
          (TRegex s : ts) -> [st { bsTokens = ts
                                 , bsBinds = insertBind "_regex" (TmLit s) (bsBinds st)
                                 , bsTerm = Just (TmLit s) }]
          _ -> []
        -- Match char literal token (single-quoted strings like 'x')
        "char" -> case bsTokens st of
          (TChar s : ts) -> [st { bsTokens = ts
                                , bsBinds = insertBind "_char" (TmChar s) (bsBinds st)
                                , bsTerm = Just (TmChar s) }]
          _ -> []
        -- Match any chars (inside string - not used at token level)
        "chars" -> [st]  -- no-op, strings are already tokenized
        -- Metavariable: "$" ident → TmVar "$x"
        "metavar" -> case bsTokens st of
          (TSym "$" : TIdent s : ts) -> 
            [st { bsTokens = ts
                , bsBinds = insertBind "_metavar" (TmVar ('$':s)) (bsBinds st)
                , bsTerm = Just (TmVar ('$':s)) }]
          (TSym "$" : TKeyword s : ts) ->
            [st { bsTokens = ts
                , bsBinds = insertBind "_metavar" (TmVar ('$':s)) (bsBinds st)
                , bsTerm = Just (TmVar ('$':s)) }]
          (TSym "$" : TReserved s : ts) ->
            [st { bsTokens = ts
                , bsBinds = insertBind "_metavar" (TmVar ('$':s)) (bsBinds st)
                , bsTerm = Just (TmVar ('$':s)) }]
          _ -> []
        -- Literal identifier: ident → TmLit "ident"
        -- Used in patterns/templates for literals that must match exactly
        "litident" -> case bsTokens st of
          (TIdent s : ts) -> [st { bsTokens = ts
                                 , bsBinds = insertBind "_litident" (TmLit s) (bsBinds st)
                                 , bsTerm = Just (TmLit s) }]
          (TKeyword s : ts) -> [st { bsTokens = ts
                                   , bsBinds = insertBind "_litident" (TmLit s) (bsBinds st)
                                   , bsTerm = Just (TmLit s) }]
          (TReserved s : ts) -> [st { bsTokens = ts
                                    , bsBinds = insertBind "_litident" (TmLit s) (bsBinds st)
                                    , bsTerm = Just (TmLit s) }]
          _ -> []
        -- Match newline token
        "newline" -> case bsTokens st of
          (TNewline : ts) -> [st { bsTokens = ts
                                 , bsBinds = insertBind "_newline" (TmCon "newline" []) (bsBinds st)
                                 , bsTerm = Just (TmCon "newline" []) }]
          _ -> []
        -- Match indent token
        "indent" -> case bsTokens st of
          (TIndent n : ts) -> [st { bsTokens = ts
                                  , bsBinds = insertBind "_indent" (TmCon "indent" [TmLit (show n)]) (bsBinds st)
                                  , bsTerm = Just (TmCon "indent" [TmLit (show n)]) }]
          _ -> []
        -- Other node types: semantic marker only
        _ -> [st { bsTerm = Just (TmCon con []) }]
      Print -> case con of
        -- Print ident: TmVar s → ident token
        "ident" -> case bsTerm st of
          Just (TmVar s) -> [st { bsTokens = bsTokens st ++ [TIdent s], bsTerm = Nothing }]
          _ -> []
        -- Print number/digits: TmLit s → digit token
        _ | con `elem` ["number", "digits"] -> case bsTerm st of
          Just (TmLit s) -> [st { bsTokens = bsTokens st ++ [TIdent s], bsTerm = Nothing }]
          _ -> []
        -- Print string: TmLit s → string token
        "string" -> case bsTerm st of
          Just (TmLit s) -> [st { bsTokens = bsTokens st ++ [TString s], bsTerm = Nothing }]
          _ -> []
        -- Print regex: TmLit s → regex token
        "regex" -> case bsTerm st of
          Just (TmLit s) -> [st { bsTokens = bsTokens st ++ [TRegex s], bsTerm = Nothing }]
          _ -> []
        -- Print metavariable: TmVar "$x" → "$" "x"
        "metavar" -> printSimple (\case TmVar ('$':s) -> Just [TSym "$", TIdent s]; _ -> Nothing) st
        -- Print literal identifier: TmLit s → ident
        "litident" -> printSimple (\case TmLit s -> Just [TIdent s]; _ -> Nothing) st
        -- Print newline: TmCon "newline" [] → newline
        "newline" -> printSimple (\case TmCon "newline" [] -> Just [TNewline]; _ -> Nothing) st
        -- Print indent: TmCon "indent" [TmLit n] → indent
        "indent" -> printSimple (\case TmCon "indent" [TmLit n] -> Just [TIndent (read n)]; _ -> Nothing) st
        -- Print char literal: TmChar s → 'char'
        "char" -> printSimple (\case TmChar s -> Just [TChar s]; _ -> Nothing) st
        _ -> [st]  -- no-op for other simple nodes
      Check -> [st]
    
    -- GNode with args: introduces a new scope for structural isolation
    -- Special case: "constructor"/"constr" [argGram] parses "(" ident args* ")" → TmCon ident args
    -- Collects bsTerm results from each child grammar
    -- Also handles symbol constructors like (~ x), (∧ x y), (@ p i) for cubical
    go (GNode constrName [argGram]) st | constrName `elem` ["constructor", "constr"] = case bsMode st of
      Parse -> case bsTokens st of
        -- Qualified constructor: (module/name args*) or (path/to/name args*)
        -- Pattern: "(" ident "/" ident "/" ... → joined with "/"
        (TSym "(" : TIdent conName : TSym "/" : TIdent part2 : rest) -> do
          -- Collect qualified name parts: name / part2 / part3 / ...
          let (moreParts, rest') = collectQualParts rest
              qualName = intercalate "/" (conName : part2 : moreParts)
              st0 = st { bsTokens = rest', bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          (st1, argTerms) <- parseConstrArgs argGram st0
          case bsTokens st1 of
            (TSym ")" : rest'') ->
              [st1 { bsTokens = rest''
                   , bsTerm = Just (TmCon qualName argTerms)
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> []
        -- Level annotation: (type^1) or (Type^n) - join with "^"
        -- Pattern: "(" ident "^" digit ... → joined as "type^1"
        (TSym "(" : TIdent conName : TSym "^" : TIdent level : rest) -> do
          -- Build level-annotated name
          let leveledName = conName ++ "^" ++ level
              st0 = st { bsTokens = rest, bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          (st1, argTerms) <- parseConstrArgs argGram st0
          case bsTokens st1 of
            (TSym ")" : rest') ->
              [st1 { bsTokens = rest'
                   , bsTerm = Just (TmCon leveledName argTerms)
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> []
        (TSym "(" : TIdent conName : rest) -> do
          -- Parse args using argGram until we hit ")"
          let st0 = st { bsTokens = rest, bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          (st1, argTerms) <- parseConstrArgs argGram st0
          -- Consume closing paren
          case bsTokens st1 of
            (TSym ")" : rest') ->
              [st1 { bsTokens = rest'
                   , bsTerm = Just (TmCon conName argTerms)
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> []  -- missing close paren
        (TSym "(" : TKeyword conName : rest) -> do
          let st0 = st { bsTokens = rest, bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          (st1, argTerms) <- parseConstrArgs argGram st0
          case bsTokens st1 of
            (TSym ")" : rest') ->
              [st1 { bsTokens = rest'
                   , bsTerm = Just (TmCon conName argTerms)
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> []
        -- Symbol as constructor: (~ x), (∧ x y), (@ p i), etc.
        -- Note: "$" is excluded because it's the metavariable sigil, not a constructor
        (TSym "(" : TSym conName : rest) | conName `notElem` [")", "(", "$"] -> do
          let st0 = st { bsTokens = rest, bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          (st1, argTerms) <- parseConstrArgs argGram st0
          case bsTokens st1 of
            (TSym ")" : rest') ->
              [st1 { bsTokens = rest'
                   , bsTerm = Just (TmCon conName argTerms)
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> []
        -- Infix binary: (arg1 op arg2) where op is a symbol
        -- OR Postfix unary: (arg1 op) where op is a postfix symbol like ⁻¹
        -- OR Juxtaposition application: (arg1 arg2 ...) where args are just next to each other
        -- This handles patterns like ((refl $a) · $p), ((refl $a) ⁻¹), and (($x $z) ($y $z))
        (TSym "(" : _) -> do
          let st0 = st { bsTokens = drop 1 (bsTokens st), bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
          -- Parse first argument
          st1 <- go argGram st0
          arg1 <- maybeToList (bsTerm st1)
          case bsTokens st1 of
            -- Infix/postfix operator (symbol)
            (TSym op : rest2) | isInfixOp op -> do
              -- Check if this is postfix (op ")") or infix (op arg2 ")")
              case rest2 of
                (TSym ")" : rest3) ->
                  -- Postfix: (arg1 op)
                  [st1 { bsTokens = rest3
                       , bsTerm = Just (TmCon op [arg1])
                       , bsBinds = popScope (bsBinds st1) }]
                _ -> do
                  -- Infix: (arg1 op arg2)
                  let st2 = st1 { bsTokens = rest2, bsTerm = Nothing }
                  st3 <- go argGram st2
                  arg2 <- maybeToList (bsTerm st3)
                  -- Expect close paren
                  case bsTokens st3 of
                    (TSym ")" : rest3) ->
                      [st3 { bsTokens = rest3
                           , bsTerm = Just (TmCon op [arg1, arg2])
                           , bsBinds = popScope (bsBinds st3) }]
                    _ -> []
            -- Juxtaposition application: (arg1 arg2 ...) → TmCon "@" [arg1, TmCon "@" [arg2, ...]]
            -- This handles templates like (($x $z) ($y $z))
            (TSym ")" : rest2) ->
              -- Single element: (arg1) - just return arg1
              [st1 { bsTokens = rest2
                   , bsTerm = Just arg1
                   , bsBinds = popScope (bsBinds st1) }]
            _ -> do
              -- Try to parse more args (juxtaposition application)
              (st2, moreArgs) <- parseConstrArgs argGram (st1 { bsTerm = Nothing })
              case bsTokens st2 of
                (TSym ")" : rest2) ->
                  -- Build left-associative application: (f x y) = ((f x) y)
                  let allArgs = arg1 : moreArgs
                      app = foldl1 (\a b -> TmCon "@" [a, b]) allArgs
                  in [st2 { bsTokens = rest2
                          , bsTerm = Just app
                          , bsBinds = popScope (bsBinds st2) }]
                _ -> []
        _ -> []
      Print -> case bsTerm st of
        Just (TmCon conName subterms) -> do
          -- Print "(" conName args* ")"
          -- Use TSym for symbol constructors, TIdent for identifiers
          let conTok = if isSymbol conName then TSym conName else TIdent conName
              st0 = st { bsTokens = bsTokens st ++ [TSym "(", conTok]
                       , bsBinds = pushScope (bsBinds st) }
          st1 <- foldMPrint (\s t -> go argGram (s { bsTerm = Just t })) st0 subterms
          [st1 { bsTokens = bsTokens st1 ++ [TSym ")"]
               , bsTerm = Nothing
               , bsBinds = popScope (bsBinds st1) }]
        _ -> []
      Check -> [st]
    go (GNode con args) st = case bsMode st of
      Parse -> do
        -- Push scope, parse all args collecting their terms, pop scope
        let st0 = st { bsBinds = pushScope (bsBinds st), bsTerm = Nothing }
        (st1, argTerms) <- foldMCollect (\s g -> go g s) st0 args
        let term = TmCon con argTerms
        -- INCREMENTAL GRAMMAR: When we see DPiece or DLang, immediately
        -- compile and merge the grammar so subsequent parsing uses it
        let st2 = case con of
              "DPiece" -> mergePieceGrammar term st1
              "DLang"  -> mergeLangGrammar term st1
              _        -> st1
        [st2 { bsTerm = Just term
             , bsBinds = popScope (bsBinds st2) }]
      Print -> case bsTerm st of
        Just (TmCon c subterms) | c == con -> do
          -- Push scope, print each grammar part
          -- Only GRef consumes from subterms, others just print
          let st0 = st { bsBinds = pushScope (bsBinds st) }
          (st1, _) <- foldMPrintWithTerms (\s (g, t) -> go g (s { bsTerm = t })) 
                            st0 args subterms
          [st1 { bsTerm = Nothing, bsBinds = popScope (bsBinds st1) }]
        _ -> []
      Check -> do
        let st0 = st { bsBinds = pushScope (bsBinds st) }
        st1 <- foldM (\s g -> go g s) st0 args
        [st1 { bsBinds = popScope (bsBinds st1) }]
    
    -- Any: match any single token (insert into current scope)
    go GAny st = case bsMode st of
      Parse -> case bsTokens st of
        (t:ts) -> [st { bsTokens = ts
                      , bsBinds = insertBind "_" (tokenToTerm t) (bsBinds st) }]
        _ -> []
      Print -> [st]
      Check -> [st]
    
    -- Helper: resolve a reference name to its grammar (used by GRef memoization)
    -- Resolution strategy for unqualified names (no dot):
    --   1) Suffix match finds any "Piece.name" for "name"
    --   2) Fall back to builtin
    -- Resolution for qualified names (with dot):
    --   1) Direct lookup
    --   2) Suffix match (in case namespace differs)
    --   3) Fall back to builtin
    resolveRef :: String -> BiState Token Term -> Maybe (GrammarExpr ())
    resolveRef x st
      | '.' `elem` x = 
          -- Qualified name: try direct first, then suffix, then builtin
          case M.lookup x (bsGrammar st) of
            Just g  -> Just g
            Nothing -> 
              -- Extract base name: "A.B.term" -> "term"
              let baseName = case break (== '.') (reverse x) of
                               (rev, _:_) -> reverse rev
                               _ -> x
              in case findSuffixedGrammar baseName (bsGrammar st) of
                   Just g  -> Just g
                   Nothing -> builtinGrammar x
      | otherwise = 
          -- Unqualified name: prefer suffix match (finds piece-defined), then builtin
          case findSuffixedGrammar x (bsGrammar st) of
            Just g  -> Just g
            Nothing -> builtinGrammar x

    -- Phase 3: production-scoped keyword refinement.
    --
    -- We only refine the NEXT token (head) when entering a production reference.
    -- The refined set is derived from FIRST-word literals of that production.
    -- This avoids global "everything is a keyword" regressions while still
    -- preventing <ident> from greedily consuming declaration-head keywords.
    refineAtRef :: String -> BiState Token Term -> BiState Token Term
    refineAtRef refName st =
      let kws = firstWordLitsForRef refName st
          hard = S.intersection kws hardReservedWords
      in st { bsTokens = refineHead hard kws (bsTokens st) }

    -- Only reserve a very small set of structural words by default.
    -- This avoids the "everything is reserved" regression while still fixing
    -- the classic greedy-<ident> boundary bugs.
    hardReservedWords :: S.Set String
    hardReservedWords = S.fromList
      [ "in", "of", "then", "else", "where", "with", "is"
      , "let", "case", "if", "match"
      ]

    refineHead :: S.Set String -> S.Set String -> [Token] -> [Token]
    refineHead hard soft (TIdent s : ts)
      | s `S.member` hard = TReserved s : ts
      | s `S.member` soft = TKeyword s : ts
    refineHead _ _ toks = toks

    firstWordLitsForRef :: String -> BiState Token Term -> S.Set String
    firstWordLitsForRef refName st =
      case resolveRef refName st of
        Nothing -> S.empty
        Just g -> firstWordLits st S.empty g

    firstWordLits :: BiState Token Term -> S.Set String -> GrammarExpr () -> S.Set String
    firstWordLits _ _ GEmpty = S.empty
    firstWordLits _ _ (GLit s) = if isSymbol s then S.empty else S.singleton s
    firstWordLits _ _ (GRegex _) = S.empty  -- regex patterns don't contribute
    firstWordLits _ _ (GChar _) = S.empty  -- char classes don't contribute
    firstWordLits st seen (GSeq g1 g2)
      | nullable st seen g1 = S.union (firstWordLits st seen g1) (firstWordLits st seen g2)
      | otherwise = firstWordLits st seen g1
    firstWordLits st seen (GAlt g1 g2) = S.union (firstWordLits st seen g1) (firstWordLits st seen g2)
    firstWordLits st seen (GStar g) = firstWordLits st seen g
    firstWordLits st seen (GRec _ g) = firstWordLits st seen g
    firstWordLits st seen (GRef name)
      | name `S.member` seen = S.empty
      | otherwise =
          case resolveRef name st of
            Nothing -> S.empty
            Just g -> firstWordLits st (S.insert name seen) g
    firstWordLits st seen (GBind _ g) = firstWordLits st seen g
    firstWordLits st seen (GCut g) = firstWordLits st seen g  -- cut passes through
    firstWordLits _ _ (GVar _) = S.empty
    firstWordLits _ _ (GNode _ _) = S.empty
    firstWordLits _ _ GAny = S.empty

    nullable :: BiState Token Term -> S.Set String -> GrammarExpr () -> Bool
    nullable _ _ GEmpty = True
    nullable _ _ (GLit _) = False
    nullable _ _ (GRegex _) = False
    nullable _ _ (GChar _) = False
    nullable st seen (GSeq g1 g2) = nullable st seen g1 && nullable st seen g2
    nullable st seen (GAlt g1 g2) = nullable st seen g1 || nullable st seen g2
    nullable _ _ (GStar _) = True
    nullable st seen (GRec _ g) = nullable st seen g
    nullable st seen (GRef name)
      | name `S.member` seen = False
      | otherwise =
          case resolveRef name st of
            Nothing -> False
            Just g -> nullable st (S.insert name seen) g
    nullable st seen (GBind _ g) = nullable st seen g
    nullable st seen (GCut g) = nullable st seen g  -- cut passes through
    nullable _ _ (GVar _) = True
    nullable st seen (GNode _ args) = all (nullable st seen) args
    nullable _ _ GAny = False
    
    -- Greedy star: match as many as possible, return only the longest match (PEG semantics)
    -- Collects bsTerm from each iteration into TmCon "seq" [...]
    greedyStar :: GrammarExpr () -> BiState Token Term -> [BiState Token Term]
    greedyStar g st = greedyStarCollect g st []
    
    -- Helper: collect terms from each iteration of star
    greedyStarCollect :: GrammarExpr () -> BiState Token Term -> [Term] -> [BiState Token Term]
    greedyStarCollect g st acc = case go g st of
      [] -> 
        -- Can't match any more, build final sequence
        let seqTerm = case acc of
              [] -> Nothing  -- empty star produces no term
              [t] -> Just t  -- single element: just return it
              ts -> Just (TmCon "seq" (reverse ts))  -- multiple: wrap in seq
        in [st { bsTerm = seqTerm }]
      results -> 
        -- Filter to results that made progress
        let progress = filter (\st1 -> bsTokens st1 /= bsTokens st) results
        in case progress of
          [] -> 
            -- No progress made, stop here
            let seqTerm = case acc of
                  [] -> Nothing
                  [t] -> Just t
                  ts -> Just (TmCon "seq" (reverse ts))
            in [st { bsTerm = seqTerm }]
          (st1:_) -> 
            -- Made progress: collect term and continue
            let newTerm = fromMaybe (TmCon "unit" []) (bsTerm st1)
            in greedyStarCollect g (st1 { bsTerm = Nothing }) (newTerm : acc)
    
    -- Parse constructor args until ")"
    -- Skips whitespace (TNewline, TIndent) between args for multi-line terms
    -- Also handles qualified identifiers like l/ih as single args
    parseConstrArgs :: GrammarExpr () -> BiState Token Term -> [(BiState Token Term, [Term])]
    parseConstrArgs _ s | isCloseParen (skipWs (bsTokens s)) = [(s { bsTokens = skipWs (bsTokens s) }, [])]
    parseConstrArgs argGram s = do
      let s0 = s { bsTokens = skipWs (bsTokens s) }
      -- Check for qualified identifier pattern: ident "/" ident "/" ...
      case bsTokens s0 of
        (TIdent first : TSym "/" : TIdent second : rest) -> do
          let (moreParts, rest') = collectQualParts rest
              qualName = intercalate "/" (first : second : moreParts)
              term = TmVar qualName
          (s'', terms) <- parseConstrArgs argGram (s0 { bsTokens = rest', bsTerm = Nothing })
          [(s'', term : terms)]
        _ -> do
          s' <- go argGram s0
          let term = fromMaybeT (TmCon "unit" []) (bsTerm s')
          (s'', terms) <- parseConstrArgs argGram (s' { bsTerm = Nothing })
          [(s'', term : terms)]
    
    -- Skip whitespace tokens (newlines and indentation)
    skipWs :: [Token] -> [Token]
    skipWs (TNewline : rest) = skipWs rest
    skipWs (TIndent _ : rest) = skipWs rest
    skipWs ts = ts
    
    isCloseParen :: [Token] -> Bool
    isCloseParen (TSym ")" : _) = True
    isCloseParen _ = False
    
    -- Collect qualified name parts: "/" ident "/" ident ...
    -- Returns (list of parts, remaining tokens)
    collectQualParts :: [Token] -> ([String], [Token])
    collectQualParts (TSym "/" : TIdent part : rest) = 
      let (more, rest') = collectQualParts rest
      in (part : more, rest')
    collectQualParts ts = ([], ts)
    -- Fold that collects bsTerm from each step (only Just terms, skip Nothing)
    foldMCollect :: (BiState Token Term -> GrammarExpr () -> [BiState Token Term]) 
                 -> BiState Token Term -> [GrammarExpr ()] -> [(BiState Token Term, [Term])]
    foldMCollect _ s [] = [(s, [])]
    foldMCollect f s (x:xs) = do
      s' <- f s x
      (s'', terms) <- foldMCollect f (s' { bsTerm = Nothing }) xs
      -- Only collect if there's a term (skip literals which produce Nothing)
      let terms' = case bsTerm s' of
            Just t  -> t : terms
            Nothing -> terms
      [(s'', terms')]
    
    -- Fold for printing (doesn't collect)
    foldMPrint :: (BiState Token Term -> a -> [BiState Token Term]) 
               -> BiState Token Term -> [a] -> [BiState Token Term]
    foldMPrint _ s [] = [s]
    foldMPrint f s (x:xs) = f s x >>= \s' -> foldMPrint f s' xs
    
    -- Fold for printing with terms: only refs consume from term list
    foldMPrintWithTerms :: (BiState Token Term -> (GrammarExpr (), Maybe Term) -> [BiState Token Term]) 
                        -> BiState Token Term -> [GrammarExpr ()] -> [Term] -> [(BiState Token Term, [Term])]
    foldMPrintWithTerms _ s [] ts = [(s, ts)]
    foldMPrintWithTerms f s (g:gs) ts = do
      let (mterm, ts') = case g of
            GRef _ -> case ts of
              (t:rest) -> (Just t, rest)
              []       -> (Nothing, [])
            _ -> (Nothing, ts)  -- Literals don't consume terms
      s' <- f s (g, mterm)
      foldMPrintWithTerms f s' gs ts'
    
    fromMaybeT :: Term -> Maybe Term -> Term
    fromMaybeT d Nothing = d
    fromMaybeT _ (Just x) = x
    
    -- foldM for list monad
    foldM :: (BiState Token Term -> a -> [BiState Token Term]) 
          -> BiState Token Term -> [a] -> [BiState Token Term]
    foldM _ z [] = [z]
    foldM f z (x:xs) = f z x >>= \z' -> foldM f z' xs

-- | Convert tokens to term (for capture)
tokensToTerm :: [Token] -> Term
tokensToTerm [] = TmCon "unit" []
tokensToTerm [t] = tokenToTerm t
tokensToTerm ts = TmCon "seq" (map tokenToTerm ts)

tokenToTerm :: Token -> Term
tokenToTerm (TIdent s) = TmVar s
tokenToTerm (TKeyword s) = TmVar s
tokenToTerm (TReserved s) = TmVar s
tokenToTerm (TString s) = TmLit s      -- Quoted strings become TmLit
tokenToTerm (TRegex s) = TmRegex s     -- Regex literals become TmRegex
tokenToTerm (TChar s) = TmChar s       -- Single-quoted strings become TmChar
tokenToTerm (TSym s) = TmLit s         -- Bare symbols become TmLit
tokenToTerm TNewline = TmCon "newline" []
tokenToTerm (TIndent n) = TmCon "indent" [TmLit (show n)]

-- | Built-in grammars for primitives (name, nat, etc.)
-- These are fallbacks when a grammar reference isn't found in the grammar map
builtinGrammar :: String -> Maybe (GrammarExpr ())
builtinGrammar "name" = Just $ GNode "ident" []   -- Match identifier token
builtinGrammar "nat"  = Just $ GNode "digits" []  -- Match number/digit token
builtinGrammar _ = Nothing

-- | Find a grammar entry where the key ends with ".x"
-- Used to resolve unqualified references like "term" to "Piece.term"
-- Prefers shorter prefixes (e.g., "Term.term" over "BaseTerm.term")
findSuffixedGrammar :: String -> M.Map String (GrammarExpr ()) -> Maybe (GrammarExpr ())
findSuffixedGrammar x m = 
  let suffix = "." ++ x
      matches = [(k, g) | (k, g) <- M.toList m, suffix `isSuffixOf` k]
      -- Sort by key length so shorter prefixes (more canonical) come first
      sorted = sortOn (length . fst) matches
  in case sorted of
       ((_, g):_) -> Just g
       []    -> Nothing
  where
    sortOn f = map snd . sortBy (comparing fst) . map (\a -> (f a, a))
    sortBy cmp = foldr (insertBy cmp) []
    insertBy cmp a [] = [a]
    insertBy cmp a (b:bs) = case cmp a b of
      GT -> b : insertBy cmp a bs
      _  -> a : b : bs
    isSuffixOf needle haystack = drop (length haystack - length needle) haystack == needle

-- | Convert term to tokens (for printing)
termToTokens :: Term -> [Token]
termToTokens (TmVar s) = [TIdent s]
termToTokens (TmLit s) = [TString s]
termToTokens (TmChar s) = [TChar s]
termToTokens (TmCon "unit" []) = []
termToTokens (TmCon "seq" ts) = concatMap termToTokens ts
termToTokens (TmCon "newline" []) = [TNewline]
termToTokens (TmCon "indent" [TmLit n]) = [TIndent (read n)]
termToTokens (TmCon c args) = [TSym "(", TIdent c] ++ 
                              concatMap termToTokens args ++ [TSym ")"]
termToTokens t = [TIdent (show t)]  -- Fallback for any missed cases

--------------------------------------------------------------------------------
-- High-Level API: Parsing
--------------------------------------------------------------------------------

-- | Parse input using a grammar production
parseWith :: GrammarDefs -> String -> String -> Either String Term
parseWith gd prodName input = 
  case M.lookup prodName (gdProductions gd) of
    Nothing -> Left $ "Unknown production: " ++ prodName
    Just g -> 
      let toks = tokenize input
          initState = BiState toks [M.empty] Nothing Parse (gdProductions gd) M.empty
      in case runGrammar g initState of
           [] -> Left "Parse failed"
           (st:_) -> Right $ fromMaybe (bindingsToTerm (flattenBinds (bsBinds st))) (bsTerm st)

-- | Parse using a named production
-- Uses longest-match semantics: prefers result that consumes most tokens
parseProduction :: GrammarDefs -> String -> [Token] -> Either String (Term, [Token])
parseProduction gd prodName toks =
  case M.lookup prodName (gdProductions gd) of
    Nothing -> Left $ "Unknown production: " ++ prodName
    Just g ->
      let initState = BiState toks [M.empty] Nothing Parse (gdProductions gd) M.empty
      in case runGrammar g initState of
           [] -> Left "Parse failed"
           results -> 
             -- Pick result that consumed most tokens (longest match)
             let best = minimumBy (comparing (length . bsTokens)) results
             in Right (fromMaybe (bindingsToTerm (flattenBinds (bsBinds best))) (bsTerm best), 
                      bsTokens best)

-- | Convert bindings to term (from flattened map)
bindingsToTerm :: M.Map String Term -> Term
bindingsToTerm binds = TmCon "bindings" [TmCon k [v] | (k, v) <- M.toList binds]

--------------------------------------------------------------------------------
-- High-Level API: Printing
--------------------------------------------------------------------------------

-- | Print term using a grammar production
printWith :: GrammarDefs -> String -> Term -> Either String String
printWith gd prodName term =
  case M.lookup prodName (gdProductions gd) of
    Nothing -> Left $ "Unknown production: " ++ prodName
    Just g ->
      let initState = BiState [] [M.empty] (Just term) Print (gdProductions gd) M.empty
      in case runGrammar g initState of
           [] -> Left "Print failed"
           (st:_) -> Right $ unwords (map showToken (bsTokens st))

-- | Print using named production
printProduction :: GrammarDefs -> String -> Term -> Either String [Token]
printProduction gd prodName term =
  case M.lookup prodName (gdProductions gd) of
    Nothing -> Left $ "Unknown production: " ++ prodName
    Just g ->
      let initState = BiState [] [M.empty] (Just term) Print (gdProductions gd) M.empty
      in case runGrammar g initState of
           [] -> Left "Print failed"
           (st:_) -> Right (bsTokens st)

-- | Show token as string
showToken :: Token -> String
showToken (TIdent s) = s
showToken (TKeyword s) = s
showToken (TReserved s) = "`" ++ s ++ "`"
showToken (TString s) = "\"" ++ s ++ "\""
showToken (TRegex s) = "/" ++ s ++ "/"
showToken (TChar s) = "'" ++ s ++ "'"
showToken (TSym s) = s
showToken TNewline = "\n"
showToken (TIndent n) = replicate n ' '
showToken (TComment s) = s

--------------------------------------------------------------------------------
-- Convenience: Pre-built Grammar Definitions
--------------------------------------------------------------------------------

-- | Pre-built GrammarDefs for term parsing
-- Combines termGrammar and atomGrammar from GrammarDef
termGrammarDefs :: GrammarDefs
termGrammarDefs = GrammarDefs
  { gdKeywords = S.empty
  , gdSymbols = S.empty
  , gdProductions = M.union termGrammar atomGrammar
  , gdRules = []
  }

-- | Parse a term from a string
-- Convenience function using pre-built term grammar
parseTerm :: String -> Either String Term
parseTerm input = parseWith termGrammarDefs "Term.term" input

--------------------------------------------------------------------------------
-- Incremental Grammar: Pushout on piece/lang declaration
--------------------------------------------------------------------------------

-- | Merge a DPiece term's grammar productions into the state
-- Called during parsing when we complete a (node DPiece ...) construction
-- For production names that exist in both, we EXTEND with alternatives:
--   existing "term ::= a" + new "term ::= b" = "term ::= b | a"
-- This allows piece grammars to add new syntactic forms while keeping
-- the bootstrap grammar's ability to parse metavars, identifiers, etc.
mergePieceGrammar :: Term -> BiState Token Term -> BiState Token Term
mergePieceGrammar (TmCon "DPiece" (nameT : prods)) st =
  let pieceName = case nameT of
        TmVar n -> n
        TmLit n -> n
        _ -> "unknown"
      -- Extract grammar productions from the piece body
      newProds = extractGrammarProds pieceName prods
      -- Merge with extension: new productions extend existing ones with GAlt
      grammar' = foldr extendGrammar (bsGrammar st) newProds
  in st { bsGrammar = grammar' }
  where
    -- Extend grammar: if key exists, combine with GAlt (new | existing)
    extendGrammar (k, newG) m = case M.lookup k m of
      Just existingG -> M.insert k (GAlt newG existingG) m
      Nothing        -> M.insert k newG m
mergePieceGrammar _ st = st

-- | Merge a DLang term's grammar productions into the state
-- Handles both lang inheritance and body productions
mergeLangGrammar :: Term -> BiState Token Term -> BiState Token Term
mergeLangGrammar (TmCon "DLang" (nameT : rest)) st =
  let langName = case nameT of
        TmVar n -> n
        TmLit n -> n
        _ -> "unknown"
      -- Extract grammar from lang body (skip parents term)
      bodyProds = case rest of
        [_, bodyT] -> extractLangBodyGrammar langName bodyT
        [bodyT]    -> extractLangBodyGrammar langName bodyT
        _          -> []
      -- Merge into existing grammar
      grammar' = M.union (M.fromList bodyProds) (bsGrammar st)
  in st { bsGrammar = grammar' }
mergeLangGrammar _ st = st

-- | Extract grammar productions from a piece body
extractGrammarProds :: String -> [Term] -> [(String, GrammarExpr ())]
extractGrammarProds pieceName = concatMap (extractProdFrom pieceName)

extractProdFrom :: String -> Term -> [(String, GrammarExpr ())]
extractProdFrom pn (TmCon "seq" ts) = concatMap (extractProdFrom pn) ts
extractProdFrom pn (TmCon "prodWrap" (d:_)) = extractProdFrom pn d
extractProdFrom pn (TmCon "DGrammar" [TmVar name, gramT]) =
  let gexpr = termToGrammarExpr gramT
      -- Wrap in GNode with production name to create AST nodes
      -- This makes `add ::= "(" "add" term term ")"` parse to TmCon "add" [...]
      wrapped = wrapInNode name gexpr
  in [(pn ++ "." ++ name, wrapped)]
extractProdFrom pn (TmCon "DGrammar" [TmLit name, gramT]) =
  let gexpr = termToGrammarExpr gramT
      wrapped = wrapInNode name gexpr
  in [(pn ++ "." ++ name, wrapped)]
extractProdFrom _ _ = []

-- | Wrap a grammar expression in a GNode if it's not already a node or simple reference
-- For `add ::= "(" "add" term term ")"`:
--   GNode "add" [GLit "(", GLit "add", GRef term, GRef term, GLit ")"]
--   Literals match but produce no term; refs produce terms
--   Result: TmCon "add" ["2", "3"]
--
-- For `type ::= "Type" | name`:
--   Both alternatives should produce a term when matched
--   Wrap in GNode so alternatives produce terms
wrapInNode :: String -> GrammarExpr () -> GrammarExpr ()
wrapInNode name gexpr = case gexpr of
  GRef _ -> gexpr          -- Pure reference: forward
  GNode _ _ -> gexpr       -- Already a node
  GAlt _ _ -> 
    -- For alternatives containing literals, wrap in node so literal matches produce terms
    if hasLitInAlt gexpr
    then GNode name [wrapLitsInAlt gexpr]
    else gexpr
  _ -> let parts = flattenSeq gexpr
       in if any isRef parts
          then GNode name parts  -- Has refs: wrap in node
          else gexpr             -- No refs: just literals, no node
  where
    isRef (GRef _) = True
    isRef _ = False

-- | Check if alternative contains any GLit
hasLitInAlt :: GrammarExpr () -> Bool
hasLitInAlt (GAlt g1 g2) = hasLitInAlt g1 || hasLitInAlt g2
hasLitInAlt (GLit _) = True
hasLitInAlt _ = False

-- | Wrap literals in alternatives with GNode so they produce terms
wrapLitsInAlt :: GrammarExpr () -> GrammarExpr ()
wrapLitsInAlt (GAlt g1 g2) = GAlt (wrapLitsInAlt g1) (wrapLitsInAlt g2)
wrapLitsInAlt (GLit s) = GNode s []  -- Nullary node produces TmCon s []
wrapLitsInAlt g = g  -- Refs already produce terms

-- | Flatten GSeq to list
flattenSeq :: GrammarExpr () -> [GrammarExpr ()]
flattenSeq (GSeq g1 g2) = flattenSeq g1 ++ flattenSeq g2
flattenSeq GEmpty = []
flattenSeq g = [g]

-- | Extract grammar from lang body (which contains pieces)
extractLangBodyGrammar :: String -> Term -> [(String, GrammarExpr ())]
extractLangBodyGrammar _langName (TmCon "seq" items) = 
  concatMap extractLangItem items
extractLangBodyGrammar _langName item = extractLangItem item

extractLangItem :: Term -> [(String, GrammarExpr ())]
extractLangItem (TmCon "DPiece" (nameT : prods)) =
  let pieceName = case nameT of
        TmVar n -> n
        TmLit n -> n
        _ -> "unknown"
  in extractGrammarProds pieceName prods
extractLangItem (TmCon "seq" ts) = concatMap extractLangItem ts
extractLangItem _ = []

-- | Convert Term representation of grammar to GrammarExpr
termToGrammarExpr :: Term -> GrammarExpr ()
termToGrammarExpr (TmVar s) = GRef s
termToGrammarExpr (TmLit s) = GLit s
termToGrammarExpr (TmCon "alt" [g1, _, g2]) = GAlt (termToGrammarExpr g1) (termToGrammarExpr g2)
termToGrammarExpr (TmCon "alt" [g1, g2]) = GAlt (termToGrammarExpr g1) (termToGrammarExpr g2)
termToGrammarExpr (TmCon "alt" gs) = foldr1 GAlt (map termToGrammarExpr gs)
termToGrammarExpr (TmCon "seq" gs) = foldr GSeq GEmpty (map termToGrammarExpr gs)
termToGrammarExpr (TmCon "star" [g]) = GStar (termToGrammarExpr g)
termToGrammarExpr (TmCon "star" gs) = GStar (foldr GSeq GEmpty (map termToGrammarExpr gs))
termToGrammarExpr (TmCon "bind" [TmVar x, g]) = GBind x (termToGrammarExpr g)
termToGrammarExpr (TmCon "bind" [TmLit x, g]) = GBind x (termToGrammarExpr g)
termToGrammarExpr (TmCon "node" [TmVar n]) = GNode n []
termToGrammarExpr (TmCon "node" [TmLit n]) = GNode n []
termToGrammarExpr (TmCon "node" (TmVar n : gs)) = GNode n (map termToGrammarExpr gs)
termToGrammarExpr (TmCon "node" (TmLit n : gs)) = GNode n (map termToGrammarExpr gs)
termToGrammarExpr (TmCon "ref" [TmVar r]) = GRef r
termToGrammarExpr (TmCon "ref" [TmLit r]) = GRef r
termToGrammarExpr (TmCon "lit" [TmVar l]) = GLit l
termToGrammarExpr (TmCon "lit" [TmLit l]) = GLit l
termToGrammarExpr (TmCon "cut" [g]) = GCut (termToGrammarExpr g)
termToGrammarExpr (TmCon "empty" []) = GEmpty
termToGrammarExpr (TmCon "any" []) = GAny
-- Fallback: treat as literal
termToGrammarExpr (TmCon c []) = GLit c
termToGrammarExpr _ = GEmpty