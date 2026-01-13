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
    -- Special token types: "identifier"/"ident", "digits", "string", "chars", "constructor", "patvar", "anglevar"
    -- These set both bsBinds (for backward compatibility) and bsTerm (for GNode arg collection)
    go (GNode con []) st = case bsMode st of
      Parse -> case con of
        -- Match identifier token
        -- <ident> rejects reserved words (TReserved).
        --
        -- Soft keywords (TKeyword) are allowed as identifiers to avoid breaking
        -- contexts where a word-like token can be both a keyword and an ident.
        _ | con `elem` ["identifier", "ident"] -> case bsTokens st of
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
        -- Print metavariable: TmVar "$x" → "$" "x"
        "metavar" -> case bsTerm st of
          Just (TmVar ('$':s)) ->
            [st { bsTokens = bsTokens st ++ [TSym "$", TIdent s]
                , bsTerm = Nothing }]
          _ -> []
        -- Print literal identifier: TmLit s → ident
        "litident" -> case bsTerm st of
          Just (TmLit s) ->
            [st { bsTokens = bsTokens st ++ [TIdent s]
                , bsTerm = Nothing }]
          _ -> []
        -- Print newline: TmCon "newline" [] → newline
        "newline" -> case bsTerm st of
          Just (TmCon "newline" []) ->
            [st { bsTokens = bsTokens st ++ [TNewline]
                , bsTerm = Nothing }]
          _ -> []
        -- Print indent: TmCon "indent" [TmLit n] → indent
        "indent" -> case bsTerm st of
          Just (TmCon "indent" [TmLit n]) ->
            [st { bsTokens = bsTokens st ++ [TIndent (read n)]
                , bsTerm = Nothing }]
          _ -> []
        -- Print char literal: TmChar s → 'char'
        "char" -> case bsTerm st of
          Just (TmChar s) ->
            [st { bsTokens = bsTokens st ++ [TChar s]
                , bsTerm = Nothing }]
          _ -> []
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
        [st1 { bsTerm = Just (TmCon con argTerms)
             , bsBinds = popScope (bsBinds st1) }]
      Print -> case bsTerm st of
        Just (TmCon c subterms) | c == con -> do
          -- Push scope, print each subterm, pop scope
          let st0 = st { bsBinds = pushScope (bsBinds st) }
          st1 <- foldMPrint (\s (g, t) -> go g (s { bsTerm = Just t })) 
                            st0 (zip args (subterms ++ repeat (TmCon "unit" [])))
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
    resolveRef :: String -> BiState Token Term -> Maybe (GrammarExpr ())
    resolveRef x st = case M.lookup x (bsGrammar st) of
      Just g  -> Just g
      Nothing -> 
        -- Try to find a qualified name that ends with .x
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
    -- Fold that collects bsTerm from each step
    foldMCollect :: (BiState Token Term -> GrammarExpr () -> [BiState Token Term]) 
                 -> BiState Token Term -> [GrammarExpr ()] -> [(BiState Token Term, [Term])]
    foldMCollect _ s [] = [(s, [])]
    foldMCollect f s (x:xs) = do
      s' <- f s x
      let term = fromMaybeT (TmCon "unit" []) (bsTerm s')
      (s'', terms) <- foldMCollect f (s' { bsTerm = Nothing }) xs
      [(s'', term : terms)]
    
    -- Fold for printing (doesn't collect)
    foldMPrint :: (BiState Token Term -> a -> [BiState Token Term]) 
               -> BiState Token Term -> [a] -> [BiState Token Term]
    foldMPrint _ s [] = [s]
    foldMPrint f s (x:xs) = f s x >>= \s' -> foldMPrint f s' xs
    
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
builtinGrammar "name" = Just $ GAny  -- Match any identifier token
builtinGrammar "nat" = Just $ GAny   -- Match any number token
builtinGrammar _ = Nothing

-- | Find a grammar entry where the key ends with ".x"
-- Used to resolve unqualified references like "term" to "Universe.term"
findSuffixedGrammar :: String -> M.Map String (GrammarExpr ()) -> Maybe (GrammarExpr ())
findSuffixedGrammar x m = 
  let suffix = "." ++ x
      matches = [g | (k, g) <- M.toList m, suffix `isSuffixOf` k]
  in case matches of
       (g:_) -> Just g
       []    -> Nothing
  where
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

