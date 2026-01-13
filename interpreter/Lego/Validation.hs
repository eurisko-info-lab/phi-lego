{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
-- |
-- Module: Lego.Validation
-- Purpose: Semantic validation for .lego files
--
-- Detects errors that pass parsing but are semantically invalid:
--   - Undefined production references
--   - Duplicate production names
--   - Unbound variables in rule templates
--   - Conflicting rules (same pattern, different result)
--   - Left recursion (direct and indirect)
--   - Unused productions
--
-- Architecture: Pure validation functions, no IO.
-- Called after parsing, before evaluation.

module Lego.Validation
  ( -- * Validation types
    ValidationError(..)
  , ValidationWarning(..)
  , Severity(..)
  , ValidationResult(..)
    -- * Main validation
  , validate
  , validateGrammar
  , validateRules
    -- * Specific checks
  , checkUndefinedRefs
  , checkDuplicateProds
  , checkUnboundVars
  , checkConflictingRules
  , checkLeftRecursion
  , checkUnusedProds
    -- * Utilities
  , formatError
  , formatWarning
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

import Lego (Term, GrammarExpr)
import Lego (pattern GRef, pattern GSeq, pattern GAlt, pattern GStar, pattern GBind, pattern GCut, pattern GLit)
import Lego (pattern TmVar, pattern TmLit, pattern TmCon)
import Lego.Internal (Fix(..))

-- | Severity of validation issue
data Severity = Error | Warning | Info
  deriving (Show, Eq, Ord)

-- | Validation error (blocks execution)
data ValidationError
  = UndefinedProduction String String   -- ^ production, referenced from
  | DuplicateProduction String          -- ^ production name defined twice
  | UnboundVariable String String       -- ^ variable, rule name
  | CircularImport String               -- ^ module name
  | InvalidSyntax String String         -- ^ context, message
  deriving (Show, Eq)

-- | Validation warning (execution continues)
data ValidationWarning
  = ConflictingRules String String String  -- ^ rule1, rule2, reason
  | DirectLeftRecursion String             -- ^ production name
  | IndirectLeftRecursion [String]         -- ^ cycle path
  | UnusedProduction String                -- ^ production name
  | ShadowedProduction String String       -- ^ production, shadowed by
  | AmbiguousGrammar String String         -- ^ production, reason
  deriving (Show, Eq)

-- | Result of validation
data ValidationResult = ValidationResult
  { vrErrors   :: [ValidationError]
  , vrWarnings :: [ValidationWarning]
  } deriving (Show, Eq)

instance Semigroup ValidationResult where
  (ValidationResult e1 w1) <> (ValidationResult e2 w2) =
    ValidationResult (e1 ++ e2) (w1 ++ w2)

instance Monoid ValidationResult where
  mempty = ValidationResult [] []

-- | Main validation entry point
validate :: M.Map String (GrammarExpr ())  -- ^ Grammar productions
         -> [(String, Term, Term)]          -- ^ Rules (name, pattern, template)
         -> ValidationResult
validate grammar rules =
  validateGrammar grammar <> validateRules grammar rules

-- | Validate grammar definitions
validateGrammar :: M.Map String (GrammarExpr ()) -> ValidationResult
validateGrammar grammar =
  checkUndefinedRefs grammar <>
  checkDuplicateProds grammar <>
  checkLeftRecursion grammar <>
  checkUnusedProds grammar (S.empty)  -- No root hints

-- | Validate rewrite rules
validateRules :: M.Map String (GrammarExpr ())
              -> [(String, Term, Term)]
              -> ValidationResult
validateRules grammar rules =
  checkUnboundVars rules <>
  checkConflictingRules rules

---------------------------------------------------------------
-- Grammar Checks
---------------------------------------------------------------

-- | Check for undefined production references
checkUndefinedRefs :: M.Map String (GrammarExpr ()) -> ValidationResult
checkUndefinedRefs grammar = 
  ValidationResult errors []
  where
    -- Built-in productions that don't need explicit definition
    builtins = S.fromList ["nat", "int", "str", "string", "ident", "char", "float", "bool"]
    
    -- Extract base names (strip piece qualifier like "Term.expr" -> "expr")
    baseName :: String -> String
    baseName s = case break (== '.') s of
      (_, '.':rest) -> rest  -- Has qualifier, return part after dot
      _             -> s      -- No qualifier, return as-is
    
    -- Build set of defined names (both qualified and base forms)
    defined = M.keysSet grammar
    definedBase = S.map baseName defined  -- Set of base names
    
    -- Find all references in a grammar expression
    refs :: GrammarExpr () -> S.Set String
    refs g = case g of
      GRef name      -> S.singleton name
      GSeq g1 g2     -> refs g1 <> refs g2
      GAlt g1 g2     -> refs g1 <> refs g2
      GStar g1       -> refs g1
      GBind _ g1     -> refs g1
      GCut g1        -> refs g1
      _              -> S.empty
    
    -- All references from all productions
    allRefs = M.foldMapWithKey (\name g -> 
      S.map (\r -> (r, name)) (refs g)) grammar
    
    -- A reference is defined if:
    -- 1. It matches a defined name exactly, OR
    -- 2. Its base name matches any defined base name, OR
    -- 3. It's a built-in production
    isDefined ref = ref `S.member` defined || 
                    baseName ref `S.member` definedBase ||
                    baseName ref `S.member` builtins
    
    -- Undefined = referenced but not defined
    errors = [ UndefinedProduction ref from 
             | (ref, from) <- S.toList allRefs
             , not (isDefined ref)
             ]

-- | Check for duplicate production names (within same scope)
-- Note: Cross-piece duplicates are handled by composition conflict detection
checkDuplicateProds :: M.Map String (GrammarExpr ()) -> ValidationResult
checkDuplicateProds _grammar =
  -- Map already de-duplicates, so we can't detect this here
  -- Would need to check at parse time before map construction
  mempty

-- | Check for left recursion
checkLeftRecursion :: M.Map String (GrammarExpr ()) -> ValidationResult
checkLeftRecursion grammar =
  ValidationResult [] (directWarnings ++ indirectWarnings)
  where
    -- Check if production has direct left recursion
    isDirectLeftRec :: String -> GrammarExpr () -> Bool
    isDirectLeftRec name g = case g of
      GRef ref     -> ref == name
      GSeq g1 _    -> isDirectLeftRec name g1  -- Check leftmost
      GAlt g1 g2   -> isDirectLeftRec name g1 || isDirectLeftRec name g2
      GStar g1     -> isDirectLeftRec name g1
      GBind _ g1   -> isDirectLeftRec name g1
      GCut g1      -> isDirectLeftRec name g1
      _            -> False
    
    directWarnings = 
      [ DirectLeftRecursion name
      | (name, g) <- M.toList grammar
      , isDirectLeftRec name g
      ]
    
    -- Find indirect left recursion via DFS
    -- Get the "first" set - productions reachable at the start
    firstSet :: String -> S.Set String
    firstSet name = case M.lookup name grammar of
      Nothing -> S.empty
      Just g  -> go S.empty g
      where
        go visited g' = case g' of
          GRef ref
            | ref `S.member` visited -> S.empty
            | otherwise -> S.insert ref (go (S.insert ref visited) 
                             (fromMaybe (GLit "") (M.lookup ref grammar)))
          GSeq g1 _ -> go visited g1
          GAlt g1 g2 -> go visited g1 <> go visited g2
          GStar g1 -> go visited g1
          GBind _ g1 -> go visited g1
          GCut g1 -> go visited g1
          _ -> S.empty
    
    -- Check for cycles: can we reach name from name's first set?
    findCycle :: String -> Maybe [String]
    findCycle start = go [start] (firstSet start)
      where
        go path candidates
          | start `S.member` candidates = Just (reverse path)
          | S.null candidates = Nothing
          | otherwise = 
              let next = S.foldl' (\acc n -> acc <> firstSet n) S.empty candidates
                  path' = if null (S.toList candidates) then path 
                         else head (S.toList candidates) : path
              in if S.null (next S.\\ S.fromList path)
                 then Nothing
                 else go path' (next S.\\ S.fromList path)
    
    -- Indirect cycles (that aren't direct)
    indirectWarnings =
      [ IndirectLeftRecursion cycle
      | (name, _) <- M.toList grammar
      , name `notElem` map (\(DirectLeftRecursion n) -> n) directWarnings
      , Just cycle <- [findCycle name]
      , length cycle > 1
      ]

-- | Check for unused productions (not reachable from roots)
checkUnusedProds :: M.Map String (GrammarExpr ()) -> S.Set String -> ValidationResult
checkUnusedProds grammar roots =
  ValidationResult [] warnings
  where
    defined = M.keysSet grammar
    
    -- Find reachable productions from a starting set
    reachable :: S.Set String -> S.Set String
    reachable starts = go starts starts
      where
        go acc frontier
          | S.null frontier = acc
          | otherwise =
              let refs = S.foldl' (\a n -> a <> refsIn n) S.empty frontier
                  newRefs = refs S.\\ acc
              in go (acc <> newRefs) newRefs
        
        refsIn name = case M.lookup name grammar of
          Nothing -> S.empty
          Just g  -> extractRefs g
        
        extractRefs g = case g of
          GRef name'     -> S.singleton name'
          GSeq g1 g2     -> extractRefs g1 <> extractRefs g2
          GAlt g1 g2     -> extractRefs g1 <> extractRefs g2
          GStar g1       -> extractRefs g1
          GBind _ g1     -> extractRefs g1
          GCut g1        -> extractRefs g1
          _              -> S.empty
    
    -- If no roots given, assume all are roots (no unused check)
    actualRoots = if S.null roots then defined else roots
    used = reachable actualRoots
    unused = defined S.\\ used
    
    warnings = map UnusedProduction (S.toList unused)

---------------------------------------------------------------
-- Rule Checks
---------------------------------------------------------------

-- | Check for unbound variables in rule templates
checkUnboundVars :: [(String, Term, Term)] -> ValidationResult
checkUnboundVars rules =
  ValidationResult errors []
  where
    -- Extract variables from a term
    varsIn :: Term -> S.Set String
    varsIn t = case t of
      TmVar v          -> S.singleton v
      TmCon _ args     -> S.unions (map varsIn args)
      _                -> S.empty
    
    -- Extract pattern variables (those starting with $)
    patternVars :: Term -> S.Set String
    patternVars t = case t of
      TmVar v 
        | "$" == take 1 v -> S.singleton v
        | otherwise       -> S.empty
      TmCon _ args -> S.unions (map patternVars args)
      _            -> S.empty
    
    -- Check each rule
    checkRule (ruleName, pat, template) =
      let patVars = patternVars pat
          tplVars = S.filter (\v -> "$" == take 1 v) (varsIn template)
          unbound = tplVars S.\\ patVars
      in [ UnboundVariable v ruleName | v <- S.toList unbound ]
    
    errors = concatMap checkRule rules

-- | Check for conflicting rules (same pattern, different result)
checkConflictingRules :: [(String, Term, Term)] -> ValidationResult
checkConflictingRules rules =
  ValidationResult [] warnings
  where
    -- Group rules by pattern structure (ignoring variable names)
    patternKey :: Term -> String
    patternKey t = case t of
      TmVar _        -> "_"
      TmLit s        -> show s
      TmCon name args -> "(" ++ name ++ " " ++ 
                        intercalate " " (map patternKey args) ++ ")"
      _              -> "_"
    
    -- Find rules with same pattern
    grouped = foldr (\(name, pat, tpl) m -> 
      M.insertWith (++) (patternKey pat) [(name, pat, tpl)] m) 
      M.empty rules
    
    -- Check groups with multiple rules
    checkGroup rs
      | length rs < 2 = []
      | otherwise = 
          let pairs = [(r1, r2) | r1 <- rs, r2 <- rs, fst3 r1 < fst3 r2]
          in [ ConflictingRules (fst3 r1) (fst3 r2) "same pattern structure"
             | (r1, r2) <- pairs
             , snd3 r1 /= snd3 r2  -- Different templates
             ]
      where
        fst3 (a,_,_) = a
        snd3 (_,_,c) = c
    
    warnings = concatMap checkGroup (M.elems grouped)

---------------------------------------------------------------
-- Formatting
---------------------------------------------------------------

-- | Format an error for display
formatError :: ValidationError -> String
formatError = \case
  UndefinedProduction ref from ->
    "ERROR: Undefined production '" ++ ref ++ "' referenced from '" ++ from ++ "'"
  DuplicateProduction name ->
    "ERROR: Duplicate production '" ++ name ++ "'"
  UnboundVariable var rule ->
    "ERROR: Unbound variable '" ++ var ++ "' in rule '" ++ rule ++ "'"
  CircularImport modName ->
    "ERROR: Circular import of '" ++ modName ++ "'"
  InvalidSyntax ctx msg ->
    "ERROR: Invalid syntax in " ++ ctx ++ ": " ++ msg

-- | Format a warning for display
formatWarning :: ValidationWarning -> String
formatWarning = \case
  ConflictingRules r1 r2 reason ->
    "WARNING: Conflicting rules '" ++ r1 ++ "' and '" ++ r2 ++ "': " ++ reason
  DirectLeftRecursion name ->
    "WARNING: Direct left recursion in production '" ++ name ++ "'"
  IndirectLeftRecursion path ->
    "WARNING: Indirect left recursion: " ++ intercalate " -> " path
  UnusedProduction name ->
    "WARNING: Unused production '" ++ name ++ "'"
  ShadowedProduction name by ->
    "WARNING: Production '" ++ name ++ "' shadowed by '" ++ by ++ "'"
  AmbiguousGrammar name reason ->
    "WARNING: Ambiguous grammar for '" ++ name ++ "': " ++ reason
