{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
-- |
-- Module: Lego.Validation
-- Purpose: Semantic validation and optimization for .lego files
--
-- Detects errors that pass parsing but are semantically invalid:
--   - Undefined production references
--   - Duplicate production names
--   - Unbound variables in rule templates
--   - Conflicting rules (same pattern, different result)
--   - Left recursion (direct and indirect)
--   - Unused productions
--
-- Optimization warnings:
--   - Missing cut points (suggests where to add cuts)
--   - Unreachable alternatives in grammar
--   - Redundant alternatives
--   - Non-terminating rule cycles
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
    -- * Optimization checks
  , checkMissingCuts
  , checkRuleCycles
  , checkUnreachableAlts
    -- * Utilities
  , formatError
  , formatWarning
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate)
import Data.Maybe (fromMaybe, mapMaybe)

import Lego (Term, GrammarExpr, Rule(..))
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
  -- Optimization warnings
  | MissingCut String String               -- ^ production, keyword that should have cut
  | RuleCycle [String]                     -- ^ cycle of rule names
  | UnreachableAlt String Int              -- ^ production, alternative index
  | RedundantAlt String Int Int            -- ^ production, alt1, alt2 (alt2 shadows alt1)
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
  checkMissingCuts grammar <>
  checkUnreachableAlts grammar

-- | Validate rewrite rules
validateRules :: M.Map String (GrammarExpr ())
              -> [(String, Term, Term)]
              -> ValidationResult
validateRules _grammar rules =
  checkUnboundVars rules <>
  checkConflictingRules rules <>
  checkRuleCycles rules

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
    
    -- Extract direct left-recursive names
    directNames = [n | DirectLeftRecursion n <- directWarnings]
    
    -- Indirect cycles (that aren't direct)
    indirectWarnings =
      [ IndirectLeftRecursion cyc
      | (name, _) <- M.toList grammar
      , name `notElem` directNames
      , Just cyc <- [findCycle name]
      , length cyc > 1
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
-- Optimization Checks
---------------------------------------------------------------

-- | Check for missing cut points in grammar
--
-- A cut should follow keywords that uniquely identify a production.
-- This helps with error recovery - once we see "rule", commit to parsing a rule.
checkMissingCuts :: M.Map String (GrammarExpr ()) -> ValidationResult
checkMissingCuts grammar = 
  ValidationResult [] warnings
  where
    warnings = concatMap (uncurry checkProd) (M.toList grammar)
    
    checkProd :: String -> GrammarExpr () -> [ValidationWarning]
    checkProd prodName g = 
      let keywords = findLeadingKeywords g
          -- Only warn for keywords that aren't already followed by cut
          missingCuts = filter (not . hasFollowingCut g) keywords
      in [MissingCut prodName kw | kw <- missingCuts]
    
    -- Find keywords at the start of a production (or alternatives)
    findLeadingKeywords :: GrammarExpr () -> [String]
    findLeadingKeywords g = case g of
      GLit kw | isKeywordLike kw -> [kw]
      GAlt g1 g2     -> findLeadingKeywords g1 ++ findLeadingKeywords g2
      GSeq g1 _      -> findLeadingKeywords g1
      GBind _ g1     -> findLeadingKeywords g1
      _              -> []
    
    -- Check if a keyword is already followed by a cut
    hasFollowingCut :: GrammarExpr () -> String -> Bool
    hasFollowingCut g kw = case g of
      GSeq (GLit kw') (GCut _) | kw == kw' -> True
      GAlt g1 g2 -> hasFollowingCut g1 kw || hasFollowingCut g2 kw
      GSeq g1 g2 -> hasFollowingCut g1 kw || hasFollowingCut g2 kw
      GBind _ g1 -> hasFollowingCut g1 kw
      GCut _ -> True  -- Already has cut
      _ -> False
    
    isKeywordLike s = not (null s) && all isAlphaLike s
    isAlphaLike c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['_'])

-- | Check for rule cycles (potential non-termination)
--
-- If rule A produces pattern that matches rule B, and B produces A,
-- we have a potential infinite loop.
checkRuleCycles :: [(String, Term, Term)] -> ValidationResult
checkRuleCycles rules =
  ValidationResult [] warnings
  where
    -- Build a graph: rule name -> set of rule names it might trigger
    -- A rule "triggers" another if its template matches the other's pattern head
    getHead :: Term -> Maybe String
    getHead t = case t of
      TmCon name _ -> Just name
      TmLit name   -> Just name
      _            -> Nothing
    
    -- Check if template could trigger rule with given head
    couldTrigger :: Term -> String -> Bool
    couldTrigger tpl head' = case tpl of
      TmCon name _ -> name == head'
      TmLit name   -> name == head'
      _            -> False
    
    -- Build adjacency: rule -> rules it might trigger
    edges = M.fromListWith S.union
      [ (name1, S.singleton name2)
      | (name1, _, tpl) <- rules
      , (name2, pat, _) <- rules
      , Just head' <- [getHead pat]
      , couldTrigger tpl head'
      ]
    
    -- Find cycles using DFS
    findCycles :: S.Set String -> [String] -> String -> [[String]]
    findCycles visited path node
      | node `S.member` visited = 
          if node `elem` path 
          then [reverse (node : takeWhile (/= node) path) ++ [node]]
          else []
      | otherwise =
          let neighbors = maybe [] S.toList (M.lookup node edges)
              visited' = S.insert node visited
              path' = node : path
          in concatMap (findCycles visited' path') neighbors
    
    allCycles = concatMap (findCycles S.empty []) (M.keys edges)
    -- Deduplicate cycles (same cycle can be found from different starting points)
    uniqueCycles = S.toList $ S.fromList (map (take 1) allCycles)
    
    warnings = [RuleCycle cyc | cyc <- uniqueCycles, length cyc > 1]

-- | Check for unreachable alternatives in grammar
--
-- If alternative A is a prefix of alternative B and comes first,
-- B will never be reached. Example: expr ::= "if" expr | "if" expr "else" expr
checkUnreachableAlts :: M.Map String (GrammarExpr ()) -> ValidationResult
checkUnreachableAlts grammar =
  ValidationResult [] warnings
  where
    warnings = concatMap (uncurry checkProd) (M.toList grammar)
    
    checkProd :: String -> GrammarExpr () -> [ValidationWarning]
    checkProd prodName g = 
      let alts = enumerateAlts g
          -- Check each pair of alternatives
          pairs = [(i, j, a1, a2) | (i, a1) <- alts, (j, a2) <- alts, i < j]
      in mapMaybe (checkPair prodName) pairs
    
    checkPair :: String -> (Int, Int, GrammarExpr (), GrammarExpr ()) -> Maybe ValidationWarning
    checkPair prodName (i, j, alt1, alt2)
      | alt1 `isPrefix` alt2 = Just (UnreachableAlt prodName j)
      | alt1 `structurallyEqual` alt2 = Just (RedundantAlt prodName i j)
      | otherwise = Nothing
    
    -- Enumerate alternatives with indices
    enumerateAlts :: GrammarExpr () -> [(Int, GrammarExpr ())]
    enumerateAlts g = zip [0..] (flattenAlts g)
    
    flattenAlts :: GrammarExpr () -> [GrammarExpr ()]
    flattenAlts g = case g of
      GAlt g1 g2 -> flattenAlts g1 ++ flattenAlts g2
      _ -> [g]
    
    -- Check if g1 is a prefix of g2 (g2 starts with g1)
    isPrefix :: GrammarExpr () -> GrammarExpr () -> Bool
    isPrefix g1 g2 = case (g1, g2) of
      (GLit s1, GLit s2) -> s1 == s2
      (GRef r1, GRef r2) -> r1 == r2
      (GSeq a1 b1, GSeq a2 b2) -> a1 `structurallyEqual` a2 && b1 `isPrefix` b2
      (_, GSeq a2 _) -> g1 `structurallyEqual` a2
      _ -> False
    
    -- Structural equality (ignoring annotations)
    structurallyEqual :: GrammarExpr () -> GrammarExpr () -> Bool
    structurallyEqual g1 g2 = case (g1, g2) of
      (GLit s1, GLit s2) -> s1 == s2
      (GRef r1, GRef r2) -> r1 == r2
      (GSeq a1 b1, GSeq a2 b2) -> a1 `structurallyEqual` a2 && b1 `structurallyEqual` b2
      (GAlt a1 b1, GAlt a2 b2) -> a1 `structurallyEqual` a2 && b1 `structurallyEqual` b2
      (GStar g1', GStar g2') -> g1' `structurallyEqual` g2'
      (GBind n1 g1', GBind n2 g2') -> n1 == n2 && g1' `structurallyEqual` g2'
      (GCut g1', GCut g2') -> g1' `structurallyEqual` g2'
      _ -> False

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
  -- Optimization warnings
  MissingCut prod kw ->
    "OPTIMIZE: Production '" ++ prod ++ "' could add cut after '" ++ kw ++ "' for better errors"
  RuleCycle cyc ->
    "WARNING: Potential non-terminating rule cycle: " ++ intercalate " -> " cyc
  UnreachableAlt prod idx ->
    "WARNING: Alternative " ++ show idx ++ " in '" ++ prod ++ "' is unreachable"
  RedundantAlt prod i j ->
    "WARNING: Alternatives " ++ show i ++ " and " ++ show j ++ " in '" ++ prod ++ "' are redundant"
