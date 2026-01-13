{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Lego Composition: Pushout with conflict detection and law verification
--
-- == Algebraic Laws
--
-- Language composition forms a commutative monoid:
--   Identity:     L ⊔ ∅ = L
--   Commutativity: L1 ⊔ L2 ≅ L2 ⊔ L1
--   Associativity: (L1 ⊔ L2) ⊔ L3 = L1 ⊔ (L2 ⊔ L3)
--
-- These laws are testable via the `law` declaration syntax.
--
-- == Conflict Detection
--
-- When composing languages, conflicts can arise:
--   - GrammarConflict: same production name, different definition
--   - RuleConflict: same pattern head, different template
--   - VocabConflict: overlapping keywords/symbols with different roles
--
module Lego.Composition
  ( -- * Conflict Types
    Conflict(..)
  , ConflictSeverity(..)
  , CompositionResult(..)
    -- * Pushout with Conflicts
  , composeGrammars
  , composeRules
  , composeVocab
  , composeFull
    -- * Conflict Formatting
  , formatConflict
  , formatConflicts
    -- * Law Verification
  , LawTest(..)
  , LawResult(..)
  , checkLaw
  , grammarEquiv
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (intercalate)

import Lego (GrammarExpr, Rule(..), pattern GEmpty, pattern GLit, pattern GSyntax,
             pattern GKeyword, pattern GNode, pattern GSeq, pattern GAlt, pattern GStar,
             pattern GRec, pattern GRef, pattern GBind, pattern GCut, pattern GAny)

--------------------------------------------------------------------------------
-- Conflict Types
--------------------------------------------------------------------------------

-- | Severity of a composition conflict
data ConflictSeverity
  = CriticalConflict   -- Must be resolved (same name, incompatible defs)
  | WarningConflict    -- Might be intentional (shadowing)
  | InfoConflict       -- Informational (duplicate but identical)
  deriving (Eq, Show, Ord)

-- | A conflict that arose during composition
data Conflict
  = GrammarConflict
    { gcProdName :: String
    , gcLeft     :: GrammarExpr ()
    , gcRight    :: GrammarExpr ()
    , gcSeverity :: ConflictSeverity
    }
  | RuleConflict
    { rcRuleName :: String
    , rcLeft     :: Rule
    , rcRight    :: Rule
    , rcSeverity :: ConflictSeverity
    }
  | VocabConflict
    { vcWord     :: String
    , vcLeftRole :: String   -- "keyword" or "symbol"
    , vcRightRole :: String
    , vcSeverity :: ConflictSeverity
    }
  deriving (Show)

-- | Result of a composition operation
data CompositionResult a
  = Clean a                    -- No conflicts
  | WithConflicts a [Conflict] -- Succeeded but has conflicts
  | Failed [Conflict]          -- Critical conflicts, cannot proceed
  deriving (Show)

instance Functor CompositionResult where
  fmap f (Clean a) = Clean (f a)
  fmap f (WithConflicts a cs) = WithConflicts (f a) cs
  fmap _ (Failed cs) = Failed cs

--------------------------------------------------------------------------------
-- Grammar Composition
--------------------------------------------------------------------------------

-- | Compose two grammar maps with conflict detection
--
-- For each production name that appears in both:
--   - If definitions are equivalent: no conflict (merge)
--   - If definitions differ: GrammarConflict
--
-- Right-hand side wins on conflict (shadowing semantics).
composeGrammars :: M.Map String (GrammarExpr ()) 
                -> M.Map String (GrammarExpr ()) 
                -> CompositionResult (M.Map String (GrammarExpr ()))
composeGrammars g1 g2 = 
  let -- Find overlapping keys
      overlap = M.keysSet g1 `S.intersection` M.keysSet g2
      -- Check each overlap for conflicts
      conflicts = concatMap checkOverlap (S.toList overlap)
      -- Merge (right wins)
      merged = M.union g2 g1
  in case partition conflicts of
       ([], [])  -> Clean merged
       ([], ws)  -> WithConflicts merged ws
       (cs, ws)  -> if null cs then WithConflicts merged ws
                    else Failed (cs ++ ws)
  where
    checkOverlap name = 
      case (M.lookup name g1, M.lookup name g2) of
        (Just e1, Just e2)
          | grammarEquiv e1 e2 -> []  -- identical, no conflict
          | otherwise -> [GrammarConflict name e1 e2 CriticalConflict]
        _ -> []  -- shouldn't happen
    
    partition = foldr go ([], [])
      where
        go c (crits, warns) = case gcSeverity c of
          CriticalConflict -> (c:crits, warns)
          _ -> (crits, c:warns)

--------------------------------------------------------------------------------
-- Rule Composition
--------------------------------------------------------------------------------

-- | Compose rule lists with conflict detection
--
-- Rules with same name are conflicts unless identical.
-- Later rules shadow earlier ones.
composeRules :: [Rule] -> [Rule] -> CompositionResult [Rule]
composeRules rs1 rs2 =
  let -- Build name -> rule maps
      ruleMap1 = M.fromList [(ruleName r, r) | r <- rs1]
      ruleMap2 = M.fromList [(ruleName r, r) | r <- rs2]
      -- Find overlaps
      overlap = M.keysSet ruleMap1 `S.intersection` M.keysSet ruleMap2
      -- Check conflicts
      checkOverlap name =
        case (M.lookup name ruleMap1, M.lookup name ruleMap2) of
          (Just r1, Just r2)
            | ruleEquiv r1 r2 -> []
            | otherwise -> [RuleConflict name r1 r2 WarningConflict]
          _ -> []
      conflicts = concatMap checkOverlap (S.toList overlap)
      -- Merge (later rules come after, effective shadowing via order)
      merged = rs1 ++ rs2
      hasCritical = any (\case RuleConflict _ _ _ CriticalConflict -> True; _ -> False)
  in case hasCritical conflicts of
       True  -> Failed conflicts
       False -> if null conflicts 
                then Clean merged 
                else WithConflicts merged conflicts

-- | Check if two rules are equivalent
ruleEquiv :: Rule -> Rule -> Bool
ruleEquiv r1 r2 = 
  ruleName r1 == ruleName r2 &&
  rulePattern r1 == rulePattern r2 &&
  ruleTemplate r1 == ruleTemplate r2

--------------------------------------------------------------------------------
-- Vocab Composition
--------------------------------------------------------------------------------

-- | Compose vocabulary sets with conflict detection
--
-- Keywords and symbols can conflict if same word has different roles.
composeVocab :: S.Set String  -- keywords1
             -> S.Set String  -- symbols1
             -> S.Set String  -- keywords2
             -> S.Set String  -- symbols2
             -> CompositionResult (S.Set String, S.Set String)
composeVocab kw1 sym1 kw2 sym2 =
  let -- Check cross-conflicts: keyword in one, symbol in other
      kwInSym = S.intersection kw1 sym2
      symInKw = S.intersection sym1 kw2
      conflicts = 
        [VocabConflict w "keyword" "symbol" WarningConflict | w <- S.toList kwInSym] ++
        [VocabConflict w "symbol" "keyword" WarningConflict | w <- S.toList symInKw]
      -- Merge
      mergedKw = S.union kw1 kw2
      mergedSym = S.union sym1 sym2
  in if null conflicts
     then Clean (mergedKw, mergedSym)
     else WithConflicts (mergedKw, mergedSym) conflicts

--------------------------------------------------------------------------------
-- Full Composition
--------------------------------------------------------------------------------

-- | Full language composition with all conflict types
composeFull :: (M.Map String (GrammarExpr ()), [Rule], S.Set String, S.Set String)
            -> (M.Map String (GrammarExpr ()), [Rule], S.Set String, S.Set String)
            -> CompositionResult (M.Map String (GrammarExpr ()), [Rule], S.Set String, S.Set String)
composeFull (g1, r1, kw1, sym1) (g2, r2, kw2, sym2) =
  let gramRes = composeGrammars g1 g2
      ruleRes = composeRules r1 r2
      vocabRes = composeVocab kw1 sym1 kw2 sym2
  in combineResults gramRes ruleRes vocabRes
  where
    combineResults (Failed cs) _ _ = Failed cs
    combineResults _ (Failed cs) _ = Failed cs
    combineResults _ _ (Failed cs) = Failed cs
    combineResults (Clean g) (Clean r) (Clean (kw, sym)) = 
      Clean (g, r, kw, sym)
    combineResults gr rr vr = 
      let allConflicts = getConflicts gr ++ getRuleConflicts rr ++ getVocabConflicts vr
          g = getGrammar gr
          r = getRules rr
          (kw, sym) = getVocab vr
      in WithConflicts (g, r, kw, sym) allConflicts
    
    getGrammar (Clean x) = x
    getGrammar (WithConflicts x _) = x
    getGrammar (Failed _) = M.empty
    
    getRules (Clean x) = x
    getRules (WithConflicts x _) = x
    getRules (Failed _) = []
    
    getVocab (Clean x) = x
    getVocab (WithConflicts x _) = x
    getVocab (Failed _) = (S.empty, S.empty)
    
    getConflicts (WithConflicts _ cs) = cs
    getConflicts (Clean _) = []
    getConflicts (Failed cs) = cs
    
    getRuleConflicts (WithConflicts _ cs) = cs
    getRuleConflicts (Clean _) = []
    getRuleConflicts (Failed cs) = cs
    
    getVocabConflicts (WithConflicts _ cs) = cs
    getVocabConflicts (Clean _) = []
    getVocabConflicts (Failed cs) = cs

--------------------------------------------------------------------------------
-- Conflict Formatting
--------------------------------------------------------------------------------

-- | Format a single conflict for display
formatConflict :: Conflict -> String
formatConflict (GrammarConflict name e1 e2 sev) =
  severityPrefix sev ++ "Grammar conflict on '" ++ name ++ "':\n" ++
  "  Left:  " ++ show e1 ++ "\n" ++
  "  Right: " ++ show e2
formatConflict (RuleConflict name r1 r2 sev) =
  severityPrefix sev ++ "Rule conflict on '" ++ name ++ "':\n" ++
  "  Left:  " ++ show (rulePattern r1) ++ " ~> " ++ show (ruleTemplate r1) ++ "\n" ++
  "  Right: " ++ show (rulePattern r2) ++ " ~> " ++ show (ruleTemplate r2)
formatConflict (VocabConflict word role1 role2 sev) =
  severityPrefix sev ++ "Vocab conflict on '" ++ word ++ "': " ++
  role1 ++ " vs " ++ role2

severityPrefix :: ConflictSeverity -> String
severityPrefix CriticalConflict = "ERROR: "
severityPrefix WarningConflict = "WARNING: "
severityPrefix InfoConflict = "INFO: "

-- | Format multiple conflicts
formatConflicts :: [Conflict] -> String
formatConflicts [] = "No conflicts"
formatConflicts cs = intercalate "\n\n" (map formatConflict cs)

--------------------------------------------------------------------------------
-- Grammar Equivalence
--------------------------------------------------------------------------------

-- | Check if two grammar expressions are structurally equivalent
grammarEquiv :: GrammarExpr () -> GrammarExpr () -> Bool
grammarEquiv GEmpty GEmpty = True
grammarEquiv (GLit s1) (GLit s2) = s1 == s2
grammarEquiv (GSyntax s1) (GSyntax s2) = s1 == s2
grammarEquiv (GKeyword s1) (GKeyword s2) = s1 == s2
grammarEquiv (GRef s1) (GRef s2) = s1 == s2
grammarEquiv (GSeq a1 b1) (GSeq a2 b2) = grammarEquiv a1 a2 && grammarEquiv b1 b2
grammarEquiv (GAlt a1 b1) (GAlt a2 b2) = grammarEquiv a1 a2 && grammarEquiv b1 b2
grammarEquiv (GStar g1) (GStar g2) = grammarEquiv g1 g2
grammarEquiv (GRec x1 g1) (GRec x2 g2) = x1 == x2 && grammarEquiv g1 g2
grammarEquiv (GBind x1 g1) (GBind x2 g2) = x1 == x2 && grammarEquiv g1 g2
grammarEquiv (GCut g1) (GCut g2) = grammarEquiv g1 g2
grammarEquiv (GNode n1 gs1) (GNode n2 gs2) = 
  n1 == n2 && length gs1 == length gs2 && and (zipWith grammarEquiv gs1 gs2)
grammarEquiv GAny GAny = True
grammarEquiv _ _ = False

--------------------------------------------------------------------------------
-- Law Verification
--------------------------------------------------------------------------------

-- | A law to be tested
data LawTest
  = IdentityLeft String   -- (A + Empty) ≅ A
  | IdentityRight String  -- (Empty + A) ≅ A
  | Commutativity String String  -- (A + B) ≅ (B + A)
  | Associativity String String String  -- ((A+B)+C) ≅ (A+(B+C))
  deriving (Show)

-- | Result of checking a law
data LawResult
  = LawHolds
  | LawFails String  -- counterexample/reason
  deriving (Show)

-- | Check a composition law
-- Takes a resolver to look up language names
checkLaw :: (String -> Maybe (M.Map String (GrammarExpr ())))
         -> LawTest 
         -> LawResult
checkLaw resolve = \case
  IdentityLeft name -> case resolve name of
    Nothing -> LawFails $ "Unknown language: " ++ name
    Just g -> 
      let result = composeGrammars g M.empty
      in case result of
           Clean g' | grammarMapEquiv g g' -> LawHolds
           _ -> LawFails "Identity left failed"
  
  IdentityRight name -> case resolve name of
    Nothing -> LawFails $ "Unknown language: " ++ name
    Just g ->
      let result = composeGrammars M.empty g
      in case result of
           Clean g' | grammarMapEquiv g g' -> LawHolds
           _ -> LawFails "Identity right failed"
  
  Commutativity n1 n2 -> case (resolve n1, resolve n2) of
    (Just g1, Just g2) ->
      let ab = composeGrammars g1 g2
          ba = composeGrammars g2 g1
      in case (ab, ba) of
           (Clean gab, Clean gba) | grammarMapEquiv gab gba -> LawHolds
           (WithConflicts gab _, WithConflicts gba _) | grammarMapEquiv gab gba -> LawHolds
           _ -> LawFails "Commutativity failed"
    _ -> LawFails "Unknown language in commutativity test"
  
  Associativity n1 n2 n3 -> case (resolve n1, resolve n2, resolve n3) of
    (Just g1, Just g2, Just g3) ->
      -- (g1 + g2) + g3
      let ab = case composeGrammars g1 g2 of
                 Clean g -> g
                 WithConflicts g _ -> g
                 Failed _ -> M.empty
          abc_l = composeGrammars ab g3
          -- g1 + (g2 + g3)
          bc = case composeGrammars g2 g3 of
                 Clean g -> g
                 WithConflicts g _ -> g
                 Failed _ -> M.empty
          abc_r = composeGrammars g1 bc
      in case (abc_l, abc_r) of
           (Clean gl, Clean gr) | grammarMapEquiv gl gr -> LawHolds
           (WithConflicts gl _, WithConflicts gr _) | grammarMapEquiv gl gr -> LawHolds
           _ -> LawFails "Associativity failed"
    _ -> LawFails "Unknown language in associativity test"

-- | Check if two grammar maps are equivalent
grammarMapEquiv :: M.Map String (GrammarExpr ()) 
                -> M.Map String (GrammarExpr ()) 
                -> Bool
grammarMapEquiv m1 m2 =
  M.keysSet m1 == M.keysSet m2 &&
  all (\k -> case (M.lookup k m1, M.lookup k m2) of
               (Just e1, Just e2) -> grammarEquiv e1 e2
               _ -> False) (M.keys m1)
