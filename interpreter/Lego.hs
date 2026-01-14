{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Lego: A minimal language for building languages
--
-- The 5 pieces: Name, Graph, Grammar, Rule, Lang
-- The 3 operations: Pushout (⊔), Fold, Fix (μ)
module Lego
  ( -- * The 5 Pieces
    Name(..)
  , Graph(..), GId, Port, emptyGraph, addNode, addEdge, (<>)
  , GrammarExpr, pattern GEmpty, pattern GLit, pattern GRegex, pattern GChar, pattern GNode
  , pattern GSeq, pattern GAlt, pattern GStar, pattern GRec, pattern GRef
  , pattern GBind, pattern GCut, pattern GVar, pattern GAny
  , glit, gseq, galt, gstar, grec, gbind, gcut, gnode, gempty
  , Rule(..), RuleDir(..)
  , mkRule, flipRule, canForward, canBackward
  , patternName, isPatVar, patVarName
  , Lang(..), LangF(..), emptyLang
  , CompiledLang, mkCompiledLang, emptyCompiled, renameLang
  , addImport, addImports, addTest, addTests, addLaw, addInherit, addAutocut
  , addVocab, addGrammar, addRule
  , clName, clVocab, clGrammar, clRules, clTests, clLaws, clImports, clInherits, clAutocuts
  , TypeRule(..)
  , LegoDecl(..)
  , Law(..)
    -- * The 3 Operations
  , poGraph, poLang, poLangChecked
  , LangConflict(..), formatConflicts
  , foldLang
  , fix
    -- * Bidirectional Grammar (Modal Interpretation)
  , Mode(..), BiState(..), BiResult(..)
  , runBiGrammar, biParse, biPrint, biCheck
  , emptyBiState
  , lookupBind, insertBind, pushScope, popScope, flattenBinds
    -- * Base Expression Functor (Common Algebra)
  , Fix(..), cata, ana
  , ExprF(..), SubstF(..), KleeneF(..), BindF(..), AnyF(..)
  , (:+:)(..)
  , GrammarF
    -- * Evaluation
  , Term, pattern TmVar, pattern TmCon, pattern TmLit, pattern TmRegex, pattern TmChar
    -- * Cubical primitives
  , pattern TmInterval, pattern TmI0, pattern TmI1
  , pattern TmPathType, pattern TmPathAbs, pattern TmPathApp
    -- * Composition operations
  , pattern TmComp, pattern TmHComp, pattern TmTransp
  , normalize, normalizeDir
  , normalizeTrace, normalizeTraceDir
  , TraceStep(..), formatTrace
  , matchPat
  , applyTemplate
  , builtinStep
  , substTerm

    -- * Testing
  , Test(..)
  , TestResult(..)
  , runTest
  , runTests
  , matchTerms
    -- * Enhanced testing
  , TestSpec(..), TestExpect(..), TestOpts(..)
  , TestResultE(..)
  , defaultOpts, testToSpec, runTestSpec
  , (.&&.), (.||.), expectNot   -- Boolean combinators
  
    -- * Located terms
  , LocTerm, mkLocTerm, unLocTerm, termLoc
  
    -- * Error handling
  , module Lego.Error
  ) where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Control.Applicative ((<|>))
import Control.Monad (foldM)

-- Re-export error types
import Lego.Error

-- Re-export from Internal (breaks circular deps)
import Lego.Internal (Fix(..), cata, ana, ExprF(..),
                      Term(..), pattern TmVar, pattern TmCon, pattern TmLit, pattern TmRegex, pattern TmChar,
                      pattern TmInterval, pattern TmI0, pattern TmI1,
                      pattern TmPathType, pattern TmPathAbs, pattern TmPathApp,
                      pattern TmComp, pattern TmHComp, pattern TmTransp)
-- Re-export from Builtins
import Lego.Builtins (builtinStep, substTerm)

--------------------------------------------------------------------------------
-- Located Terms
--------------------------------------------------------------------------------

-- | A term with optional source location
type LocTerm = Located Term

-- | Create a located term
mkLocTerm :: SrcSpan -> Term -> LocTerm
mkLocTerm s t = withLoc s t

-- | Extract the term, discarding location
unLocTerm :: LocTerm -> Term
unLocTerm = unLoc

-- | Get location from a located term
termLoc :: LocTerm -> Maybe SrcSpan
termLoc = getLoc

--------------------------------------------------------------------------------
-- PIECE 1: Name (Set)
--------------------------------------------------------------------------------

newtype Name = Name { unName :: String }
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------
-- PIECE 2: Graph (Monoid)
--------------------------------------------------------------------------------

type GId = Int
type Port = (GId, Int)  -- (node id, slot)

data Graph a = Graph
  { gNodes :: Map GId a        -- node id → label
  , gEdges :: Set (Port, Port) -- wiring
  , gFresh :: GId              -- next fresh id
  } deriving (Eq, Show, Functor)

emptyGraph :: Graph a
emptyGraph = Graph M.empty S.empty 0

addNode :: a -> Graph a -> (GId, Graph a)
addNode label g = 
  let nid = gFresh g
  in (nid, g { gNodes = M.insert nid label (gNodes g)
             , gFresh = nid + 1 })

addEdge :: Port -> Port -> Graph a -> Graph a
addEdge p1 p2 g = g { gEdges = S.insert (p1, p2) (gEdges g) }

-- | Monoid: disjoint union with node renumbering
instance Semigroup (Graph a) where
  g1 <> g2 = 
    let shift = gFresh g1
        nodes2 = M.mapKeys (+ shift) (gNodes g2)
        edges2 = S.map (\((n1,s1),(n2,s2)) -> ((n1+shift,s1),(n2+shift,s2))) (gEdges g2)
    in Graph
      { gNodes = M.union (gNodes g1) nodes2
      , gEdges = S.union (gEdges g1) edges2
      , gFresh = gFresh g1 + gFresh g2
      }

instance Monoid (Graph a) where
  mempty = emptyGraph

-- | Pushout: composition with identification
poGraph :: Eq a => Graph a -> Graph a -> Graph a
poGraph = (<>)  -- For now, just disjoint union (full pushout needs shared subgraph)

--------------------------------------------------------------------------------
-- PIECE 3: Grammar (Free Algebra) - Now via Fix GrammarF
--------------------------------------------------------------------------------

-- GrammarExpr is defined below after Fix and the base functors.
-- Here we just have the smart constructors (which work with the pattern synonyms)

-- Smart constructors
gempty :: GrammarExpr a
gempty = GEmpty

glit :: String -> GrammarExpr a
glit = GLit

gnode :: String -> [GrammarExpr a] -> GrammarExpr a
gnode = GNode

gseq :: GrammarExpr a -> GrammarExpr a -> GrammarExpr a
gseq GEmpty g = g
gseq g GEmpty = g
gseq g1 g2 = GSeq g1 g2

galt :: GrammarExpr a -> GrammarExpr a -> GrammarExpr a
galt = GAlt

gstar :: GrammarExpr a -> GrammarExpr a
gstar = GStar

grec :: String -> GrammarExpr a -> GrammarExpr a
grec = GRec

gbind :: String -> GrammarExpr a -> GrammarExpr a
gbind = GBind

gcut :: GrammarExpr a -> GrammarExpr a
gcut = GCut

-- | Monoid: sequence (uses pattern synonyms)
instance Semigroup (GrammarExpr a) where
  (<>) = gseq

instance Monoid (GrammarExpr a) where
  mempty = GEmpty

--------------------------------------------------------------------------------
-- Bidirectional Grammar: Modal Interpretation
--------------------------------------------------------------------------------

-- | Mode: interpretation strategy for grammar
-- The KEY insight: same grammar, different behavior based on mode
--
--   Parse: consume tokens, produce AST
--   Print: consume AST, produce tokens  
--   Check: validate structure without transformation
data Mode = Parse | Print | Check
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | Bidirectional state: unified for all modes, parametric over token and binding types
--
-- The binding environment is a STACK of maps, implementing lexical scoping:
--   - Each GNode (with args) introduces a new scope (pushes a frame)
--   - GBind inserts only into the current (top) frame
--   - Lookups search the stack from top to bottom (nearest binding wins)
--
-- The memo field implements packrat-style memoization:
--   - Key: (production name, token position = length of remaining tokens)
--   - Value: list of resulting states (cached parse results)
-- Memo entry: (term result, tokens consumed, bindings snapshot)
-- Using simpler data to avoid recursive Eq instance
type MemoEntry bind = (Maybe Term, Int, [Map String bind])

data BiState tok bind = BiState
  { bsTokens   :: [tok]              -- remaining/produced tokens
  , bsBinds    :: [Map String bind]  -- scoped bindings (stack, head = innermost)
  , bsTerm     :: Maybe Term         -- current term (for Print mode)
  , bsMode     :: Mode               -- current interpretation mode
  , bsGrammar  :: Map String (GrammarExpr ())  -- grammar environment
  , bsMemo     :: Map (String, Int) [MemoEntry bind]  -- packrat memo table
  } deriving (Eq, Show)

-- | Lookup binding in scope stack (lexical: nearest enclosing scope wins)
lookupBind :: String -> [Map String bind] -> Maybe bind
lookupBind _ [] = Nothing
lookupBind x (frame:rest) = case M.lookup x frame of
  Just v  -> Just v
  Nothing -> lookupBind x rest

-- | Insert binding into current (top) scope
insertBind :: String -> bind -> [Map String bind] -> [Map String bind]
insertBind _ _ [] = []  -- shouldn't happen: always have at least one frame
insertBind x v (frame:rest) = M.insert x v frame : rest

-- | Push new scope
pushScope :: [Map String bind] -> [Map String bind]
pushScope frames = M.empty : frames

-- | Pop scope (drop innermost)
popScope :: [Map String bind] -> [Map String bind]
popScope [] = []  -- shouldn't happen
popScope (_:rest) = rest

-- | Flatten scopes to single map (for output: merges with outer first, inner wins)
flattenBinds :: [Map String bind] -> Map String bind
flattenBinds = foldr M.union M.empty  -- folds right so inner scopes shadow outer

-- | Bidirectional result
data BiResult tok bind
  = BiSuccess (BiState tok bind)   -- successful interpretation
  | BiFail String                  -- failure with message
  deriving (Eq, Show)

-- | Empty state for a given mode (starts with one empty scope)
emptyBiState :: Mode -> BiState tok bind
emptyBiState m = BiState [] [M.empty] Nothing m M.empty M.empty

-- | Run grammar in specified mode
-- This is the profunctor-style modal interpreter:
--   same grammar definition → different semantics per mode
runBiGrammar :: GrammarExpr a -> BiState String String -> [BiState String String]
runBiGrammar = go M.empty
  where
    go :: Map String (GrammarExpr a) -> GrammarExpr a -> BiState String String -> [BiState String String]
    
    -- Empty: always succeeds, no-op
    go _env GEmpty st = [st]
    
    -- Literal: match token in Parse mode, emit in Print mode
    go _env (GLit s) st = goLit s st
    
    -- Node: semantic marker for AST construction
    -- GNode introduces a new scope for its children
    go env (GNode con args) st = case bsMode st of
      Parse -> do
        -- Push scope, parse all args, pop scope, construct term
        let st0 = st { bsBinds = pushScope (bsBinds st) }
        st' <- foldM (\s g -> go env g s) st0 args
        [st' { bsTerm = Just (TmCon con [])
             , bsBinds = popScope (bsBinds st') }]
      Print -> case bsTerm st of
        Just (TmCon c subterms) | c == con -> do
          -- Push scope, print each subterm, pop scope
          let st0 = st { bsBinds = pushScope (bsBinds st) }
          st' <- foldM (\s (g, t) -> go env g (s { bsTerm = Just t })) 
                       st0 (zip args (subterms ++ repeat (TmCon "unit" [])))
          [st' { bsTerm = Nothing, bsBinds = popScope (bsBinds st') }]
        _ -> []  -- mismatch
      Check -> do
        let st0 = st { bsBinds = pushScope (bsBinds st) }
        st' <- foldM (\s g -> go env g s) st0 args
        [st' { bsBinds = popScope (bsBinds st') }]
    
    -- Sequence: chain interpretations
    go env (GSeq g1 g2) st = do
      st1 <- go env g1 st
      go env g2 st1
    
    -- Alternative: try both branches
    go env (GAlt g1 g2) st = go env g1 st ++ go env g2 st
    
    -- Kleene star: zero or more
    go env (GStar g) st = st : do  -- empty case first
      st1 <- go env g st
      guard (st1 /= st)  -- must make progress
      go env (GStar g) st1
    
    -- Recursion: bind name and recurse
    go env (GRec x g) st = go (M.insert x g env) g st
    
    -- Reference: lookup and interpret
    go env (GRef x) st = case M.lookup x env of
      Just g  -> go env g st
      Nothing -> []  -- undefined reference
    
    -- Bind: capture identifier (into current scope only)
    go env (GBind x g) st = case bsMode st of
      Parse -> do
        st1 <- go env g st
        -- Capture from consumed tokens into current scope
        case bsTokens st of
          (t:_) -> [st1 { bsBinds = insertBind x t (bsBinds st1) }]
          _ -> [st1]
      Print -> do
        st1 <- go env g st
        case lookupBind x (bsBinds st) of
          Just v  -> [st1 { bsTokens = bsTokens st1 ++ [v] }]
          Nothing -> [st1]
      Check -> go env g st
    
    -- Variable: use captured value (lexical lookup)
    go _env (GVar x) st = case bsMode st of
      Parse -> case lookupBind x (bsBinds st) of
        Just _  -> [st]
        Nothing -> []  -- unbound variable
      Print -> case lookupBind x (bsBinds st) of
        Just v  -> [st { bsTokens = bsTokens st ++ [v] }]
        Nothing -> []
      Check -> [st]
    
    -- Any: match any single token (insert into current scope)
    go _env GAny st = case bsMode st of
      Parse -> case bsTokens st of
        (t:ts) -> [st { bsTokens = ts, bsBinds = insertBind "_" t (bsBinds st) }]
        _ -> []
      Print -> [st]  -- no-op in print mode
      Check -> [st]
    
    -- Regex: match regex pattern
    go _env (GRegex _pat) st = case bsMode st of
      Parse -> case bsTokens st of
        (t:ts) -> [st { bsTokens = ts, bsTerm = Just (TmLit t) }]  -- TODO: regex match
        _ -> []
      Print -> [st]  -- TODO: regex print
      Check -> [st]
    
    -- Char: match single character class
    go _env (GChar _cls) st = case bsMode st of
      Parse -> case bsTokens st of
        (t:ts) -> [st { bsTokens = ts, bsTerm = Just (TmLit t) }]  -- TODO: char class match
        _ -> []
      Print -> [st]  -- TODO: char print
      Check -> [st]
    
    -- Literal helper: unified handling for GLit
    goLit :: String -> BiState String String -> [BiState String String]
    goLit s st = case bsMode st of
      Parse -> case bsTokens st of
        (t:ts) | t == s -> [st { bsTokens = ts }]
        _ -> []  -- no match
      Print -> [st { bsTokens = bsTokens st ++ [s] }]
      Check -> [st]
    
    -- Helper for Kleene star
    guard True = [()]
    guard False = []
    
    _foldMList _ z [] = [z]
    _foldMList f z (x:xs) = f z x >>= \z' -> _foldMList f z' xs

-- | Parse helper: interpret grammar in Parse mode
biParse :: GrammarExpr a -> [String] -> [(Term, [String])]
biParse g toks = 
  [ (fromMaybe (TmCon "unit" []) (bsTerm st), bsTokens st)
  | st <- runBiGrammar g initSt ]
  where
    initSt :: BiState String String
    initSt = BiState toks [M.empty] Nothing Parse M.empty M.empty
    fromMaybe d Nothing = d
    fromMaybe _ (Just x) = x

-- | Print helper: interpret grammar in Print mode
biPrint :: GrammarExpr a -> Term -> Map String String -> [String]
biPrint g term binds = 
  case runBiGrammar g initSt of
    (st:_) -> bsTokens st
    []     -> []
  where
    initSt :: BiState String String
    initSt = BiState [] [binds] (Just term) Print M.empty M.empty

-- | Check helper: interpret grammar in Check mode  
biCheck :: GrammarExpr a -> BiState String String -> Bool
biCheck g st = not (null (runBiGrammar g (st { bsMode = Check })))

--------------------------------------------------------------------------------
-- PIECE 4: Rule (Rewrite) - Pattern and Template via Fix
--------------------------------------------------------------------------------

-- Pattern and Template are defined below after Fix.
-- Here we just have helpers that work with pattern synonyms.

-- | Extract the name from a pattern term
--   Pattern variables have $ prefix: $x, $foo
--   Returns the constructor name, literal, or variable name
patternName :: Term -> String
patternName (TmCon c _) = c
patternName (TmLit s) = s
patternName (TmVar x) = x
patternName (TmRegex s) = s  -- regex pattern
patternName (TmChar s) = s  -- char class
patternName TmInterval = "I"
patternName TmI0 = "i0"
patternName TmI1 = "i1"
patternName (TmPathType _ _ _) = "Path"
patternName (TmPathAbs _ _) = "λ"
patternName (TmPathApp _ _) = "@"
patternName (TmComp _ _ _ _) = "comp"
patternName (TmHComp _ _ _ _) = "hcomp"
patternName (TmTransp _ _ _) = "transp"

-- | Check if a term is a pattern variable (has $ prefix)
isPatVar :: Term -> Bool
isPatVar (TmVar ('$':_)) = True
isPatVar _ = False

-- | Get the variable name from a pattern variable (strips $ prefix)
patVarName :: Term -> Maybe String
patVarName (TmVar ('$':x)) = Just x
patVarName _ = Nothing

-- | Rule direction: which way(s) can the rule fire?
-- Forms a lattice: Both ⊑ Forward, Both ⊑ Backward
data RuleDir
  = Forward   -- ~>  : L → R only (reduction)
  | Backward  -- <~  : R → L only (expansion)  
  | Both      -- <~> : isomorphism (either direction)
  deriving (Eq, Show)

data Rule = Rule
  { ruleName     :: String
  , rulePattern  :: Term      -- Pattern uses $ prefix for variables
  , ruleTemplate :: Term      -- Template uses $ for substitution targets
  , ruleGuard    :: Maybe Term
  , ruleDir      :: RuleDir   -- Direction: Forward, Backward, or Both
  } deriving (Eq, Show)

-- | A single step in a normalization trace
data TraceStep = TraceStep
  { tsRule     :: String           -- Rule name that fired
  , tsBefore   :: Term             -- Term before reduction
  , tsAfter    :: Term             -- Term after reduction
  , tsBindings :: Map String Term  -- Pattern bindings
  , tsLocation :: Maybe SrcSpan    -- Source location of the redex (if tracked)
  } deriving (Eq, Show)

-- | Smart constructor for forward rule (default)
mkRule :: String -> Term -> Term -> Rule
mkRule name pat templ = Rule name pat templ Nothing Forward

-- | Flip a rule's direction (for backward application)
flipRule :: Rule -> Rule
flipRule r = r { rulePattern = ruleTemplate r
               , ruleTemplate = rulePattern r
               }

-- | Can this rule fire forward (L → R)?
canForward :: RuleDir -> Bool
canForward Forward = True
canForward Both = True
canForward Backward = False

-- | Can this rule fire backward (R → L)?
canBackward :: RuleDir -> Bool
canBackward Backward = True
canBackward Both = True
canBackward Forward = False

--------------------------------------------------------------------------------
-- PIECE 5: Lang (Initial Algebra)
--------------------------------------------------------------------------------

-- | Language functor: the shape of a language definition
-- This is the core algebraic structure. Runtime uses Lang () for concrete languages.
data LangF a l = LangF
  { lfName     :: String
  , lfVocab    :: Set String           -- keywords + symbols
  , lfGrammar  :: Map String (GrammarExpr a)  -- production name → grammar
  , lfRules    :: [Rule]
  , lfTypes    :: [TypeRule]           -- typing judgements
  , lfExtends  :: [l]                  -- base languages (recursive)
  -- Runtime fields (used during evaluation)
  , lfTests    :: [Test]               -- test declarations
  , lfLaws     :: [Law]                -- algebraic laws
  , lfImports  :: [String]             -- import names (for lazy resolution)
  , lfInherits :: [String]             -- inherit declarations
  , lfAutocuts :: [String]             -- @autocut production names
  } deriving (Eq, Show, Functor, Foldable, Traversable)

newtype Lang a = Lang { unLang :: LangF a (Lang a) }
  deriving (Eq, Show)

-- | Compiled language: concrete Lang with unit annotation
-- This is what the evaluator works with at runtime
type CompiledLang = Lang ()

data TypeRule = TypeRule
  { trName     :: String
  , trPremises :: [Term]
  , trConclusion :: Term
  } deriving (Eq, Show)

-- | Empty language with given name
emptyLang :: String -> Lang a
emptyLang name = Lang $ LangF name S.empty M.empty [] [] [] [] [] [] [] []

-- | Accessor functions for CompiledLang (compatibility layer)
clName :: CompiledLang -> String
clName = lfName . unLang

clVocab :: CompiledLang -> Set String
clVocab = lfVocab . unLang

clGrammar :: CompiledLang -> Map String (GrammarExpr ())
clGrammar = lfGrammar . unLang

clRules :: CompiledLang -> [Rule]
clRules = lfRules . unLang

clTests :: CompiledLang -> [Test]
clTests = lfTests . unLang

clLaws :: CompiledLang -> [Law]
clLaws = lfLaws . unLang

clImports :: CompiledLang -> [String]
clImports = lfImports . unLang

clInherits :: CompiledLang -> [String]
clInherits = lfInherits . unLang

clAutocuts :: CompiledLang -> [String]
clAutocuts = lfAutocuts . unLang

-- | Smart constructor for CompiledLang
mkCompiledLang :: String -> Set String -> Map String (GrammarExpr ()) 
               -> [Rule] -> [Test] -> [String] -> [Law] -> [String] -> [String]
               -> CompiledLang
mkCompiledLang name vocab grammar rules tests imports laws inherits autocuts =
  Lang $ LangF name vocab grammar rules [] [] tests laws imports inherits autocuts

-- | Empty compiled language
emptyCompiled :: String -> CompiledLang
emptyCompiled name = Lang $ LangF name S.empty M.empty [] [] [] [] [] [] [] []

-- | Rename a language (returns a new lang with the given name)
renameLang :: String -> Lang a -> Lang a
renameLang name (Lang l) = Lang $ l { lfName = name }

-- | Modify functions for CompiledLang
addImport :: String -> CompiledLang -> CompiledLang
addImport imp (Lang l) = Lang $ l { lfImports = lfImports l ++ [imp] }

addImports :: [String] -> CompiledLang -> CompiledLang
addImports imps (Lang l) = Lang $ l { lfImports = lfImports l ++ imps }

addTest :: Test -> CompiledLang -> CompiledLang
addTest t (Lang l) = Lang $ l { lfTests = lfTests l ++ [t] }

addTests :: [Test] -> CompiledLang -> CompiledLang
addTests ts (Lang l) = Lang $ l { lfTests = lfTests l ++ ts }

addLaw :: Law -> CompiledLang -> CompiledLang
addLaw lw (Lang l) = Lang $ l { lfLaws = lfLaws l ++ [lw] }

addInherit :: String -> CompiledLang -> CompiledLang
addInherit inh (Lang l) = Lang $ l { lfInherits = lfInherits l ++ [inh] }

addAutocut :: String -> CompiledLang -> CompiledLang
addAutocut ac (Lang l) = Lang $ l { lfAutocuts = lfAutocuts l ++ [ac] }

addVocab :: Set String -> CompiledLang -> CompiledLang
addVocab v (Lang l) = Lang $ l { lfVocab = S.union (lfVocab l) v }

addGrammar :: String -> GrammarExpr () -> CompiledLang -> CompiledLang
addGrammar name g (Lang l) = Lang $ l { lfGrammar = M.insert name g (lfGrammar l) }

addRule :: Rule -> CompiledLang -> CompiledLang
addRule r (Lang l) = Lang $ l { lfRules = lfRules l ++ [r] }

--------------------------------------------------------------------------------
-- Pushout with Conflict Detection
--------------------------------------------------------------------------------

-- | Conflict types that can arise during language composition
data LangConflict
  = GrammarConflict String String String   -- ^ Same production name, different defs
  | RuleConflict String String String      -- ^ Same rule pattern, different templates
  | VocabConflict String                   -- ^ Vocabulary overlap (informational)
  deriving (Eq, Show)

-- | Pushout of languages (simple union, silent on conflicts)
--
-- NOTE: For production use, prefer 'poLangChecked' which reports conflicts.
poLang :: Lang a -> Lang a -> Lang a
poLang (Lang l1) (Lang l2) = Lang $ LangF
  { lfName = lfName l1 ++ "_" ++ lfName l2
  , lfVocab = S.union (lfVocab l1) (lfVocab l2)
  , lfGrammar = M.union (lfGrammar l1) (lfGrammar l2)
  , lfRules = lfRules l1 ++ lfRules l2
  , lfTypes = lfTypes l1 ++ lfTypes l2
  , lfExtends = []  -- Flattened
  -- Runtime fields: merge
  , lfTests = lfTests l1 ++ lfTests l2
  , lfLaws = lfLaws l1 ++ lfLaws l2
  , lfImports = lfImports l1 ++ lfImports l2
  , lfInherits = lfInherits l1 ++ lfInherits l2
  , lfAutocuts = lfAutocuts l1 ++ lfAutocuts l2
  }

-- | Pushout with conflict detection
--
-- Returns (merged language, list of conflicts).
-- Callers should check conflicts and warn/error appropriately.
--
-- Conflicts detected:
--   - Grammar: same production name with different definitions
--   - Rules: same pattern head with different templates
--   - Vocab: overlapping keywords/symbols (informational)
poLangChecked :: Eq a => Lang a -> Lang a -> (Lang a, [LangConflict])
poLangChecked (Lang l1) (Lang l2) = (merged, conflicts)
  where
    merged = poLang (Lang l1) (Lang l2)
    
    conflicts = grammarConflicts ++ ruleConflicts ++ vocabConflicts
    
    -- Grammar conflicts: same production, different definition
    grammarConflicts = 
      [ GrammarConflict prod (lfName l1) (lfName l2)
      | prod <- M.keys (lfGrammar l1)
      , prod `M.member` lfGrammar l2
      , M.lookup prod (lfGrammar l1) /= M.lookup prod (lfGrammar l2)
      ]
    
    -- Rule conflicts: same pattern head, different template
    ruleConflicts =
      [ RuleConflict (ruleName r1) (lfName l1) (lfName l2)
      | r1 <- lfRules l1
      , r2 <- lfRules l2
      , ruleName r1 == ruleName r2
      , ruleTemplate r1 /= ruleTemplate r2
      ]
    
    -- Vocabulary overlaps (informational, not usually errors)
    vocabConflicts = 
      [ VocabConflict v 
      | v <- S.toList (S.intersection (lfVocab l1) (lfVocab l2))
      ]

-- | Format conflicts for display
formatConflicts :: [LangConflict] -> String
formatConflicts [] = "No conflicts"
formatConflicts cs = unlines $ map formatOne cs
  where
    formatOne (GrammarConflict prod l1 l2) = 
      "⚠ Grammar conflict: production '" ++ prod ++ "' defined in both " ++ l1 ++ " and " ++ l2
    formatOne (RuleConflict rule l1 l2) =
      "⚠ Rule conflict: rule '" ++ rule ++ "' has different templates in " ++ l1 ++ " and " ++ l2
    formatOne (VocabConflict v) =
      "ℹ Vocab overlap: '" ++ v ++ "' appears in both languages"

-- | Catamorphism
foldLang :: (LangF a b -> b) -> Lang a -> b
foldLang f (Lang l) = f (fmap (foldLang f) l)

-- | Fixed point
fix :: (a -> a) -> a
fix f = let x = f x in x

--------------------------------------------------------------------------------
-- Extension Functors (Algebraic Extensions)
--------------------------------------------------------------------------------

-- | SubstF: Let-binding extension for Template
--   SubstF a = String × a × a  (let x = e1 in e2)
data SubstF a = ESubst String a a
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | KleeneF: Kleene algebra extension for GrammarExpr
--   Forms a *-semiring: (|, ε) is a monoid, (·, ε) is a monoid, * is Kleene star
data KleeneF a
  = KEmpty              -- ε (identity for ·)
  | KSeq a a            -- g₁ · g₂
  | KAlt a a            -- g₁ | g₂
  | KStar a             -- g*
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | BindF: Binding/recursion extension for GrammarExpr
--   GRec x g ≈ μx.g,  GRef x ≈ use of bound name,  GBind x g ≈ x ← g
--   BCut g ≈ commit point (no backtracking past this)
data BindF a
  = BRec String a       -- μX. g (recursive grammar)
  | BRef String         -- X (reference to bound grammar)
  | BBind String a      -- x ← g (capture binding)
  | BCut a              -- cut: commit point, no backtracking past here
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- | AnyF: Wildcard extension
data AnyF a = EAny
  deriving (Eq, Show, Functor, Foldable, Traversable)

--------------------------------------------------------------------------------
-- Coproduct of Functors (Sum type for extensions)
--------------------------------------------------------------------------------

-- | Coproduct: F + G
data (f :+: g) a = InL (f a) | InR (g a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

infixr 5 :+:

--------------------------------------------------------------------------------
-- Composite Functor Types
--------------------------------------------------------------------------------

-- | GrammarF = ExprF + KleeneF + BindF + AnyF
type GrammarF  = ExprF :+: KleeneF :+: BindF :+: AnyF

--------------------------------------------------------------------------------
-- GrammarExpr = newtype Fix GrammarF (with pattern synonyms)
--------------------------------------------------------------------------------

-- GrammarExpr has a phantom type parameter for historical compatibility
newtype GrammarExpr a = GrammarExpr { unGrammarExpr :: Fix GrammarF }
  deriving (Eq)

pattern GVar :: String -> GrammarExpr a
pattern GVar x = GrammarExpr (Fix (InL (EVar x)))

pattern GNode :: String -> [GrammarExpr a] -> GrammarExpr a
pattern GNode c gs <- GrammarExpr (Fix (InL (ECon c (map GrammarExpr -> gs))))
  where GNode c gs = GrammarExpr (Fix (InL (ECon c (map unGrammarExpr gs))))

pattern GLit :: String -> GrammarExpr a
pattern GLit s = GrammarExpr (Fix (InL (ELit s)))

pattern GRegex :: String -> GrammarExpr a
pattern GRegex s = GrammarExpr (Fix (InL (ERegex s)))

pattern GChar :: String -> GrammarExpr a
pattern GChar s = GrammarExpr (Fix (InL (EChar s)))

pattern GEmpty :: GrammarExpr a
pattern GEmpty = GrammarExpr (Fix (InR (InL KEmpty)))

pattern GSeq :: GrammarExpr a -> GrammarExpr a -> GrammarExpr a
pattern GSeq g1 g2 <- GrammarExpr (Fix (InR (InL (KSeq (GrammarExpr -> g1) (GrammarExpr -> g2)))))
  where GSeq g1 g2 = GrammarExpr (Fix (InR (InL (KSeq (unGrammarExpr g1) (unGrammarExpr g2)))))

pattern GAlt :: GrammarExpr a -> GrammarExpr a -> GrammarExpr a
pattern GAlt g1 g2 <- GrammarExpr (Fix (InR (InL (KAlt (GrammarExpr -> g1) (GrammarExpr -> g2)))))
  where GAlt g1 g2 = GrammarExpr (Fix (InR (InL (KAlt (unGrammarExpr g1) (unGrammarExpr g2)))))

pattern GStar :: GrammarExpr a -> GrammarExpr a
pattern GStar g <- GrammarExpr (Fix (InR (InL (KStar (GrammarExpr -> g)))))
  where GStar g = GrammarExpr (Fix (InR (InL (KStar (unGrammarExpr g)))))

pattern GRec :: String -> GrammarExpr a -> GrammarExpr a
pattern GRec x g <- GrammarExpr (Fix (InR (InR (InL (BRec x (GrammarExpr -> g))))))
  where GRec x g = GrammarExpr (Fix (InR (InR (InL (BRec x (unGrammarExpr g))))))

pattern GRef :: String -> GrammarExpr a
pattern GRef x = GrammarExpr (Fix (InR (InR (InL (BRef x)))))

pattern GBind :: String -> GrammarExpr a -> GrammarExpr a
pattern GBind x g <- GrammarExpr (Fix (InR (InR (InL (BBind x (GrammarExpr -> g))))))
  where GBind x g = GrammarExpr (Fix (InR (InR (InL (BBind x (unGrammarExpr g))))))

pattern GCut :: GrammarExpr a -> GrammarExpr a
pattern GCut g <- GrammarExpr (Fix (InR (InR (InL (BCut (GrammarExpr -> g))))))
  where GCut g = GrammarExpr (Fix (InR (InR (InL (BCut (unGrammarExpr g))))))

pattern GAny :: GrammarExpr a
pattern GAny = GrammarExpr (Fix (InR (InR (InR EAny))))

{-# COMPLETE GVar, GNode, GLit, GRegex, GChar, GEmpty, GSeq, GAlt, GStar, GRec, GRef, GBind, GCut, GAny #-}

instance Show (GrammarExpr a) where
  show GEmpty = "ε"
  show (GLit s) = "'" ++ s ++ "'"
  show (GRegex s) = "/" ++ s ++ "/"
  show (GChar s) = "'" ++ s ++ "'"
  show (GVar x) = "$" ++ x
  show (GNode c []) = "<" ++ c ++ ">"
  show (GNode c gs) = "<" ++ c ++ " " ++ unwords (map show gs) ++ ">"
  show (GSeq g1 g2) = show g1 ++ " " ++ show g2
  show (GAlt g1 g2) = "(" ++ show g1 ++ " | " ++ show g2 ++ ")"
  show (GStar g) = "(" ++ show g ++ ")*"
  show (GRec x g) = "μ" ++ x ++ "." ++ show g
  show (GRef x) = x
  show (GBind x g) = x ++ " ← " ++ show g
  show (GCut g) = "!" ++ show g  -- cut: commit point
  show GAny = "_"

--------------------------------------------------------------------------------
-- Pattern Matching & Template Application (Unified via Term)
--
-- Surface syntax uses $ to mark binders/references:
--   Pattern:  $x parses to TmVar "x" (binder)
--   Pattern:  foo parses to TmLit "foo" (literal)
--   Template: $x parses to TmVar "x" (reference)
--   Template: foo parses to TmLit "foo" (literal)
--
-- Internally, $ is stripped - position determines semantics:
--   TmVar in pattern = binder (captures any term)
--   TmVar in template = reference (substitutes bound value)
--   TmLit = must match/emit exactly
--------------------------------------------------------------------------------

type Bindings = Map String Term

-- | Match pattern against term, collecting bindings
--   TmVar = binder (captures any term)
--   TmLit = literal (must match TmVar with same name, or TmCon with no args)
--   TmCon = constructor (recurse on children)
--   
-- Key insight: TmLit in a pattern represents a "symbol name" that should match
-- a TmVar (reference) or nullary TmCon. It should NOT match another TmLit,
-- because TmLit in a term represents "data" that shouldn't be expanded.
-- This prevents infinite loops like: def era = (agent era 0) where the
-- "era" inside agent is a data name (TmLit), not a reference (TmVar).
matchPat :: Term -> Term -> Maybe Bindings
matchPat (TmVar x) t = Just (M.singleton x t)  -- All vars are binders
-- TmLit pattern matches TmVar reference (symbol to expand) - key case
matchPat (TmLit s) (TmVar x) | s == x = Just M.empty
-- TmLit pattern matches nullary TmCon (for grammar productions)
matchPat (TmLit s) (TmCon c []) | s == c = Just M.empty
-- TmLit does NOT match TmLit - both are data, not references
matchPat (TmCon c ps) (TmCon c' ts)
  | c == c' && length ps == length ts = do
      binds <- zipWithM matchPat ps ts
      return $ M.unions binds
matchPat _ _ = Nothing

zipWithM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

-- | Apply template with bindings
--   TmVar x = reference (substitutes bound value)
--   (subst x e body) = let-binding: body[x := e]
applyTemplate :: Bindings -> Term -> Term
applyTemplate binds = \case
  TmVar x -> case M.lookup x binds of
    Just t  -> t
    Nothing -> TmVar x  -- Unbound var stays as-is
  TmLit s -> TmLit s
  TmRegex s -> TmRegex s
  TmChar s -> TmChar s
  -- subst with TmVar as variable name
  TmCon "subst" [TmVar x, e, body] ->
    let v = applyTemplate binds e
        binds' = M.insert x v binds
    in applyTemplate binds' body
  -- subst with TmLit as variable name (from captured pattern)
  TmCon "subst" [TmLit x, e, body] ->
    let v = applyTemplate binds e
        binds' = M.insert x v binds
    in applyTemplate binds' body
  TmCon c ts -> TmCon c (map (applyTemplate binds) ts)
  -- Cubical primitives
  TmInterval -> TmInterval
  TmI0 -> TmI0
  TmI1 -> TmI1
  TmPathType a x y -> TmPathType (applyTemplate binds a) (applyTemplate binds x) (applyTemplate binds y)
  TmPathAbs i e -> TmPathAbs i (applyTemplate binds e)  -- TODO: shadow i
  TmPathApp p r -> TmPathApp (applyTemplate binds p) (applyTemplate binds r)
  -- Composition operations
  TmComp a phi u a0 -> TmComp (applyTemplate binds a) (applyTemplate binds phi) (applyTemplate binds u) (applyTemplate binds a0)
  TmHComp a phi u a0 -> TmHComp (applyTemplate binds a) (applyTemplate binds phi) (applyTemplate binds u) (applyTemplate binds a0)
  TmTransp a phi a0 -> TmTransp (applyTemplate binds a) (applyTemplate binds phi) (applyTemplate binds a0)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Normalize a term using rules (forward direction only by default)
normalize :: [Rule] -> Term -> Term
normalize = normalizeDir Forward

-- | Normalize with explicit direction
normalizeDir :: RuleDir -> [Rule] -> Term -> Term
normalizeDir dir rules = go (1000 :: Int)  -- fuel
  where
    -- Expand rules: Both direction rules contribute both forward and backward
    expandedRules = concatMap (expandRule dir) rules
    
    go :: Int -> Term -> Term
    go 0 t = t  -- out of fuel
    go n t = 
      -- First, normalize subterms (congruence)
      let t' = normSub t
      in case step t' of
        Nothing -> t'  -- fully normalized
        Just t'' -> go (n-1) t''
    
    -- Normalize subterms
    normSub :: Term -> Term
    normSub (TmCon c args) = TmCon c (map (normalizeDir dir rules) args)
    normSub v@(TmVar _) = case builtinStep v of
      Just t -> normalizeDir dir rules t  -- Variables can reduce (e.g., newline)
      Nothing -> v
    normSub t = t
    
    step :: Term -> Maybe Term
    step t = builtinStep t <|> foldr (<|>) Nothing (map (tryRule t) expandedRules)
    
    tryRule :: Term -> Rule -> Maybe Term
    tryRule t rule = do
      binds <- matchPat (rulePattern rule) t
      -- Check guard if present
      case ruleGuard rule of
        Nothing -> return $ applyTemplate binds (ruleTemplate rule)
        Just guardTerm -> 
          let guardInst = applyTemplate binds guardTerm
              guardResult = normalizeDir dir rules guardInst
          in if isTruthy guardResult
             then return $ applyTemplate binds (ruleTemplate rule)
             else Nothing
    
    -- | Check if a term is truthy (evaluates to true-like value)
    isTruthy :: Term -> Bool
    isTruthy (TmCon "true" []) = True
    isTruthy (TmVar "true") = True
    isTruthy (TmLit "true") = True
    isTruthy (TmCon "True" []) = True
    isTruthy (TmVar "True") = True
    isTruthy (TmLit "True") = True
    isTruthy _ = False

-- | Normalize with tracing: returns final term + list of reduction steps
normalizeTrace :: [Rule] -> Term -> (Term, [TraceStep])
normalizeTrace = normalizeTraceDir Forward

-- | Normalize with tracing and explicit direction
normalizeTraceDir :: RuleDir -> [Rule] -> Term -> (Term, [TraceStep])
normalizeTraceDir dir rules term = go (1000 :: Int) term []
  where
    expandedRules = concatMap (expandRule dir) rules
    
    go :: Int -> Term -> [TraceStep] -> (Term, [TraceStep])
    go 0 t acc = (t, reverse acc)  -- out of fuel
    go n t acc =
      -- First, normalize subterms (no tracing for subterms - top-level only)
      let t' = normSub t
      in case stepWithTrace t' of
        Nothing -> (t', reverse acc)  -- fully normalized
        Just (t'', step) -> go (n-1) t'' (step : acc)
    
    -- Normalize subterms (non-tracing, just congruence)
    normSub :: Term -> Term
    normSub (TmCon c args) = TmCon c (map (normalizeDir dir rules) args)
    normSub v@(TmVar _) = case builtinStep v of
      Just r -> normalizeDir dir rules r
      Nothing -> v
    normSub t = t
    
    -- Step with trace info
    stepWithTrace :: Term -> Maybe (Term, TraceStep)
    stepWithTrace t = builtinStepTrace t <|> foldr (<|>) Nothing (map (tryRuleTrace t) expandedRules)
    
    -- Builtin step with trace
    builtinStepTrace :: Term -> Maybe (Term, TraceStep)
    builtinStepTrace t = do
      result <- builtinStep t
      return (result, TraceStep { tsRule = "<builtin>", tsBefore = t, tsAfter = result, tsBindings = M.empty, tsLocation = Nothing })
    
    -- Try rule with trace
    tryRuleTrace :: Term -> Rule -> Maybe (Term, TraceStep)
    tryRuleTrace t rule = do
      binds <- matchPat (rulePattern rule) t
      result <- case ruleGuard rule of
        Nothing -> return $ applyTemplate binds (ruleTemplate rule)
        Just guardTerm ->
          let guardInst = applyTemplate binds guardTerm
              guardResult = normalizeDir dir rules guardInst
          in if isTruthy guardResult
             then return $ applyTemplate binds (ruleTemplate rule)
             else Nothing
      return (result, TraceStep { tsRule = ruleName rule, tsBefore = t, tsAfter = result, tsBindings = binds, tsLocation = Nothing })
    
    isTruthy :: Term -> Bool
    isTruthy (TmCon "true" []) = True
    isTruthy (TmVar "true") = True
    isTruthy (TmLit "true") = True
    isTruthy (TmCon "True" []) = True
    isTruthy (TmVar "True") = True
    isTruthy (TmLit "True") = True
    isTruthy _ = False

-- | Format a trace for display
formatTrace :: [TraceStep] -> String
formatTrace steps = unlines $ zipWith formatStep [1..] steps
  where
    formatStep :: Int -> TraceStep -> String
    formatStep i step = concat
      [ show i, ". [", tsRule step, "]"
      , case tsLocation step of
          Nothing -> ""
          Just loc -> " at " ++ show loc
      , "\n"
      , "   ", show (tsBefore step), "\n"
      , "   → ", show (tsAfter step)
      , if M.null (tsBindings step) then "" else "\n   bindings: " ++ showBindings (tsBindings step)
      ]
    showBindings binds = concat $ intersperse ", " [k ++ "=" ++ show v | (k,v) <- M.toList binds]
    intersperse _ [] = []
    intersperse _ [x] = [x]
    intersperse sep (x:xs) = x : sep : intersperse sep xs

-- | Expand a rule based on requested direction
-- Forward rules: only fire forward (pattern → template)
-- Backward rules: only fire backward (template → pattern)
-- Both rules: fire in whichever direction is requested
expandRule :: RuleDir -> Rule -> [Rule]
expandRule Forward r = case ruleDir r of
  Forward  -> [r]                    -- Forward ~> Forward: yes
  Backward -> []                     -- Backward in forward context: no
  Both     -> [r]                    -- Both ~> Forward: yes
expandRule Backward r = case ruleDir r of
  Forward  -> []                     -- Forward in backward context: no
  Backward -> [r]                    -- Backward <~ Backward: yes
  Both     -> [flipRule r]           -- Both ~> Backward: flip it
expandRule Both r = case ruleDir r of
  Forward  -> [r]                    -- Forward in both context: forward only
  Backward -> [r]                    -- Backward in both context: backward only
  Both     -> [r, flipRule r]        -- Both in both: both directions

--------------------------------------------------------------------------------
-- Testing
--------------------------------------------------------------------------------

-- | Basic test (legacy format)
data Test = Test
  { testName :: String
  , testInput :: Term
  , testExpected :: Term
  } deriving (Eq, Show)

-- | Enhanced test specification
data TestSpec = TestSpec
  { tsName     :: String
  , tsInput    :: Term
  , tsExpect   :: TestExpect     -- What result to expect
  , tsOpts     :: TestOpts       -- Additional options
  } deriving (Eq, Show)

-- | What the test expects (with boolean calculus)
data TestExpect
  = ExpectParse                   -- Just parse, no normalization
  | ExpectNorm Term               -- Normalize and match term
  | ExpectError String            -- Expect an error (partial match)
  | ExpectNoChange                -- Input should be in normal form
  -- Boolean combinators
  | ExpectAnd TestExpect TestExpect  -- Both must pass
  | ExpectOr TestExpect TestExpect   -- Either must pass
  | ExpectNot TestExpect             -- Must NOT pass
  -- Quantitative
  | ExpectSteps Int                  -- Exact step count
  | ExpectViaRule String             -- Must use this rule
  deriving (Eq, Show)

-- | Smart constructors for boolean algebra
(.&&.) :: TestExpect -> TestExpect -> TestExpect
(.&&.) = ExpectAnd
infixr 3 .&&.

(.||.) :: TestExpect -> TestExpect -> TestExpect
(.||.) = ExpectOr
infixr 2 .||.

expectNot :: TestExpect -> TestExpect
expectNot = ExpectNot

-- | Test options (modifiers)
data TestOpts = TestOpts
  { toTrace     :: Bool           -- Show rule trace
  , toViaRule   :: Maybe String   -- Require specific rule to fire
  , toSteps     :: Maybe Int      -- Exact step count
  , toBidir     :: Bool           -- Test in both directions
  } deriving (Eq, Show)

-- | Default test options
defaultOpts :: TestOpts
defaultOpts = TestOpts False Nothing Nothing False

-- | Convert legacy Test to TestSpec
testToSpec :: Test -> TestSpec
testToSpec t = TestSpec
  { tsName   = testName t
  , tsInput  = testInput t
  , tsExpect = ExpectNorm (testExpected t)
  , tsOpts   = defaultOpts
  }

data TestResult = Pass String | Fail String Term Term
  deriving (Eq, Show)

-- | Declaration types for Lego files
data LegoDecl
  = DLang String [String] [LegoDecl] -- lang Name (Parents) := body
  | DPiece String [String] [LegoDecl] -- piece Name is Parents with: body
  | DImport String                   -- import Name (scope only, no pushout)
  | DPushout String String           -- L1 ⊔ L2 (explicit pushout)
  | DVocab [String] [String]         -- vocab: keywords, symbols
  | DGrammar String (GrammarExpr ()) -- Name ::= grammar
  | DRule Rule                       -- pattern ~> template
  | DType TypeRule                   -- typing rule
  | DTest Test                       -- test (legacy)
  | DTestSpec TestSpec               -- test (enhanced)
  | DDef String Term                 -- def name = term (desugars to rule)
  | DLaw Law                         -- law "name": expr ≅ expr
  | DInherit String                  -- inherit Module.Production
  | DAutocut String                  -- @autocut production
  deriving (Eq, Show)

-- | Law declaration for algebraic laws
data Law = Law
  { lawName  :: String     -- name of the law
  , lawLhs   :: Term       -- left-hand side expression
  , lawRhs   :: Term       -- right-hand side expression
  } deriving (Eq, Show)

-- | Run a basic test (legacy)
runTest :: [Rule] -> Test -> TestResult
runTest rules test =
  let actual = normalize rules (testInput test)
      expected = testExpected test
  in case matchTerms expected actual of
       Just _ -> Pass (testName test)
       Nothing -> Fail (testName test) expected actual

-- | Enhanced test result with more info
data TestResultE
  = PassE String                          -- Passed
  | FailE String String                   -- Failed with message
  | FailMatchE String Term Term           -- Expected vs actual mismatch
  | FailStepsE String Int Int             -- Expected vs actual step count
  | FailRuleE String String               -- Expected rule didn't fire
  deriving (Eq, Show)

-- | Run an enhanced test spec
runTestSpec :: [Rule] -> TestSpec -> TestResultE
runTestSpec rules spec = 
  let (actual, trace) = normalizeTrace rules (tsInput spec)
      name = tsName spec
  in evalExpect name actual trace (tsExpect spec)
  where
    evalExpect :: String -> Term -> [TraceStep] -> TestExpect -> TestResultE
    evalExpect name _actual _trace ExpectParse = 
      PassE name
    
    evalExpect name actual _trace (ExpectNorm expected) =
      case matchTerms expected actual of
        Just _  -> PassE name
        Nothing -> FailMatchE name expected actual
    
    evalExpect name _actual trace ExpectNoChange =
      if null trace
      then PassE name
      else FailE name "expected no reduction but got steps"
    
    evalExpect name _actual _trace (ExpectError _) =
      FailE name "ExpectError checked at parse time"
    
    evalExpect name _actual trace (ExpectSteps n) =
      if length trace == n
      then PassE name
      else FailStepsE name n (length trace)
    
    evalExpect name _actual trace (ExpectViaRule rule) =
      if any (\s -> tsRule s == rule) trace
      then PassE name
      else FailRuleE name rule
    
    -- Boolean combinators
    evalExpect name actual trace (ExpectAnd e1 e2) =
      case evalExpect name actual trace e1 of
        PassE _ -> evalExpect name actual trace e2
        failure -> failure
    
    evalExpect name actual trace (ExpectOr e1 e2) =
      case evalExpect name actual trace e1 of
        PassE _ -> PassE name
        _ -> evalExpect name actual trace e2
    
    evalExpect name actual trace (ExpectNot e) =
      case evalExpect name actual trace e of
        PassE _ -> FailE name "expected NOT to pass but did"
        _ -> PassE name

-- | Match expected (with variables) against actual (concrete)
-- Variables in expected pattern match anything
matchTerms :: Term -> Term -> Maybe Bindings
matchTerms (TmVar x) actual = Just (M.singleton x actual)
matchTerms (TmLit s) (TmLit s') | s == s' = Just M.empty
matchTerms (TmLit s) (TmCon c []) | s == c = Just M.empty
matchTerms (TmCon c []) (TmLit s) | c == s = Just M.empty
matchTerms (TmCon c ts) (TmCon c' ts')
  | c == c' && length ts == length ts' = do
      binds <- zipWithM matchTerms ts ts'
      -- Check consistency: same variable must match same term
      mergeBindings binds
matchTerms _ _ = Nothing

mergeBindings :: [Bindings] -> Maybe Bindings
mergeBindings = foldM mergeTwoBindings M.empty

mergeTwoBindings :: Bindings -> Bindings -> Maybe Bindings
mergeTwoBindings b1 b2 = foldM addBinding b1 (M.toList b2)
  where
    addBinding m (k, v) = case M.lookup k m of
      Nothing -> Just (M.insert k v m)
      Just v' -> if v == v' then Just m else Nothing

runTests :: [Rule] -> [Test] -> [TestResult]
runTests rules = map (runTest rules)

_printResults :: [TestResult] -> IO ()
_printResults results = do
  let (passed, failed) = partition results
  putStrLn $ "Passed: " ++ show (length passed)
  putStrLn $ "Failed: " ++ show (length failed)
  mapM_ printFail failed
  where
    partition = foldr f ([], [])
    f r@(Pass _) (ps, fs) = (r:ps, fs)
    f r@(Fail _ _ _) (ps, fs) = (ps, r:fs)
    
    printFail (Fail name expected actual) = do
      putStrLn $ "FAIL: " ++ name
      putStrLn $ "  Expected: " ++ show expected
      putStrLn $ "  Actual:   " ++ show actual
    printFail _ = return ()