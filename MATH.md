# Lego: Mathematical Foundations

> **"The more math, the less code and bugs."**
>
> **Status**: Standalone package • See [lego.cabal](lego.cabal) • [math-concepts.svg](math-concepts.svg)

This document provides a complete mathematical specification of Lego, a declarative language workbench where syntax is expression. Every definition includes precise paths to constructors and fields, enabling formalization in a proof assistant.

---

## Table of Contents

1. [Overview](#overview)
2. [Type Universe](#type-universe)
3. [The 5 Pieces](#the-5-pieces)
4. [The 3 Operations](#the-3-operations)
5. [Grammar Algebra](#grammar-algebra)
6. [Bidirectional Interpretation](#bidirectional-interpretation)
7. [Pattern Matching & Rewriting](#pattern-matching--rewriting)
8. [Composition & Pushouts](#composition--pushouts)
9. [Algebraic Laws](#algebraic-laws)
10. [References](#references)

---

## Overview

Lego is a **language workbench** built on categorical foundations. The core insight:

> **Syntax is expression, not procedure.**

The same grammar definition drives parsing, printing, and validation via modal interpretation—a profunctor-style design where the mode parameter selects behavior.

### Architecture Summary

```
Pieces := Name | Graph | GrammarExpr | Rule | Lang
Operations := Pushout (⊔) | Fold (catamorphism) | Fix (μ)

Lang = μL. LangF L   where   LangF L = (Name, Vocab, Grammar, [Rule], [L])
```

---

## Type Universe

### Path Notation

We use `Path[T]` notation to reference constructors and fields:

```
Path[T] ::= T                           -- Type itself
          | T.constructor               -- Constructor
          | T.constructor.field         -- Field of constructor
          | T.constructor.field[n]      -- n-th element (0-indexed)
```

### Base Types

```agda
-- Primitive types
String : Type
Int : Type
Bool : Type
Set[A] : Type → Type
Map[K,V] : Type → Type → Type
List[A] : Type → Type
Maybe[A] : Type → Type
```

---

## The 5 Pieces

### Piece 1: Name (Atomic Set)

**Definition**: Names are atomic identifiers forming a discrete set.

```agda
-- Path: Lego.Name
Name : Type
Name = String

-- Constructor path: Lego.Name.Name
Name.Name : String → Name
Name.unName : Name → String
```

**Laws**: Names form an equivalence under string equality.

```
∀ (x y : Name). x ≡ y ↔ unName x = unName y
```

---

### Piece 2: Graph (Monoid)

**Definition**: Graphs are finite directed multigraphs with labeled nodes and port-based edges.

```agda
-- Path: Lego.Graph
Graph : Type → Type

-- Type aliases
-- Path: Lego.GId
GId : Type
GId = Int

-- Path: Lego.Port  
Port : Type
Port = (GId, Int)   -- (node id, slot index)
```

**Constructor**:

```agda
-- Path: Lego.Graph.Graph
data Graph (a : Type) where
  Graph : (gNodes : Map[GId, a])      -- Field: Graph.Graph.gNodes
        → (gEdges : Set[(Port, Port)]) -- Field: Graph.Graph.gEdges
        → (gFresh : GId)               -- Field: Graph.Graph.gFresh
        → Graph a
```

**Operations**:

```agda
-- Path: Lego.emptyGraph
emptyGraph : ∀ a. Graph a
emptyGraph = Graph Map.empty Set.empty 0

-- Path: Lego.addNode
addNode : ∀ a. a → Graph a → (GId, Graph a)
addNode label g = 
  let nid = g.gFresh
  in (nid, Graph (Map.insert nid label g.gNodes) g.gEdges (nid + 1))

-- Path: Lego.addEdge
addEdge : Port → Port → Graph a → Graph a
addEdge p1 p2 g = g { gEdges = Set.insert (p1, p2) g.gEdges }
```

**Monoid Instance**:

```agda
-- Path: Lego.Graph.<>
(<>) : ∀ a. Graph a → Graph a → Graph a
g1 <> g2 = 
  let shift = g1.gFresh
      nodes2 = Map.mapKeys (+ shift) g2.gNodes
      edges2 = Set.map (shiftPorts shift) g2.gEdges
  in Graph (Map.union g1.gNodes nodes2)
           (Set.union g1.gEdges edges2)
           (g1.gFresh + g2.gFresh)
  where
    shiftPorts s ((n1,s1),(n2,s2)) = ((n1+s,s1),(n2+s,s2))

-- Path: Lego.Graph.mempty
mempty : ∀ a. Graph a
mempty = emptyGraph
```

**Algebraic Structure**: `(Graph a, <>, emptyGraph)` is a **Monoid**.

---

### Piece 3: GrammarExpr (Free Algebra)

**Definition**: Grammar expressions form a free algebra over tokens, with Kleene structure.

#### Base Expression Functor

```agda
-- Path: Lego.Internal.ExprF
data ExprF (a : Type) where
  EVar : String → ExprF a       -- Path: ExprF.EVar
  ECon : String → List a → ExprF a  -- Path: ExprF.ECon
  ELit : String → ExprF a       -- Path: ExprF.ELit
  ESyn : String → ExprF a       -- Path: ExprF.ESyn (syntax marker)
```

#### Kleene Extension

```agda
-- Path: Lego.KleeneF
-- Forms a *-semiring: (|, ε) is monoid, (·, ε) is monoid, * is Kleene star
data KleeneF (a : Type) where
  KEmpty : KleeneF a                  -- Path: KleeneF.KEmpty (ε)
  KSeq   : a → a → KleeneF a          -- Path: KleeneF.KSeq (g₁ · g₂)
  KAlt   : a → a → KleeneF a          -- Path: KleeneF.KAlt (g₁ | g₂)
  KStar  : a → KleeneF a              -- Path: KleeneF.KStar (g*)
```

#### Binding Extension

```agda
-- Path: Lego.BindF
data BindF (a : Type) where
  BRec  : String → a → BindF a       -- Path: BindF.BRec (μX. g)
  BRef  : String → BindF a           -- Path: BindF.BRef (X)
  BBind : String → a → BindF a       -- Path: BindF.BBind (x ← g)
```

#### Wildcard Extension

```agda
-- Path: Lego.AnyF
data AnyF (a : Type) where
  EAny : AnyF a                      -- Path: AnyF.EAny (_)
```

#### Functor Coproduct

```agda
-- Path: Lego.:+:
data (:+:) (f g : Type → Type) (a : Type) where
  InL : f a → (f :+: g) a            -- Path: :+:.InL
  InR : g a → (f :+: g) a            -- Path: :+:.InR
```

#### Composite Grammar Functor

```agda
-- Path: Lego.GrammarF
GrammarF : Type → Type
GrammarF = ExprF :+: KleeneF :+: BindF :+: AnyF
```

#### GrammarExpr (Fixed Point)

```agda
-- Path: Lego.Internal.Fix
data Fix (f : Type → Type) where
  Fix : f (Fix f) → Fix f           -- Path: Fix.Fix
  
unFix : Fix f → f (Fix f)           -- Path: Fix.unFix
unFix (Fix x) = x

-- Path: Lego.GrammarExpr
newtype GrammarExpr (a : Type) where
  GrammarExpr : Fix GrammarF → GrammarExpr a
```

**Pattern Synonyms** (for ergonomic access):

```agda
-- Path: Lego.GEmpty
pattern GEmpty : GrammarExpr a
pattern GEmpty = GrammarExpr (Fix (InR (InL KEmpty)))

-- Path: Lego.GLit
pattern GLit : String → GrammarExpr a
pattern GLit s = GrammarExpr (Fix (InL (ELit s)))

-- Path: Lego.GSyntax  
pattern GSyntax : String → GrammarExpr a
pattern GSyntax s = GrammarExpr (Fix (InL (ESyn s)))

-- Path: Lego.GVar
pattern GVar : String → GrammarExpr a
pattern GVar x = GrammarExpr (Fix (InL (EVar x)))

-- Path: Lego.GNode
pattern GNode : String → List (GrammarExpr a) → GrammarExpr a

-- Path: Lego.GSeq
pattern GSeq : GrammarExpr a → GrammarExpr a → GrammarExpr a

-- Path: Lego.GAlt
pattern GAlt : GrammarExpr a → GrammarExpr a → GrammarExpr a

-- Path: Lego.GStar
pattern GStar : GrammarExpr a → GrammarExpr a

-- Path: Lego.GRec
pattern GRec : String → GrammarExpr a → GrammarExpr a

-- Path: Lego.GRef
pattern GRef : String → GrammarExpr a

-- Path: Lego.GBind
pattern GBind : String → GrammarExpr a → GrammarExpr a

-- Path: Lego.GAny
pattern GAny : GrammarExpr a
```

**Algebraic Structure**: `GrammarExpr` forms a **Kleene Algebra** (semiring with star):

```
-- Additive monoid (|, ε_alt)
∀ g.       g | ∅   ≡ g
∀ g.       ∅ | g   ≡ g  
∀ g h k.   (g | h) | k ≡ g | (h | k)

-- Multiplicative monoid (·, ε)
∀ g.       g · ε   ≡ g
∀ g.       ε · g   ≡ g
∀ g h k.   (g · h) · k ≡ g · (h · k)

-- Kleene star
∀ g.       g* ≡ ε | (g · g*)
∀ g.       g* ≡ ε | (g* · g)
∀ g.       g** ≡ g*
```

---

### Piece 4: Rule (Rewrite)

**Definition**: Rules specify term rewriting with optional guards and direction.

#### Term (S-Expression AST)

```agda
-- Path: Lego.Internal.Term
newtype Term where
  Term : Fix ExprF → Term            -- Path: Term.Term
  
unTerm : Term → Fix ExprF            -- Path: Term.unTerm

-- Pattern synonyms
-- Path: Lego.Internal.TmVar
pattern TmVar : String → Term
pattern TmVar x = Term (Fix (EVar x))

-- Path: Lego.Internal.TmCon
pattern TmCon : String → List Term → Term

-- Path: Lego.Internal.TmLit
pattern TmLit : String → Term
pattern TmLit s = Term (Fix (ELit s))

-- Path: Lego.Internal.TmSyntax
pattern TmSyntax : String → Term
pattern TmSyntax s = Term (Fix (ESyn s))
```

#### Rule Direction

```agda
-- Path: Lego.RuleDir
-- Forms a lattice: Both ⊑ Forward, Both ⊑ Backward
data RuleDir where
  Forward  : RuleDir     -- Path: RuleDir.Forward  (~>)
  Backward : RuleDir     -- Path: RuleDir.Backward (<~)
  Both     : RuleDir     -- Path: RuleDir.Both     (<~>)
```

#### Rule Constructor

```agda
-- Path: Lego.Rule
data Rule where
  Rule : (ruleName     : String)      -- Path: Rule.Rule.ruleName
       → (rulePattern  : Term)        -- Path: Rule.Rule.rulePattern
       → (ruleTemplate : Term)        -- Path: Rule.Rule.ruleTemplate
       → (ruleGuard    : Maybe Term)  -- Path: Rule.Rule.ruleGuard
       → (ruleDir      : RuleDir)     -- Path: Rule.Rule.ruleDir
       → Rule
```

**Pattern Convention**: Pattern variables use `$` prefix.

```
$x, $foo, $arg  -- pattern variables (bind on match, substitute on apply)
x, foo, arg     -- literals (must match exactly)
```

#### Rule Operations

```agda
-- Path: Lego.mkRule
mkRule : String → Term → Term → Rule
mkRule name pat templ = Rule name pat templ Nothing Forward

-- Path: Lego.flipRule
flipRule : Rule → Rule
flipRule r = r { rulePattern = r.ruleTemplate
               , ruleTemplate = r.rulePattern }

-- Path: Lego.canForward
canForward : RuleDir → Bool
canForward Forward  = True
canForward Both     = True
canForward Backward = False

-- Path: Lego.canBackward
canBackward : RuleDir → Bool
canBackward Backward = True
canBackward Both     = True
canBackward Forward  = False
```

---

### Piece 5: Lang (Initial Algebra)

**Definition**: Languages are the fixed point of the language functor.

#### Language Functor

```agda
-- Path: Lego.LangF
data LangF (a : Type) (l : Type) where
  LangF : (lfName    : String)                     -- Path: LangF.LangF.lfName
        → (lfVocab   : Set String)                 -- Path: LangF.LangF.lfVocab
        → (lfGrammar : Map String (GrammarExpr a)) -- Path: LangF.LangF.lfGrammar
        → (lfRules   : List Rule)                  -- Path: LangF.LangF.lfRules
        → (lfTypes   : List TypeRule)              -- Path: LangF.LangF.lfTypes
        → (lfExtends : List l)                     -- Path: LangF.LangF.lfExtends
        → LangF a l
```

#### Language (Fixed Point)

```agda
-- Path: Lego.Lang
newtype Lang (a : Type) where
  Lang : LangF a (Lang a) → Lang a   -- Path: Lang.Lang
  
unLang : Lang a → LangF a (Lang a)   -- Path: Lang.unLang
```

#### Type Rules

```agda
-- Path: Lego.TypeRule
data TypeRule where
  TypeRule : (trName       : String)    -- Path: TypeRule.TypeRule.trName
           → (trPremises   : List Term) -- Path: TypeRule.TypeRule.trPremises
           → (trConclusion : Term)      -- Path: TypeRule.TypeRule.trConclusion
           → TypeRule
```

#### Empty Language

```agda
-- Path: Lego.emptyLang
emptyLang : String → Lang a
emptyLang name = Lang (LangF name Set.empty Map.empty [] [] [])
```

---

## The 3 Operations

### Operation 1: Pushout (⊔)

**Definition**: Categorical pushout for language composition.

```
      A (shared structure)
     / \
    /   \
   L1   L2
    \   /
     \ /
    L1 ⊔ L2
```

#### Graph Pushout

```agda
-- Path: Lego.poGraph
poGraph : ∀ a. Eq a ⇒ Graph a → Graph a → Graph a
poGraph = (<>)  -- Currently disjoint union; full pushout needs identification
```

#### Language Pushout

```agda
-- Path: Lego.poLang
poLang : Lang a → Lang a → Lang a
poLang (Lang l1) (Lang l2) = Lang (LangF
  { lfName    = l1.lfName ++ "_" ++ l2.lfName
  , lfVocab   = Set.union l1.lfVocab l2.lfVocab
  , lfGrammar = Map.union l1.lfGrammar l2.lfGrammar
  , lfRules   = l1.lfRules ++ l2.lfRules
  , lfTypes   = l1.lfTypes ++ l2.lfTypes
  , lfExtends = []
  })
```

**Universal Property**: For any `X` with morphisms from `L1` and `L2`:

```
         i₁
    L1 ────────→ L1 ⊔ L2
     \            │
      \           │ !
   f₁  \          ↓
        ↘        X
         ↗
   f₂  /
      /
    L2 ────────→ L1 ⊔ L2
         i₂
```

There exists a unique morphism `! : L1 ⊔ L2 → X` making the diagram commute.

---

### Operation 2: Fold (Catamorphism)

**Definition**: The unique morphism from an initial algebra.

```agda
-- Path: Lego.Internal.cata
cata : ∀ f a. Functor f ⇒ (f a → a) → Fix f → a
cata alg = go where
  go (Fix f) = alg (fmap go f)

-- Path: Lego.foldLang
foldLang : (LangF a b → b) → Lang a → b
foldLang f (Lang l) = f (fmap (foldLang f) l)
```

**Uniqueness**: `foldLang` is the unique morphism from the initial `LangF`-algebra.

---

### Operation 3: Fix (Fixed Point)

**Definition**: Knot-tying for recursive definitions.

```agda
-- Path: Lego.fix
fix : (a → a) → a
fix f = let x = f x in x

-- Path: Lego.Internal.ana (Anamorphism - dual to cata)
ana : ∀ f a. Functor f ⇒ (a → f a) → a → Fix f
ana coalg = go where
  go a = Fix (fmap go (coalg a))
```

---

## Grammar Algebra

### Semiring Structure

`GrammarExpr` forms a **Kleene Algebra**:

| Operation | Symbol | Identity | Interpretation |
|-----------|--------|----------|----------------|
| Alternative | `|` (GAlt) | ∅ (fail) | Coproduct |
| Sequence | `·` (GSeq) | ε (GEmpty) | Monoidal product |
| Kleene star | `*` (GStar) | — | Free monoid |

### Grammar Equations

```agda
-- Sequence identity
∀ g. gseq GEmpty g ≡ g
∀ g. gseq g GEmpty ≡ g

-- Alternative identity
∀ g. galt g (fail) ≡ g

-- Kleene unfolding
∀ g. GStar g ≡ GAlt GEmpty (GSeq g (GStar g))

-- Distributivity
∀ g h k. GSeq g (GAlt h k) ≡ GAlt (GSeq g h) (GSeq g k)
∀ g h k. GSeq (GAlt g h) k ≡ GAlt (GSeq g k) (GSeq h k)
```

### Grammar Definition Map

These grammars are loaded from `prelude/lego/Grammar.sexpr` at module initialization.
The .sexpr format is portable and generated by `GenGrammarDef` from Grammar.lego.

```agda
-- Path: Lego.GrammarDef.legoGrammar
legoGrammar : Map String (GrammarExpr ())

-- Component grammars
-- Path: Lego.GrammarDef.atomGrammar
atomGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.termGrammar  
termGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.patternGrammar
patternGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.templateGrammar
templateGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.grammarExprGrammar
grammarExprGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.ruleGrammar
ruleGrammar : Map String (GrammarExpr ())

-- Path: Lego.GrammarDef.testGrammar
testGrammar : Map String (GrammarExpr ())
```

---

## Bidirectional Interpretation

### Mode (Modal Parameter)

**Definition**: Interpretation mode selects behavior from the same grammar.

```agda
-- Path: Lego.Mode
data Mode where
  Parse : Mode   -- Path: Mode.Parse   (tokens → AST)
  Print : Mode   -- Path: Mode.Print   (AST → tokens)
  Check : Mode   -- Path: Mode.Check   (validation)
```

**Key Insight**: Same grammar, different semantics per mode. This is a **profunctor-style** design.

### Bidirectional State

```agda
-- Path: Lego.BiState
data BiState (tok bind : Type) where
  BiState : (bsTokens  : List tok)              -- Path: BiState.BiState.bsTokens
          → (bsBinds   : List (Map String bind)) -- Path: BiState.BiState.bsBinds (scope stack)
          → (bsTerm    : Maybe Term)             -- Path: BiState.BiState.bsTerm
          → (bsMode    : Mode)                   -- Path: BiState.BiState.bsMode
          → (bsGrammar : Map String (GrammarExpr ())) -- Path: BiState.BiState.bsGrammar
          → BiState tok bind
```

### Scope Operations

The binding environment is a **stack of maps** implementing lexical scoping:

```agda
-- Path: Lego.lookupBind
lookupBind : String → List (Map String bind) → Maybe bind
lookupBind _ [] = Nothing
lookupBind x (frame : rest) = case Map.lookup x frame of
  Just v  → Just v
  Nothing → lookupBind x rest

-- Path: Lego.insertBind
insertBind : String → bind → List (Map String bind) → List (Map String bind)
insertBind x v (frame : rest) = Map.insert x v frame : rest

-- Path: Lego.pushScope
pushScope : List (Map String bind) → List (Map String bind)
pushScope frames = Map.empty : frames

-- Path: Lego.popScope
popScope : List (Map String bind) → List (Map String bind)
popScope (_ : rest) = rest

-- Path: Lego.flattenBinds
flattenBinds : List (Map String bind) → Map String bind
flattenBinds = foldr Map.union Map.empty  -- inner scopes shadow outer
```

### Bidirectional Result

```agda
-- Path: Lego.BiResult
data BiResult (tok bind : Type) where
  BiSuccess : BiState tok bind → BiResult tok bind   -- Path: BiResult.BiSuccess
  BiFail    : String → BiResult tok bind             -- Path: BiResult.BiFail
```

### Interpretation Function

```agda
-- Path: Lego.runBiGrammar
runBiGrammar : GrammarExpr a → BiState String String → List (BiState String String)

-- Path: Lego.biParse
biParse : GrammarExpr a → List String → List (Term, List String)

-- Path: Lego.biPrint
biPrint : GrammarExpr a → Term → Map String String → List String

-- Path: Lego.biCheck
biCheck : GrammarExpr a → BiState String String → Bool
```

### Modal Semantics Table

| Grammar | Parse Mode | Print Mode | Check Mode |
|---------|------------|------------|------------|
| `GEmpty` | succeed | succeed | succeed |
| `GLit s` | consume token `s` | produce token `s` | succeed |
| `GSyntax s` | consume token `s` | produce token `s` | succeed |
| `GSeq g₁ g₂` | parse g₁, then g₂ | print g₁, then g₂ | check g₁, then g₂ |
| `GAlt g₁ g₂` | try g₁, else g₂ | try g₁, else g₂ | check either |
| `GStar g` | zero or more g | print all | check all |
| `GBind x g` | capture to x | emit from x | check g |
| `GNode c args` | push scope, collect AST | push scope, emit AST | check args |

---

## Pattern Matching & Rewriting

### Pattern Matching

```agda
-- Path: Lego.Bindings
Bindings : Type
Bindings = Map String Term

-- Path: Lego.matchPat
matchPat : Term → Term → Maybe Bindings
matchPat (TmVar ('$':x)) t = Just (Map.singleton x t)  -- Pattern var
matchPat (TmLit s) (TmLit s') | s == s' = Just Map.empty
matchPat (TmCon c ps) (TmCon c' ts) | c == c' ∧ length ps == length ts =
  unions <$> zipWithM matchPat ps ts
matchPat _ _ = Nothing
```

### Template Application

```agda
-- Path: Lego.applyTemplate
applyTemplate : Bindings → Term → Term
applyTemplate binds (TmVar ('$':x)) = 
  fromMaybe (TmVar x) (Map.lookup x binds)
applyTemplate binds (TmCon "subst" [TmVar ('$':x), e, body]) =
  let v = applyTemplate binds e
  in applyTemplate (Map.insert x v binds) body
applyTemplate binds (TmCon c ts) = TmCon c (map (applyTemplate binds) ts)
applyTemplate _ t = t
```

### Normalization

```agda
-- Path: Lego.normalize
normalize : List Rule → Term → Term
normalize = normalizeDir Forward

-- Path: Lego.normalizeDir
normalizeDir : RuleDir → List Rule → Term → Term
normalizeDir dir rules = go fuel where
  fuel = 1000  -- termination guarantee via fuel
  
  go 0 t = t
  go n t = let t' = normSub t in
           case step t' of
             Nothing → t'
             Just t'' → go (n-1) t''
  
  normSub (TmCon c args) = TmCon c (map (normalizeDir dir rules) args)
  normSub t = t
  
  step t = builtinStep t <|> firstMatch rules t
  
  firstMatch [] _ = Nothing
  firstMatch (r:rs) t = tryRule t r <|> firstMatch rs t
  
  tryRule t r = do
    binds ← matchPat (rulePattern r) t
    guard (checkGuard binds (ruleGuard r))
    Just (applyTemplate binds (ruleTemplate r))
```

---

## Composition & Pushouts

### Import as Pushout

The `import` directive is syntactic sugar for pushout:

```
import L  ≡  CurrentLang ⊔ L
```

### Compiled Language

```agda
-- Path: Lego.Eval.CompiledLang
data CompiledLang where
  CompiledLang : (clName    : String)                   -- Path: CompiledLang.clName
               → (clVocab   : Set String)               -- Path: CompiledLang.clVocab
               → (clGrammar : Map String (GrammarExpr ())) -- Path: CompiledLang.clGrammar
               → (clRules   : List Rule)                -- Path: CompiledLang.clRules
               → (clTests   : List Test)                -- Path: CompiledLang.clTests
               → (clImports : List String)              -- Path: CompiledLang.clImports
               → CompiledLang
```

### Compiled Language Pushout

```agda
-- Path: Lego.Eval.poCompiledLang
poCompiledLang : CompiledLang → CompiledLang → CompiledLang
poCompiledLang cl1 cl2 = CompiledLang
  { clName    = cl1.clName
  , clVocab   = Set.union cl1.clVocab cl2.clVocab
  , clGrammar = Map.union cl1.clGrammar cl2.clGrammar
  , clRules   = cl1.clRules ++ cl2.clRules
  , clTests   = cl1.clTests ++ cl2.clTests
  , clImports = cl1.clImports ++ cl2.clImports
  }
```

---

## Algebraic Laws

### Monoid Laws (Graph)

```agda
-- Identity
graph_id_l : ∀ g. mempty <> g ≡ g
graph_id_r : ∀ g. g <> mempty ≡ g

-- Associativity
graph_assoc : ∀ f g h. (f <> g) <> h ≡ f <> (g <> h)
```

### Monoid Laws (GrammarExpr via GSeq)

```agda
-- Identity
gseq_id_l : ∀ g. GSeq GEmpty g ≡ g
gseq_id_r : ∀ g. GSeq g GEmpty ≡ g

-- Associativity
gseq_assoc : ∀ g h k. GSeq (GSeq g h) k ≡ GSeq g (GSeq h k)
```

### Pushout Laws (Lang)

```agda
-- Identity
po_id_l : ∀ l. poLang (emptyLang "") l ≡ l
po_id_r : ∀ l. poLang l (emptyLang "") ≡ l

-- Associativity
po_assoc : ∀ l1 l2 l3. poLang (poLang l1 l2) l3 ≡ poLang l1 (poLang l2 l3)

-- Commutativity (up to naming)
po_comm : ∀ l1 l2. poLang l1 l2 ≅ poLang l2 l1
```

### Catamorphism Uniqueness

```agda
-- foldLang is the unique F-algebra homomorphism from initial algebra
fold_unique : ∀ (f : LangF a b → b) (g : Lang a → b).
  (∀ l. g (Lang l) ≡ f (fmap g l)) → g ≡ foldLang f
```

### Bidirectionality Law

```agda
-- Parse and print are inverses (for well-formed terms)
bidir_roundtrip : ∀ g t.
  biParse g (biPrint g t Map.empty) ≡ [(t, [])]
```

---

## Parametric Languages (Functor Category)

### ParamLang

```agda
-- Path: Lego.ParamLang
newtype ParamLang (a t : Type) where
  ParamLang : (instantiate : t → Lang a) → ParamLang a t
```

**Mathematical Structure**: `ParamLang` lives in the functor category `[Type, Lang]`.

### Pointwise Pushout

```agda
-- Path: Lego.poParamLang
poParamLang : ParamLang a t → ParamLang a t → ParamLang a t
poParamLang f g = ParamLang (λ t → poLang (instantiate f t) (instantiate g t))
```

### Contravariant Mapping

```agda
-- Path: Lego.contramapParam
contramapParam : (s → t) → ParamLang a t → ParamLang a s
contramapParam h pl = ParamLang (λ s → instantiate pl (h s))
```

**Functor Laws**:

```agda
-- Identity
param_fmap_id : ∀ F. contramapParam id F ≡ F

-- Composition
param_fmap_comp : ∀ f g F. contramapParam (g ∘ f) F ≡ contramapParam f (contramapParam g F)
```

---

## Token System

### Token Type

```agda
-- Path: Lego.Token.Token
data Token where
  TIdent   : String → Token    -- Path: Token.TIdent (identifier)
  TString  : String → Token    -- Path: Token.TString ("string")
  TSym     : String → Token    -- Path: Token.TSym (symbol)
  TKeyword : String → Token    -- Path: Token.TKeyword (keyword)
  TNewline : Token             -- Path: Token.TNewline
  TIndent  : Int → Token       -- Path: Token.TIndent (indentation level)
```

### Tokenization

```agda
-- Path: Lego.Token.tokenize
tokenize : String → List Token

-- Path: Lego.Token.keywords
keywords : List String
keywords = ["lang", "import", "vocab", "grammar", "rules", "types", "tests",
            "when", "interact", "sig"]

-- Path: Lego.Token.symbols
symbols : List String
symbols = ["::=", ":=", "<~>", "~~>", "<~", "~>", "->", "→", "=>", "<>", "|",
           "*", "(", ")", "[", "]", "{", "}", ":", ".", ",", ";", "$", "<", ">",
           "=", "←", "⊔", "+", "μ", "ε", "===", "⟨", "⟩", "∧", "∨", "¬", "~",
           "∀", "∃", "λ", "Π", "Σ", "\\"]
```

---

## Declaration Types

```agda
-- Path: Lego.LegoDecl
data LegoDecl where
  DLang    : String → List LegoDecl → LegoDecl     -- Path: LegoDecl.DLang
  DImport  : String → LegoDecl                      -- Path: LegoDecl.DImport
  DPushout : String → String → LegoDecl             -- Path: LegoDecl.DPushout
  DVocab   : List String → List String → LegoDecl  -- Path: LegoDecl.DVocab
  DGrammar : String → GrammarExpr () → LegoDecl    -- Path: LegoDecl.DGrammar
  DRule    : Rule → LegoDecl                        -- Path: LegoDecl.DRule
  DType    : TypeRule → LegoDecl                    -- Path: LegoDecl.DType
  DTest    : Test → LegoDecl                        -- Path: LegoDecl.DTest
  DDef     : String → Term → LegoDecl               -- Path: LegoDecl.DDef
```

---

## Testing

### Test Type

```agda
-- Path: Lego.Test
data Test where
  Test : (testName     : String)   -- Path: Test.Test.testName
       → (testInput    : Term)     -- Path: Test.Test.testInput
       → (testExpected : Term)     -- Path: Test.Test.testExpected
       → Test
```

### Test Result

```agda
-- Path: Lego.TestResult
data TestResult where
  Pass : String → TestResult                    -- Path: TestResult.Pass
  Fail : String → Term → Term → TestResult     -- Path: TestResult.Fail
```

### Test Execution

```agda
-- Path: Lego.runTest
runTest : List Rule → Test → TestResult
runTest rules test =
  let actual = normalize rules (testInput test)
  in case matchTerms (testExpected test) actual of
       Just _  → Pass (testName test)
       Nothing → Fail (testName test) (testExpected test) actual

-- Path: Lego.runTests
runTests : List Rule → List Test → List TestResult
runTests rules = map (runTest rules)
```

---

## Builtins

### Core Operations

```agda
-- Path: Lego.Builtins.builtinStep
builtinStep : Term → Maybe Term

-- Beta reduction
builtinStep (TmCon "app" [TmCon "lam" [TmVar x, _, body], arg]) = 
  Just (substTerm x arg body)

-- Pair operations
builtinStep (TmCon "fst" [TmCon "pair" [a, _]]) = Just a
builtinStep (TmCon "snd" [TmCon "pair" [_, b]]) = Just b

-- Boolean operations
builtinStep (TmCon "not" [TmCon "true" []]) = Just (TmVar "false")
builtinStep (TmCon "if" [TmCon "true" [], thn, _]) = Just thn
-- ... etc
```

### Substitution

```agda
-- Path: Lego.Builtins.substTerm
substTerm : String → Term → Term → Term
substTerm x v (TmVar y) | x == y = v
substTerm x v (TmCon c args) = TmCon c (map (substTerm x v) args)
substTerm _ _ t = t
```

---

## Module Structure

### File Organization

```
lego/
├── interpreter/
│   ├── Lego.hs           -- Core types (5 pieces, 3 operations)
│   ├── Lego/
│   │   ├── Internal.hs   -- Fix, ExprF, Term
│   │   ├── Builtins.hs   -- Built-in reductions
│   │   ├── Token.hs      -- Tokenizer
│   │   ├── GrammarDef.hs -- Loads grammar from Grammar.sexpr
│   │   ├── GrammarParser.hs  -- File parser
│   │   ├── GrammarInterp.hs  -- Bidirectional interpreter
│   │   ├── GrammarAnalysis.hs -- Grammar vocabulary extraction
│   │   ├── Eval.hs       -- Rule evaluation
│   │   └── Registry.hs   -- Package/import resolution
│   ├── Main.hs           -- Test runner
│   └── Repl.hs           -- Interactive REPL
├── prelude/              -- Standard library
│   └── lego/Grammar.sexpr -- Portable grammar (source of truth)
├── examples/             -- Example languages
└── phi/                  -- Phi language specs
```

### Module Dependencies

```
Internal ← Builtins ← Lego ← Token ← GrammarDef ← GrammarInterp ← GrammarParser ← Eval
                        ↑                                                          ↑
                        └──────────────────── Registry ────────────────────────────┘
```

---

## References

### Category Theory

- [nLab: Pushout](https://ncatlab.org/nlab/show/pushout)
- [nLab: Initial Algebra](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)
- [nLab: Functor Category](https://ncatlab.org/nlab/show/functor+category)

### Type Theory

- [nLab: Dependent Type](https://ncatlab.org/nlab/show/dependent+type)
- [HoTT Book](https://homotopytypetheory.org/book/)

### Parsing

- [Kleene Algebra](https://en.wikipedia.org/wiki/Kleene_algebra)
- [Bidirectional Programming](https://www.cis.upenn.edu/~bcpierce/papers/lenses-etapsslides.pdf)

### Implementation

- [Wadler: Recursive types for free!](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt)
- [Swierstra: Data Types à la Carte](http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf)

---

## Appendix: Complete Path Index

For proof assistant formalization, here is the complete index of paths:

### Types
```
Lego.Name
Lego.GId
Lego.Port
Lego.Graph
Lego.Internal.Fix
Lego.Internal.ExprF
Lego.KleeneF
Lego.BindF
Lego.AnyF
Lego.:+:
Lego.GrammarF
Lego.GrammarExpr
Lego.Internal.Term
Lego.RuleDir
Lego.Rule
Lego.LangF
Lego.Lang
Lego.TypeRule
Lego.Mode
Lego.BiState
Lego.BiResult
Lego.ParamLang
Lego.Token.Token
Lego.LegoDecl
Lego.Test
Lego.TestResult
Lego.Eval.CompiledLang
```

### Constructors
```
ExprF.EVar, ExprF.ECon, ExprF.ELit, ExprF.ESyn
KleeneF.KEmpty, KleeneF.KSeq, KleeneF.KAlt, KleeneF.KStar
BindF.BRec, BindF.BRef, BindF.BBind
AnyF.EAny
:+:.InL, :+:.InR
Fix.Fix
Graph.Graph
Term.Term
RuleDir.Forward, RuleDir.Backward, RuleDir.Both
Rule.Rule
LangF.LangF
Lang.Lang
TypeRule.TypeRule
Mode.Parse, Mode.Print, Mode.Check
BiState.BiState
BiResult.BiSuccess, BiResult.BiFail
ParamLang.ParamLang
Token.TIdent, Token.TString, Token.TSym, Token.TKeyword, Token.TNewline, Token.TIndent
LegoDecl.DLang, LegoDecl.DImport, LegoDecl.DPushout, LegoDecl.DVocab, LegoDecl.DGrammar, LegoDecl.DRule, LegoDecl.DType, LegoDecl.DTest, LegoDecl.DDef
Test.Test
TestResult.Pass, TestResult.Fail
CompiledLang.CompiledLang
```

### Pattern Synonyms
```
Lego.GEmpty, Lego.GLit, Lego.GSyntax, Lego.GVar, Lego.GNode
Lego.GSeq, Lego.GAlt, Lego.GStar, Lego.GRec, Lego.GRef, Lego.GBind, Lego.GAny
Lego.Internal.TmVar, Lego.Internal.TmCon, Lego.Internal.TmLit, Lego.Internal.TmSyntax
```

### Operations
```
Lego.emptyGraph, Lego.addNode, Lego.addEdge, Lego.poGraph
Lego.gempty, Lego.glit, Lego.gsyntax, Lego.gseq, Lego.galt, Lego.gstar, Lego.grec, Lego.gbind, Lego.gnode
Lego.mkRule, Lego.flipRule, Lego.canForward, Lego.canBackward
Lego.emptyLang, Lego.poLang, Lego.foldLang
Lego.Internal.cata, Lego.Internal.ana
Lego.fix
Lego.poParamLang, Lego.contramapParam
Lego.lookupBind, Lego.insertBind, Lego.pushScope, Lego.popScope, Lego.flattenBinds
Lego.runBiGrammar, Lego.biParse, Lego.biPrint, Lego.biCheck
Lego.matchPat, Lego.applyTemplate, Lego.normalize, Lego.normalizeDir
Lego.Token.tokenize
Lego.runTest, Lego.runTests
Lego.Builtins.builtinStep, Lego.Builtins.substTerm
Lego.Eval.poCompiledLang, Lego.Eval.loadLang, Lego.Eval.evalLego
```
