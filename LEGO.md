# Lego: A Language for Building Languages

> **Status**: Standalone package • 195/234 tests • 725/725 redtt parsing • [lego.cabal](lego.cabal)

## Philosophy

**Necessary and sufficient.** Every construct maps to an algebraic structure.
No syntax sugar that doesn't correspond to a mathematical operation.

## The Five Lego Pieces

| Piece | Math | Symbol | Purpose |
|-------|------|--------|---------|
| **Vocab** | Set | keywords | Reserved words |
| **Grammar** | Free Algebra | `::=` | Syntax as expression |
| **Rules** | Rewrite | `~>` | Computation |
| **Types** | (optional) | `:` | Type annotations |
| **Tests** | Test | `~~>` | Verification |

## The Three Operations

| Op | Math | Symbol | Type |
|----|------|--------|------|
| **Pushout** | Colimit | `⊕` or `+` | `Lang × Lang → Lang` |
| **Sequential** | Composition | `·` | Import order |
| **Parallel** | Product | `‖` | Independent |

---

## Imports = Pushouts (Architecture)

**The central insight:** Language composition is implemented via categorical pushouts.
The `import` directive is syntactic sugar for the pushout operation.

### The Pushout Diagram

```
       A (shared structure)
      / \
     /   \
    L1   L2
     \   /
      \ /
     L1 ⊔ L2  (coequalizer = merged language)
```

### What Gets Pushed Out

```haskell
-- In Lego/Eval.hs:
poCompiledLang :: CompiledLang -> CompiledLang -> CompiledLang
poCompiledLang cl1 cl2 = CompiledLang
  { clVocab   = S.union (clVocab cl1) (clVocab cl2)     -- Set union
  , clGrammar = M.union (clGrammar cl1) (clGrammar cl2) -- Map union
  , clRules   = clRules cl1 ++ clRules cl2              -- List concat
  ...
  }
```

### Syntactic Equivalences

These are **semantically identical**:

```lego
-- Explicit pushout
lang Combined := Arith ⊔ Bool

-- Desugared via imports
lang Combined :=
  import Arith
  import Bool

-- Using + (also parsed as pushout)
lang Combined := Arith + Bool
```

### Why Pushouts?

1. **Commutativity** (up to isomorphism): `L1 ⊔ L2 ≅ L2 ⊔ L1`
2. **Associativity**: `(L1 ⊔ L2) ⊔ L3 = L1 ⊔ (L2 ⊔ L3)`
3. **Identity**: `L ⊔ ∅ = L`
4. **Universal property**: The pushout is the "smallest" language containing both

### Algebraic Laws

```lego
-- In Prelude.lego:
rule pushout_left_id:  ($L ⊔ emptyLang) ~> $L
rule pushout_right_id: (emptyLang ⊔ $L) ~> $L
rule pushout_assoc:    (($A ⊔ $B) ⊔ $C) ~> ($A ⊔ ($B ⊔ $C))
```

---

## Core Syntax

### 1. Names (Set)

```lego
-- Atomic: just identifiers
x, y, z, Type, Kind, lam, app, pi
```

### 2. Graphs (Monoid)

```lego
-- Empty graph (identity)
{}

-- Single node
{ n : label }

-- Edge (port wiring)  
{ n.0 ~ m.1 }

-- Composition (monoidal)
G1 <> G2

-- Pushout (with identification)
G1 ⊔[n₁=n₂] G2
```

**Laws:**
```
{} <> G = G              -- left identity
G <> {} = G              -- right identity
(G1 <> G2) <> G3 = G1 <> (G2 <> G3)  -- associativity
```

### 3. Grammar (Free Algebra)

```lego
-- Empty (ε)
ε

-- Literal token
"token"

-- Constructor (node in graph)
⟨name⟩

-- Sequence (monoidal)
g1 · g2

-- Alternative (coproduct)
g1 | g2

-- Kleene star (free monoid)
g*

-- Recursion (μ)
μX. g[X]

-- Binding (capture)
x ← g
```

**Example:**
```lego
grammar Lam :=
  | "(" "λ" x:Name "." body:Expr ")"  → ⟨lam x body⟩
  | "(" func:Expr arg:Expr ")"        → ⟨app func arg⟩
  | x:Name                            → ⟨var x⟩
```

### 4. Rules (Rewrite System)

```lego
-- Reduction rule
pattern ~> template

-- With guard
pattern ~> template  when guard

-- Substitution in template
[x := arg] body
```

**Example:**
```lego
rules Beta :=
  (app (lam $x $b) $a) ~> [$x := $a] $b
```

### 5. Lang (Initial Algebra)

```lego
lang Name :=
  vocab    { keywords..., symbols... }
  grammar  { productions... }
  rules    { rewrites... }
  types    { judgements... }
```

**Composition:**
```lego
-- Pushout (disjoint union + shared structure)
Lang1 ⊔ Lang2

-- With explicit identification
Lang1 ⊔[Expr = Term] Lang2

-- Fold (catamorphism)
fold f over L
```

---

## Complete Example: Lambda Cube via Lego

### Atomic Pieces

```lego
-- Piece 1: Variables
lang Var :=
  grammar { x:Name → ⟨var x⟩ }

-- Piece 2: Application + Lambda (no types)
lang AppLam :=
  import Var
  grammar {
    | "(" func:E arg:E ")"         → ⟨app func arg⟩
    | "(" "λ" x:Name "." body:E ")" → ⟨lam x body⟩
  }

-- Piece 3: Arrow types  
lang Arrow :=
  import Var
  grammar {
    | "(" dom:T "→" cod:T ")" → ⟨arrow dom cod⟩
  }

-- Piece 4: Polymorphism
lang Poly :=
  import Var
  grammar {
    | "(" "∀" a:Name "." body:T ")" → ⟨forall a body⟩
    | "(" "Λ" a:Name "." body:E ")" → ⟨tlam a body⟩
    | "(" func:E "[" arg:T "]" ")"  → ⟨tapp func arg⟩
  }

-- Piece 5: Dependent types
lang Dep :=
  import Var
  grammar {
    | "(" "Π" x:Name ":" dom:T "." cod:T ")" → ⟨pi x dom cod⟩
    | "(" "Σ" x:Name ":" dom:T "." cod:T ")" → ⟨sigma x dom cod⟩
  }

-- Piece 6: Sorts
lang Sorts :=
  grammar {
    | "Type" → ⟨type⟩
    | "Kind" → ⟨kind⟩
  }
```

### Composed Languages

```lego
-- Simply Typed Lambda Calculus
lang STLC := AppLam ⊔ Arrow
  rules { (app (lam $x $b) $a) ~> [$x := $a] $b }
  types { 
    Γ ⊢ f : (A → B), Γ ⊢ a : A
    ─────────────────────────── App
    Γ ⊢ (app f a) : B
  }

-- System F
lang SystemF := STLC ⊔ Poly
  rules { (tapp (tlam $a $b) $T) ~> [$a := $T] $b }

-- Calculus of Constructions  
lang CoC := AppLam ⊔ Dep ⊔ Sorts
  rules {
    (app (lam $x $t $b) $a) ~> [$x := $a] $b
  }
  types {
    -- PTS rules
    Type : Kind
    Γ, x:A ⊢ B : s
    ─────────────── Pi
    Γ ⊢ (Π x:A.B) : s
  }

-- CIC = CoC + Inductive
lang CIC := CoC ⊔ Inductive
```

### The Lego Diagram

```
        Var
       / | \
      /  |  \
 AppLam Arrow Poly  Dep  Sorts
    \    |    /      |    /
     \   |   /       |   /
      STLC          CoC
        \          / |
         \        /  |
        SystemF  CIC
            \   /
             \ /
            Full
```

---

## Type System (Judgements as Grammar)

```lego
-- Judgement forms
judgement :=
  | ctx:Γ "⊢" term:E ":" type:T     -- typing
  | ctx:Γ "⊢" type:T "type"         -- well-formed
  | type1:T "≡" type2:T             -- equality
  | type1:T "<:" type2:T            -- subtyping

-- Rule syntax
rule Name :=
  premises...
  ──────────── 
  conclusion
```

---

## Interaction Net Backend

```lego
-- Node declaration
node App := { 0:principal, 1:func, 2:arg }
node Lam := { 0:principal, 1:type, 2:body, 3:binder }

-- Interaction rule (active pair)
interact App.0 ~ Lam.0 :=
  -- Rewiring specification
  connect App.2 to each (Share where Share.1 = Lam.3)
  connect App.1 to Lam.2
  delete App, Lam

-- Signature (arity function)
sig Base := { Lam ↦ 3, App ↦ 3 }
sig CoC  := Base ⊔ { Lam ↦ 4, Pi ↦ 4, Sort ↦ 1 }
```

---

## Semantics: What Each Piece Computes

| Construct | Denotation |
|-----------|------------|
| `{}` | `mempty :: Graph` |
| `G1 <> G2` | `mappend :: Graph → Graph → Graph` |
| `G1 ⊔ G2` | `poGraph :: Graph → Graph → Graph` |
| `lang L` | `μ(LangF) :: Lang` |
| `L1 ⊔ L2` | `poLang :: Lang → Lang → Lang` |
| `p ~> t` | `Rule :: (Pattern, Template)` |
| `g1 · g2` | `GSeq :: GrammarExpr` |
| `g1 \| g2` | `GAlt :: GrammarExpr` |
| `fold f L` | `foldLang :: (LangF a → a) → Lang → a` |

---

## Implementation Strategy

### Phase 1: Core (100 lines)

```haskell
-- The 5 pieces as types
data Name = Name String
data Graph = Graph (Set Node) (Set Edge)
data GrammarExpr = ...
data Rule = Rule Pattern Template (Maybe Guard)
data Lang = Lang Vocab Grammar [Rule] [TypeRule]

-- The 3 operations
(<>) :: Graph -> Graph -> Graph      -- monoid
(⊔)  :: Lang -> Lang -> Lang         -- pushout
fold :: (LangF a -> a) -> Lang -> a  -- cata
```

### Phase 2: Parser (50 lines)

```haskell
-- Self-hosting: Lego syntax in Lego
lang Lego :=
  grammar {
    | "lang" name:Name ":=" body:LangBody → ⟨langdef name body⟩
    | lang1:Name "⊔" lang2:Name           → ⟨compose lang1 lang2⟩
    | pat:Pattern "~>" tmpl:Template      → ⟨rule pat tmpl⟩
  }
```

### Phase 3: Evaluator (50 lines)

```haskell
eval :: LegoExpr -> IO Lang
eval (LangDef n b)   = buildLang n b
eval (Compose l1 l2) = poLang <$> resolve l1 <*> resolve l2
eval (Rule p t)      = pure (mkRule p t)
```

---

## Why This Design?

### Necessary
Every construct corresponds to a mathematical operation:
- `<>` = monoid composition
- `⊔` = categorical pushout  
- `~>` = rewrite rule
- `:=` = production (grammar equation)
- `fold` = unique morphism from initial algebra

### Sufficient
These five pieces + three operations can express:
- All of the λ-cube
- Interaction nets
- Type systems (as judgement grammars)
- Proof tactics (as goal transformers)

### No More
No syntax that doesn't correspond to an algebraic structure.
No "convenience" that obscures the mathematics.

---

## Comparison: Haskell vs Lego

| Haskell (current) | Lego (proposed) | Math |
|-------------------|-----------------|------|
| `data Lang = ...` | `lang Name := ...` | μLangF |
| `poLang l1 l2` | `L1 ⊔ L2` | colimit |
| `foldLang f l` | `fold f over L` | cata |
| `Production ...` | `g1 → ⟨con ...⟩` | grammar eq |
| `Rule pat tmpl` | `pat ~> tmpl` | rewrite |
| `instance Monoid Graph` | `G1 <> G2` | monoid |

---

## Self-Hosting Bootstrap

```lego
-- Lego in Lego (meta-circular)
lang Lego :=
  import Var
  
  grammar {
    | "lang" n:Name ":=" b:Body           → ⟨langdef n b⟩
    | "import" n:Name                      → ⟨import n⟩
    | l1:Lang "⊔" l2:Lang                  → ⟨pushout l1 l2⟩
    | "grammar" "{" ps:Prod* "}"           → ⟨grammar ps⟩
    | "rules" "{" rs:Rule* "}"             → ⟨rules rs⟩
    | p:Pattern "~>" t:Template            → ⟨rule p t⟩
    | "⟨" n:Name args:Expr* "⟩"            → ⟨node n args⟩
  }
  
  rules {
    -- Composition is associative
    (pushout (pushout $a $b) $c) ~> (pushout $a (pushout $b $c))
  }
```

---

## Next Steps

1. **Formalize** the denotational semantics (Lego → Set)
2. **Implement** the core 200-line interpreter in Haskell
3. **Bootstrap** the Lego parser in Lego
4. **Port** existing .phi files to .lego format
5. **Prove** adequacy: `⟦_⟧ ∘ parse = id`

The goal: **language construction as algebra**, not programming.

---

## Appendix: Haskell Concept Mapping

Every Haskell concept used in phi-po maps to a Lego construct:

### Types (data/type/newtype)

| Haskell | Lego | Category |
|---------|------|----------|
| `data Graph a` | `Graph` piece | Monoid carrier |
| `data GrammarExpr a` | `Grammar` piece | Free algebra |
| `data RTerm` | `Term` in grammar | Initial algebra object |
| `data LangF p a l` | `Lang` piece | Functor |
| `newtype Lang p a = Lang (LangF ...)` | `lang X := ...` | μLangF (fixed point) |
| `type Env = Map String T` | `Γ : Name → T` | Context (function type) |
| `data ICNode` | `node N := { ports }` | INet node signature |
| `data Rule = Rule Pat Tmpl` | `p ~> t` | Rewrite |
| `type Tactic = ProofState → [ProofState]` | `tactic : State → State*` | Kleisli arrow |

### Type Classes (class/instance)

| Haskell | Lego | Algebra |
|---------|------|---------|
| `instance Monoid Graph` | `G1 <> G2` | Built-in: Graph is a monoid |
| `instance Monoid GrammarExpr` | `g1 · g2` | Built-in: sequence is monoidal |
| `instance Semigroup MetaCtx` | Implicit in `⊔` | Pushout handles merging |
| `instance Functor LangF` | `fold` | Catamorphism requires functor |
| `instance Foldable/Traversable` | `fold` over grammar | Recursion schemes |
| `Eq, Show` | Structural | Decidable equality on terms |

### Higher-Order Functions

| Haskell | Lego | Math |
|---------|------|------|
| `foldLang :: (LangF a → a) → Lang → a` | `fold f over L` | Catamorphism |
| `fmap :: (a → b) → F a → F b` | Implicit in grammar | Functor action |
| `(<$>), (<*>)` | Grammar combinators | Applicative parsing |
| `(>>=), return` | Rule sequencing | Monad (Search) |
| `guard` | `when g` | Guarded rewrite |

### Recursion & Fixed Points

| Haskell | Lego | Math |
|---------|------|------|
| `newtype Lang = Lang (LangF ... Lang)` | `lang` keyword | μ (least fixed point) |
| `μX. GrammarExpr[X]` | `μX. g[X]` | Recursive grammar |
| `fix :: (a → a) → a` | `μ` operator | Fixed-point combinator |
| Pattern recursion in `normalize` | `~>` rules | Rewrite to normal form |

### Algebraic Data Types

| Haskell | Lego | Construction |
|---------|------|--------------|
| `data T = C1 a \| C2 b c` | `T := C1 a \| C2 b c` | Sum of products |
| Pattern matching | LHS of `~>` | Destructuring |
| `case x of ...` | Built into `~>` | Match + rewrite |
| Record syntax `{field = ...}` | `⟨con field1 field2⟩` | Node with named ports |

### Containers

| Haskell | Lego | Use |
|---------|------|-----|
| `Map k v` | Context `Γ` | Environments |
| `Set a` | Implicit in Graph | Node/edge sets |
| `[a]` (lists) | `g*` (Kleene star) | Sequences |
| `Maybe a` | `g \| ε` | Optional |

### Language Extensions Used

| Haskell Extension | Lego Equivalent | Purpose |
|-------------------|-----------------|---------|
| `DeriveFunctor` | Built into `Lang` | Auto-derive fmap |
| `DeriveFoldable` | Built into `fold` | Auto-derive fold |
| `DeriveTraversable` | Built into grammar | Auto-derive traverse |
| `LambdaCase` | Pattern in `~>` | Case on scrutinee |
| `PatternSynonyms` | Grammar productions | Named patterns |
| `RecordWildCards` | `⟨con ..⟩` | Implicit field binding |
| `RankNTypes` / `forall` | Not needed | Lego is first-order |

### What Lego DOESN'T Need

| Haskell Feature | Why Not Needed |
|-----------------|----------------|
| `IO` monad | Languages are pure specifications |
| `StateT`, `ReaderT` | Context passed explicitly in judgements |
| Type classes for polymorphism | Parametric languages handle this |
| GADTs | Grammar + typing rules = indexed types |
| Template Haskell | Self-hosting via `fold` |
| FFI | Languages are abstract |

### The Key Insight

**Haskell is general-purpose; Lego is domain-specific.**

In Haskell, you model language composition using:
- Monoid instances for Graph
- Functor/Foldable for recursion
- Algebraic data types for ASTs
- Type classes for polymorphism
- Monads for effects

In Lego, these are **built-in** because they're the only things you do:
- `<>` is always monoidal composition
- `⊔` is always categorical pushout
- `~>` is always rewriting
- `fold` is always a catamorphism
- Grammar is always a free algebra

**100% coverage**: Every Haskell construct in phi-po has a Lego equivalent.
The difference is that Lego makes the algebra explicit and mandatory.
