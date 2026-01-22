# Lego: A Minimal Language for Building Languages

## Philosophy

**The more math, the less code and bugs.**

Every feature should be derived from a mathematical structure. If you can't name the algebra, you probably shouldn't write the code. This isn't aesthetic—it's engineering: algebraic laws give you free theorems, compositionality, and test oracles.

**Target leverage: 100-200x** (100 lines of .lego → 10,000-20,000 lines of target code)

## Architecture

Standalone, **minimal, algebraically-principled** language workbench:

```
interpreter/
  Lego.hs              -- Core: Term, GrammarExpr, 5 pieces, 3 operations
  Lego/
    Internal.hs        -- Fix, ExprF (initial algebra)
    Token.hs           -- Tokenizer (free monoid)
    GrammarDef.hs      -- Loads from Grammar.sexpr
    GrammarInterp.hs   -- Bidirectional parser/printer
    GrammarParser.hs   -- .lego file parser
    GrammarAnalysis.hs -- collectLiterals, vocab extraction
    Eval.hs            -- Language loader, normalize
prelude/lego/
  Grammar.lego         -- Grammar specification source
  Grammar.sexpr        -- Portable grammar (SOURCE OF TRUTH)
toy/
  Rosetta/Pipeline.lean -- Code generation from .lego to .lean
  test/Bootstrap.lego   -- Meta-grammar with all algebraic constructs
```

**Key insight**: Syntax is an **expression**, not a procedure. The same grammar drives parsing, printing, and validation bidirectionally.

## The 8 Algebraic Layers

### Layer 1: Core Pieces (5 Pieces + 3 Operations)

| Piece | Purpose | Algebra |
|-------|---------|---------|
| Vocab | Reserved words | Set |
| Grammar | Syntax specification | Free algebra |
| Rules | Rewrite rules | Term rewriting |
| Types | Type annotations | (optional) |
| Tests | Verification | Test framework |

| Operation | Symbol | Purpose |
|-----------|--------|---------|
| Pushout | `⊕` or `+` | Merge languages |
| Sequential | `·` | Import order |
| Parallel | `‖` | Independent |

### Layer 2: Recursion Schemes (Functorial)

```lego
derive cata for term ;           -- Catamorphism (fold)
derive ana for term ;            -- Anamorphism (unfold)
derive hylo for term ;           -- Hylomorphism (ana;cata)
derive para for term ;           -- Paramorphism (fold with original)

derive subst for term with binders = [lam, pi] ;
derive shift for term with binders = [lam, pi] ;
derive normalize for term with fuel = 1000 ;
derive conv for term ;
derive infer for term ;
derive check for term ;
```

**Math**: Grammar defines functor F. Rules define F-algebra. All traversals are catamorphisms.

### Layer 3: Grammar Algebra (Categorical)

```lego
pushout G1 G2 along f ;          -- Colimit (merge grammars)
pullback G1 G2 over f ;          -- Limit (intersect grammars)
quotient G by R ;                -- Quotient by relation
coproduct G1 G2 ;                -- Disjoint union
product G1 G2 ;                  -- Paired terms

Child extends Parent with
  rename a to b,
  hide c,
  override d = expr ;
```

**Math**: Objects = Grammars, Morphisms = Interpretations. Pushout = merge along shared fragment.

### Layer 4: Effect Algebra (Monadic)

```lego
effect E {
  op read : Unit → State ;
  op write : State → Unit ;
}

handler H for E {
  return : A ;
  bind : A ;
}

free F over G ;                  -- Free monad: μX. A + F X
cofree C over G ;                -- Cofree comonad: νX. A × F X
monad M = State S × Reader R ;   -- Monad from specification
monad M = M1 ∘ M2 ;              -- Monad transformer
```

**Math**: Algebraic effects, handlers, Kleisli categories.

### Layer 5: Optics (Profunctorial)

```lego
lens L : S ⟷ A ;                 -- get/set pair
prism P : S ⟷ A ;                -- match/build pair
iso I : A ≅ B ;                  -- Isomorphism
traversal T : S ⟿ A ;            -- Effectful traversal
affine A : S ⤳ A ;               -- At most one target
getter G : S → A ;               -- Read-only
setter S : S ← A ;               -- Write-only
review R : A ↩ S ;               -- Construct from part
```

**Math**: Profunctor optics, van Laarhoven lenses.

### Layer 6: Adjunctions (Universal)

```lego
F ⊣ G : C ⇄ D ;                  -- Adjoint pair
left adjoint F to G ;            -- F preserves colimits (free)
right adjoint G to F ;           -- G preserves limits (forgetful)
forgetful U : Alg → Set ;        -- Forgetful functor
```

**Math**: unit : Id → G∘F, counit : F∘G → Id. Hom(F a, b) ≅ Hom(a, G b).

### Layer 7: Kan Extensions (Ultimate)

```lego
lan F along K ;                  -- Left Kan extension
ran F along K ;                  -- Right Kan extension
yoneda C ;                       -- Yoneda embedding: C → [C^op, Set]
codensity F ;                    -- Codensity monad: Ran_F F
density F ;                      -- Density comonad: Lan_F F
```

**Math**: "All concepts are Kan extensions" - Mac Lane. Substitution = Ran, Shifting = Lan.

### Layer 8: Operads & Natural Transformations

```lego
operad O {
  arity 1 : term ;
  arity 2 : term ;
  compose : term ;
  unit : var ;
}

algebra A over O ;               -- O-algebra structure

α => β : F ⟹ G ;                 -- Natural transformation
dinatural δ : F ⤇ G ;            -- Dinatural (profunctors)
extranatural ε : F ⟾ G ;         -- Extranatural
```

**Math**: Multi-arity operations, coherence, polymorphic functions.

## Grammar Constructs

| Construct | Symbol | Purpose |
|-----------|--------|---------|
| Literal | `"..."` | Match exact text |
| Syntax | `'...'` | Syntax marker (parens, etc.) |
| Keyword | `` `...` `` | Reserved keyword |
| Sequence | `g1 g2` | Sequential match |
| Alternative | `g1 \| g2` | Choice |
| Star | `g*` | Zero or more |
| Reference | `name` | Grammar production reference |
| Bind | `x ← g` | Capture binding |
| Arrow | `→ name` | AST constructor annotation |
| **Cut** | `!g` | Commit point (no backtracking) |

## CRITICAL RULES

### 1. NEVER Hand-Code Parsers or Printers

```
-- FORBIDDEN PATTERNS:
termToLean, termToHaskell, termToRust, termTo*  -- NO
prettyPrint, ppTerm, showTerm                    -- NO
parseExpr, parseStmt, parse*                     -- NO
```

**THE ONLY CORRECT PATTERN:**
```lean
let ast := parseWithGrammar grammar content
let newAst := transform rules ast
let output := printWithGrammar grammar prodName ast
```

### 2. Bootstrap.lego is ONLY for Bootstrap

```
Hardcoded seed grammar ──parses──▶ Bootstrap.lego
                                        │
                                        ▼
                                  Runtime ──parses──▶ ALL other .lego files
```

### 3. Grammar.sexpr is Source of Truth

- `Grammar.lego` is the human-readable source
- `Grammar.sexpr` is the portable compiled form
- NEVER hard-code grammar definitions

### 4. Math First, Code Second

1. **Name the algebra** before writing code
2. **State the laws** (associativity, identity, functoriality)
3. **Derive operations** from universal properties
4. If two things compose, there's a monoid/category hiding

## Build & Test

```bash
# Haskell interpreter
cabal build
cabal run lego-test
cabal run lego-repl

# Lean 4 code generation
cd toy
lake build
lake exe pipeline            # Generate .lean from .lego
lake build CubicalGenerated  # Compile generated code
```

## Module Dependency Order

```
Internal ← Builtins ← Lego ← Token ← GrammarDef ← GrammarInterp ← GrammarParser ← Eval
```

## Code Generation Pipeline

```
.lego source files
       ↓
   Bootstrap.lego (meta-grammar with algebraic constructs)
       ↓
   Parse to Term AST
       ↓
   Transform via cubical2rosetta.lego + rosetta2lean.lego
       ↓
   Pipeline.lean (termToLean printer)
       ↓
   Generated .lean files (Term-rewriting based)
```

## Leverage Metrics

| Input | Output | Leverage |
|-------|--------|----------|
| 100 lines .lego | 10,000 lines .lean | 100x |
| Grammar definitions | Inductive types + traversals | auto |
| `derive subst` | 20+ substitution functions | auto |
| `derive normalize` | Full normalizer with fuel | auto |
| `F ⊣ G` adjunction | unit, counit, laws | auto |

The goal: **Write math, get code.**
