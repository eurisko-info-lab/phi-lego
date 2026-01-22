# Lego: Rebuild Prompt

**Use this prompt to reconstruct the Lego language workbench from scratch.**

---

## System Prompt

You are building Lego, a minimal algebraically-principled language workbench. The core philosophy: **The more math, the less code.** Every feature should be derived from a mathematical structure. Target leverage is 100-200x (100 lines of input → 10,000-20,000 lines of output).

---

## Phase 1: Core (Internal.hs)

Build the initial algebra for terms:

```haskell
-- The one true pattern: Fix point of a functor
newtype Fix f = In { out :: f (Fix f) }

-- Catamorphism: THE universal fold
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = alg . fmap (cata alg) . out

-- Term functor
data ExprF a
  = Atom String                    -- Leaf
  | List [a]                       -- Node with children
  deriving (Functor, Foldable, Traversable)

type Expr = Fix ExprF

-- Smart constructors
atom :: String -> Expr
list :: [Expr] -> Expr
```

**Law**: `cata alg . In = alg . fmap (cata alg)`

---

## Phase 2: Grammar as Data (GrammarDef.hs)

Grammar is an expression, not a procedure:

```haskell
data GrammarExpr
  = Lit String            -- "exact"
  | Key String            -- Reserved keyword
  | Syn String            -- Syntax marker (parens)
  | Ref String            -- Reference to production
  | Seq [GrammarExpr]     -- g1 g2 ...
  | Alt [GrammarExpr]     -- g1 | g2
  | Star GrammarExpr      -- g*
  | Bind String GrammarExpr  -- x <- g
  | Arrow String          -- → constructor
  | Cut GrammarExpr       -- ! commit point
```

Load grammar from portable S-expression format (Grammar.sexpr).

---

## Phase 3: Bidirectional Interpretation (GrammarInterp.hs)

**ONE grammar drives BOTH parsing and printing:**

```haskell
-- Parse: String → Maybe (Term, String)
parseWith :: Grammar → String → String → Maybe (Term, String)

-- Print: Term → Maybe String  
printWith :: Grammar → String → Term → Maybe String
```

Key insight: Parsing and printing are adjoint functors over the same grammar.

---

## Phase 4: The 5 Pieces (Lego.hs)

A `.lego` file has exactly 5 pieces:

```
Vocab { ... }      -- Reserved words (Set)
Grammar { ... }    -- Syntax specification (Free algebra)
Rules { ... }      -- Rewrite rules (Term rewriting system)
Types { ... }      -- Optional type annotations
Tests { ... }      -- Verification
```

Three composition operations:

| Operation | Symbol | Purpose |
|-----------|--------|---------|
| Pushout | `⊕` or `+` | Merge languages (colimit) |
| Sequential | `·` | Import order |
| Parallel | `‖` | Independent |

---

## Phase 5: Bootstrap Grammar

Create `Bootstrap.lego` as the meta-grammar. It defines the syntax for defining syntax. This is the seed:

```lego
Grammar Bootstrap {
  -- Basic declarations
  decl = grammarDecl | rulesDecl | vocabDecl | typesDecl | testsDecl ;
  
  -- The 8 algebraic layers:
  decl = deriveDecl | algebraDecl | effectDecl | opticsDecl 
       | adjunctionDecl | kanDecl | operadDecl | natDecl ;
}
```

---

## Phase 6: The 8 Algebraic Layers

### Layer 1: Recursion Schemes

```lego
deriveDecl = `derive` deriveKind `for` name deriveMod* `;` ;
deriveKind = `cata` | `ana` | `hylo` | `para` 
           | `subst` | `shift` | `map` | `fold`
           | `conv` | `eq` | `infer` | `check` | `normalize` | `eval` ;
deriveMod = `with` name `=` deriveMVal ;
```

**Math**: Grammar defines functor F. Rules define F-algebra. Traversals = catamorphisms.

### Layer 2: Grammar Algebra

```lego
algebraDecl = pushoutDecl | pullbackDecl | quotientDecl 
            | coproductDecl | productDecl | extendsDecl ;
pushoutDecl = `pushout` name name `along` name `;` ;
extendsDecl = name `extends` name `with` extendsMod* `;` ;
```

**Math**: Category of grammars. Pushout = merge along shared fragment.

### Layer 3: Effects

```lego
effectDecl = `effect` name `{` effectOp* `}` ;
handlerDecl = `handler` name `for` name `{` handlerCase* `}` ;
freeDecl = `free` name `over` name `;` ;
cofreeDecl = `cofree` name `over` name `;` ;
monadDecl = `monad` name `=` monadSpec `;` ;
```

**Math**: Algebraic effects, handlers, free monads.

### Layer 4: Optics

```lego
opticsDecl = lensDecl | prismDecl | isoDecl | traversalDecl ;
lensDecl = `lens` name `:` name `⟷` name `;` ;
prismDecl = `prism` name `:` name `⟷` name `;` ;
isoDecl = `iso` name `:` name `≅` name `;` ;
```

**Math**: Profunctor optics, van Laarhoven lenses.

### Layer 5: Adjunctions

```lego
adjunctionDecl = name `⊣` name `:` name `⇄` name `;` ;
leftAdjDecl = `left` `adjoint` name `to` name `;` ;
rightAdjDecl = `right` `adjoint` name `to` name `;` ;
forgetfulDecl = `forgetful` name `:` name `→` name `;` ;
```

**Math**: unit : Id → G∘F, counit : F∘G → Id.

### Layer 6: Kan Extensions

```lego
lanDecl = `lan` name `along` name `;` ;
ranDecl = `ran` name `along` name `;` ;
yonedaDecl = `yoneda` name `;` ;
codensityDecl = `codensity` name `;` ;
densityDecl = `density` name `;` ;
```

**Math**: "All concepts are Kan extensions" - Mac Lane.

### Layer 7: Operads

```lego
operadDecl = `operad` name `{` operadOp* `}` ;
operadAlgDecl = `algebra` name `over` name `;` ;
```

**Math**: Multi-arity operations with composition.

### Layer 8: Natural Transformations

```lego
natDecl = name `=>` name `:` name `⟹` name `;` ;
dinatDecl = `dinatural` name `:` name `⤇` name `;` ;
extranatDecl = `extranatural` name `:` name `⟾` name `;` ;
```

**Math**: Polymorphic functions between functors.

---

## Phase 7: Code Generation Pipeline

Build `Pipeline.lean` that:

1. Parses `.lego` files to Term AST
2. Transforms via rule specifications
3. Generates target language (Lean 4, Haskell, Rust, etc.)

Key handlers:

```lean
-- For each algebraic construct, generate the appropriate code
genDerive (kind : String) (target : String) → String
genPushout (g1 g2 : String) → String
genLens (name source target : String) → String
genAdjunction (f g : String) → String
genLan (f k : String) → String
-- etc.
```

---

## Phase 8: Leverage Targets

| Construct | Input | Output |
|-----------|-------|--------|
| `derive subst for term` | 1 line | 20+ substitution functions |
| `derive normalize for term` | 1 line | Full normalizer with fuel |
| `F ⊣ G : C ⇄ D` | 1 line | unit, counit, adjunction laws |
| `lan F along K` | 1 line | Left Kan extension + universal property |
| `lens L : S ⟷ A` | 1 line | get, set, over, laws |
| Grammar definition | ~50 lines | Parser, printer, inductive types |

---

## Critical Rules

### 1. NEVER Hand-Code Parsers or Printers

```
-- FORBIDDEN:
termToLean, parseExpr, prettyPrint, showTerm

-- CORRECT:
parseWithGrammar, printWithGrammar
```

### 2. Math First

Before writing code:
1. Name the algebra
2. State the laws
3. Derive from universal properties

### 3. Single Source of Truth

```
Grammar.lego (human readable)
    ↓ compile
Grammar.sexpr (portable, machine readable)
    ↓ load
Runtime grammar (drives all parsing/printing)
```

---

## Verification Checklist

- [ ] `cata` is the only explicit recursion
- [ ] Grammar drives both parsing AND printing
- [ ] Every feature maps to named algebra
- [ ] Leverage ≥ 100x on realistic examples
- [ ] No hardcoded term-to-target functions
- [ ] All 8 algebraic layers implemented

---

## Example: Full Type Theory in 150 Lines

```lego
-- TypeTheoryFromMath.lego
-- Complete dependent type theory from pure categorical constructs

-- 1. Base category structure
product Unit Type ;                    -- Unit type
coproduct Void Type ;                  -- Empty type  

-- 2. Function space from adjunction
Curry ⊣ Apply : Type×Type ⇄ Type ;     -- Π types

-- 3. Dependent types from fibrations
Pi := codensity Apply ;                -- Π via Kan
Sigma := lan Apply along proj ;        -- Σ via Kan

-- 4. Identity from path space
lens PathSpace : A×A ⟷ Path A ;        -- Path as lens

-- 5. Universes from Yoneda
yoneda Type ;                          -- Type : Type (careful!)

-- 6. Recursion from initial algebras
derive cata for term ;
derive normalize for term ;

-- ... generates 10,000+ lines of implementation
```

---

**Remember**: The goal is not to write code. The goal is to write math that generates code.
