# Lego: A Minimal Language for Building Languages

## Philosophy

**The more math, the less code and bugs.**

Every feature should be derived from a mathematical structure. If you can't name the algebra, you probably shouldn't write the code. This isn't aesthetic—it's engineering: algebraic laws give you free theorems, compositionality, and test oracles.

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
examples/              -- 65 example .lego files
```

**Key insight**: Syntax is an **expression**, not a procedure. The same grammar drives parsing, printing, and validation bidirectionally.

## The 5 Pieces + 3 Operations

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
| **Cut** | `!g` | Commit point (no backtracking) |

The **GCut** construct (`!g`) is for error recovery. Once a cut succeeds, the parser commits and won't backtrack. Use after keywords for better error messages:
```
fileDecl ::= !("rule" ruleName ":" pattern "~>" template)
```

## CRITICAL RULES

### 1. NEVER Hand-Code Parsers or Printers

**STOP. READ THIS BEFORE WRITING ANY CODE.**

If you are about to write ANY of these patterns, you are doing it wrong:

```
-- FORBIDDEN PATTERNS (if you write these, you have failed):
termToLean, termToHaskell, termToRust, termTo*  -- NO
prettyPrint, ppTerm, showTerm                    -- NO
parseExpr, parseStmt, parse*                     -- NO
case t of .con "foo" args -> "foo " ++ ...       -- NO
match t with | .con name args => s!"{name}..."   -- NO
```

**THE ONLY CORRECT PATTERN:**

```lean
-- Parse: grammar → tokens → AST
let ast := parseWithGrammar grammar content

-- Transform: rules → AST → AST  
let newAst := transform rules ast

-- Print: grammar → AST → tokens
let tokens := printWithGrammar grammar prodName ast
```

**Grammar is the parser. Grammar is the printer. There is no third option.**

If `printWithGrammar` fails, the problem is:
1. Your transformation rules produce wrong AST shape, OR
2. Your target grammar is incomplete

Fix the `.lego` files. Do NOT add a "fallback" hand-coded printer.

### 2. Bootstrap.lego is ONLY for Bootstrap

**THE BOOTSTRAP CHAIN:**
```
Hardcoded seed grammar ──parses──▶ Bootstrap.lego
                                        │
                                        ▼
                                  Runtime Grammar ──parses──▶ ALL other .lego files
```

**Bootstrap.lego defines the meta-grammar.** It is parsed ONCE at startup by the hardcoded seed. The result is the Runtime, which parses everything else.

**NEVER use Bootstrap to parse arbitrary .lego files:**
```lean
-- WRONG: Bootstrap only parses Bootstrap.lego
let ast := Bootstrap.parseLegoFile rosettaContent  -- NO!

-- RIGHT: Use Runtime (which was loaded from Bootstrap.lego)
let rt ← loadBootstrapOrFallback  -- This loads Bootstrap.lego ONCE
let ast := parseLegoFile rt content  -- Runtime parses everything else
```

If you call `Bootstrap.parseLegoFile` on anything other than Bootstrap.lego itself, you are doing it wrong.

### 3. NEVER Use `/tmp`

**WRONG:**
```bash
ghc ... > /tmp/output.hs
```

**RIGHT:**
```bash
ghc ... > ./tmp/output.hs
```

Use `./tmp/` (gitignored) for all temporary files. Never use system `/tmp`.

### 4. NEVER Pipe `ghc` or `ghci` Output Through `head`

**WRONG (HANGS):**
```bash
ghc -e "..." | head
ghci ... | head -20
```

**RIGHT:**
```bash
ghc -e "..." | tail
ghc -e "..." | grep pattern
ghc -e "..." > ./tmp/out.txt && head ./tmp/out.txt
```

GHC detects broken pipes and hangs. Always use `tail`, `grep`, or redirect to file first.

### 4. Grammar.sexpr is Source of Truth

- `Grammar.lego` is the human-readable source
- `Grammar.sexpr` is the portable compiled form
- `GrammarDef.hs` loads from `.sexpr` at runtime
- Regenerate with: `cd .. && cabal run gen-grammar-def -- lego/prelude/lego/Grammar.lego > lego/prelude/lego/Grammar.sexpr`

NEVER hard-code grammar definitions in Haskell. If Grammar.sexpr is missing, ERROR—don't fall back.

## Build & Test

```bash
cabal build
cabal run lego-test         # .lego file tests (234/234)
cabal test redtt-test       # redtt parsing (725/725)
cabal run lego-repl         # Interactive REPL
```

## Development Rules

### Math First
- **Name the algebra** before writing code
- **State the laws** (associativity, identity, functoriality)
- **Derive operations** from universal properties when possible
- If two things compose, there's probably a monoid/category hiding

### Testing Philosophy

| Category | Purpose | When broken |
|----------|---------|-------------|
| **Laws** | Algebraic axioms | Algebra is wrong |
| **Unit tests** | Structural preservation | Something basic broke |
| **Demo tests** | Showcase capabilities | Feature incomplete |

### Git
- **Squash fixes** into their originating commit
- Each commit = one well-isolated feature

### Code Safety
- **Fuel pattern** for potentially infinite loops:
  ```haskell
  normalize' :: Int -> Term -> Term
  normalize' 0 t = t  -- fuel exhausted
  normalize' n t = maybe t (normalize' (n-1)) (step t)
  ```

### Bidirectional Design
- Same grammar for parse AND print
- `→` annotation defines AST mapping in both directions
- No separate parser and printer code paths

## Module Dependency Order

```
Internal ← Builtins ← Lego ← Token ← GrammarDef ← GrammarInterp ← GrammarParser ← Eval
```

When adding features, respect this order. Lower modules should not import higher ones.

## Cubical Code Generation Pipeline

The `toy/` directory contains a Lean 4 implementation with Rosetta code generation:

```
.red / .cooltt files (user source code)
       ↓
   Red.lego / Cool.lego (parsers, extend CubicalTT.lego)
       ↓
   Cubical Term AST
       ↓
   cubical2rosetta.lego (Cubical → Rosetta transforms)
       ↓
   Rosetta AST (generic: Var, Lam, App, Pair, adtDef...)
       ↓
   rosetta2lean.lego (Rosetta → Lean)
       ↓
   .lean files
```

### Key Files

| File | Location | Purpose |
|------|----------|---------|
| **CubicalTT.lego** | `toy/src/Lego/Cubical/` | Shared cubical grammar (dims, cofs, paths, Kan ops) |
| **Red.lego** | `toy/src/Lego/Cubical/` | redtt extensions (imports CubicalTT) |
| **Cool.lego** | `toy/src/Lego/Cubical/` | cooltt extensions (imports CubicalTT) |
| **cubical2rosetta.lego** | `toy/src/Rosetta/` | Transform cubical constructs → Rosetta primitives |
| **rosetta2lean.lego** | `toy/src/Rosetta/` | Transform Rosetta → Lean syntax |
| **Rosetta.lego** | `toy/src/Rosetta/` | Generic Rosetta primitives (Var, Lam, App, Pair, etc.) |

### Separation of Concerns

- **Bootstrap.lego parsing** is Lego's internal concern (how `.lego` files are parsed)
- **CubicalTT/Red/Cool** define the source language grammars + semantics
- **cubical2rosetta + rosetta2lean** are the transformers you modify for code generation
- Rosetta is **target-agnostic**: no Lean-specific or cubical-specific constructs
