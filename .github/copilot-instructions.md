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

## CRITICAL RULES

### 1. NEVER Hand-Code Parsers or Printers

**WRONG:**
```haskell
parseExpr :: String -> Maybe Term
parseExpr s = case words s of
  ["let", x, "=", ...] -> ...  -- NO! Hand-coded parser
```

**RIGHT:**
```haskell
-- Use grammar-driven parsing
result <- runGrammar grammar "expr" tokens
-- Grammar.sexpr is the source of truth
```

The same grammar must work for BOTH parsing AND printing. If you find yourself writing pattern matches on strings or manual AST construction, STOP. Update the grammar instead.

### 2. NEVER Use `/tmp`

**WRONG:**
```bash
ghc ... > /tmp/output.hs
```

**RIGHT:**
```bash
ghc ... > ./tmp/output.hs
```

Use `./tmp/` (gitignored) for all temporary files. Never use system `/tmp`.

### 3. NEVER Pipe `ghc` or `ghci` Output Through `head`

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
cabal run lego-test         # .lego file tests (195/234)
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
