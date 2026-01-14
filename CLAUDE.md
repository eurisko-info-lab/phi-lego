# Lego: A Minimal Language for Building Languages

## Overview

Lego is a **standalone language workbench** for defining and composing domain-specific languages.
It is a self-contained project with its own cabal file, test suites, and documentation.

**Core insight**: Languages are algebras that compose via categorical pushouts.
The same grammar expression drives parsing AND printing bidirectionally.

## Quick Reference

```bash
# Build & test
cabal build
cabal run lego-test         # .lego file tests (234/234)
cabal test redtt-test       # redtt parsing (725/725)
cabal run lego-repl         # Interactive REPL

# Generate grammar
cabal run gen-grammar-def -- prelude/lego/Grammar.lego > prelude/lego/Grammar.sexpr
```

## The 5 Pieces + 3 Operations

| Piece | Purpose | Algebra |
|-------|---------|---------|
| **Vocab** | Reserved words | Set |
| **Grammar** | Syntax specification | Free algebra |
| **Rules** | Rewrite rules | Term rewriting |
| **Types** | Type annotations | (optional) |
| **Tests** | Verification | Test framework |

| Operation | Symbol | Purpose |
|-----------|--------|---------|
| **Pushout** | `⊕` or `+` | Merge languages |
| **Sequential** | `·` | Import order |
| **Parallel** | `‖` | Independent |

## Directory Structure

```
lego/
├── lego.cabal              -- Package definition (standalone)
├── README.md               -- User documentation
├── interpreter/            -- Haskell implementation
│   ├── Lego.hs             -- Core: Term, GrammarExpr, 5 pieces
│   ├── Lego/
│   │   ├── Internal.hs     -- Fix, ExprF (initial algebra)
│   │   ├── Error.hs        -- Structured errors with source spans
│   │   ├── Builtins.hs     -- substTerm, builtinStep
│   │   ├── Token.hs        -- Tokenizer (Free Monoid)
│   │   ├── Vocabulary.hs   -- Vocab algebra
│   │   ├── GrammarDef.hs   -- Loads from Grammar.sexpr
│   │   ├── GrammarInterp.hs -- Bidirectional parser/printer
│   │   ├── GrammarParser.hs -- .lego file parser
│   │   ├── GrammarAnalysis.hs -- collectLiterals, vocab extraction
│   │   ├── Eval.hs         -- Language loader, normalize
│   │   ├── Registry.hs     -- Import resolution
│   │   ├── SExpr.hs        -- Portable S-expression format
│   │   └── RewriteMachine.hs -- (experimental)
│   ├── Main.hs             -- Test runner
│   └── Repl.hs             -- Interactive REPL
├── prelude/
│   └── lego/
│       ├── Grammar.lego    -- Grammar specification source
│       └── Grammar.sexpr   -- Portable grammar (source of truth)
├── examples/               -- 65 example .lego files
│   ├── basics/             -- Bool, Nat, Lambda, Lists, SKI, Church
│   ├── types/              -- CoC, SystemF, MLTT, Cubical, HoTT
│   ├── advanced/           -- IO, Actors, Async, STM
│   ├── meta/               -- Tactics, Reflection, Staging
│   └── languages/          -- RedttParser, OCaml_Surface, Lisp
├── test/                   -- Test suites
│   └── RedttTest.hs        -- Parses 725/725 redtt declarations
└── docs/                   -- Additional documentation
    ├── MATH.md             -- Category theory foundations
    ├── LEGO.md             -- Full language reference
    └── *.md                -- Various design docs
```

## Module Dependencies

```
Internal ← Builtins ← Lego ← Token ← GrammarDef ← GrammarInterp ← GrammarParser ← Eval
                        ↑                                                          ↑
                        └──────────────────── Registry ────────────────────────────┘
```

See [dependencies.svg](dependencies.svg) for the full graph.

## Syntax Quick Reference

### Grammar Expressions
```
foo ::= "literal"           -- Literal token
      | bar                 -- Reference
      | foo bar             -- Sequence
      | foo | bar           -- Alternative
      | foo*                -- Zero or more
      | foo+                -- One or more
      | foo?                -- Optional
      | "$" ident           -- Metavariable
      | <ident>             -- Built-in token class
```

### Terms (S-expressions)
```
$x                          -- Variable
(con arg1 arg2)             -- Constructor
"string"                    -- String literal
123                         -- Number
```

### Rules
```
rule name:
  pattern ~> template

rule guarded:
  pattern ~> template when (condition)
```

### Tests
```
test "name": input ~~> expected
test "name": input                  -- Parse only
test "name": input ~~> _            -- Wildcard (any result)
```

## Key Concepts

### Bidirectional Grammar
Same grammar for parse AND print:
```lego
var ::= "$" ident
-- Parse: "$x" → (TmVar "x")
-- Print: (TmVar "x") → "$x"
```

### Language Composition
Languages compose via pushouts:
```lego
language Combined := Arith + Bool
-- Gets vocab, grammar, rules from both
```

### Grammar as Source of Truth
- `Grammar.lego` defines the Lego grammar
- `Grammar.sexpr` is the portable compiled form
- `GrammarDef.hs` loads from `.sexpr` at runtime
- Regenerate with: `cabal run gen-grammar-def -- prelude/lego/Grammar.lego`

## Test Status

| Suite | Passing | Total | Notes |
|-------|---------|-------|-------|
| lego-test | 234 | 234 | .lego file tests (100%) |
| redtt-test | 725 | 725 | 100% redtt parsing |

## Development Rules

### Math First
- Name the algebra before writing code
- State the laws (associativity, identity, functoriality)
- Derive operations from universal properties

### Grammar is Expression
- Same grammar for parse AND print
- No procedural parsing code
- Grammar.sexpr is source of truth

### Testing
- Every `.lego` file has tests
- Use wildcards (`~~> _`) when output structure varies
- RedTT test suite validates real-world parsing

## Related Files

| File | Purpose |
|------|---------|
| [README.md](README.md) | User documentation |
| [MATH.md](MATH.md) | Mathematical foundations |
| [LEGO.md](LEGO.md) | Full language reference |
| [TODO.md](TODO.md) | Development roadmap |
| [TOKENIZATION.md](TOKENIZATION.md) | Tokenizer design |
| [dependencies.svg](dependencies.svg) | Module graph |
| [math-concepts.svg](math-concepts.svg) | Math concept map |
