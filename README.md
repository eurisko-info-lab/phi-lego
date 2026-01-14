# Lego: A Minimal Language for Building Languages

[![Tests](https://img.shields.io/badge/tests-234%2F234-green)](test/)
[![RedTT](https://img.shields.io/badge/redtt-725%2F725-brightgreen)](test/RedttTest.hs)

**Lego** is a declarative language workbench where syntax is an expression, not a procedure.
The same grammar drives parsing, printing, and validation bidirectionally.

## Quick Start

```bash
# Build
cabal build

# Run all .lego file tests
cabal run lego-test

# Run redtt parsing tests (cubical type theory)
cabal test redtt-test

# Interactive REPL
cabal run lego-repl

# Regenerate Grammar.sexpr (from parent project)
# cd .. && cabal run gen-grammar-def -- lego/prelude/lego/Grammar.lego > lego/prelude/lego/Grammar.sexpr
```

## Philosophy

**The more math, the less code and bugs.**

Lego is built on the principle that languages should compose algebraically.
Instead of writing parsers procedurally, you declare grammars as expressions
that work bidirectionally for both parsing AND printing.

### The 5 Pieces

Every language in Lego is composed from 5 types of pieces:

| Piece | Purpose | Example |
|-------|---------|---------|
| **Vocab** | Reserved words & symbols | `keywords: let in where` |
| **Grammar** | Syntax specification | `expr ::= "let" ident "=" expr "in" expr` |
| **Rules** | Rewrite/reduction rules | `(add zero $n) ~> $n` |
| **Types** | (Optional) Type annotations | `add : Nat → Nat → Nat` |
| **Tests** | Verification | `test: (add zero one) ~~> one` |

### The 3 Operations

Pieces compose via three algebraic operations:

| Operation | Symbol | Purpose |
|-----------|--------|---------|
| **Pushout** | `⊕` or `+` | Merge two languages (disjoint union + identification) |
| **Sequential** | `·` | Import order (later shadows earlier) |
| **Parallel** | `‖` | Independent composition |

## Example: Boolean Language

```lego
language Bool

piece BoolGrammar
  bool ::= "true" | "false"
  expr ::= "if" expr "then" expr "else" expr
         | bool
end

rule if_true:
  (if true $then $else) ~> $then

rule if_false:
  (if false $then $else) ~> $else

test "if-true": (if true 1 2) ~~> 1
test "if-false": (if false 1 2) ~~> 2
```

## Project Structure

```
lego/
├── lego.cabal          -- Package definition
├── README.md           -- This file
├── interpreter/        -- Haskell implementation
│   ├── Lego.hs         -- Core types (Term, GrammarExpr)
│   ├── Lego/
│   │   ├── Internal.hs     -- Fix, ExprF (initial algebra)
│   │   ├── Token.hs        -- Tokenizer
│   │   ├── GrammarDef.hs   -- Loads grammar from Grammar.sexpr
│   │   ├── GrammarInterp.hs -- Bidirectional parser/printer
│   │   ├── GrammarParser.hs -- .lego file parser
│   │   ├── GrammarAnalysis.hs -- Grammar vocabulary extraction
│   │   ├── Eval.hs         -- Language loader, normalize
│   │   └── SExpr.hs        -- Portable S-expression format
│   ├── Main.hs         -- Test runner
│   └── Repl.hs         -- Interactive REPL
├── prelude/            -- Standard library
│   └── lego/
│       ├── Grammar.lego    -- Grammar specification
│       └── Grammar.sexpr   -- Portable grammar (source of truth)
├── examples/           -- Example languages
│   ├── basics/         -- Bool, Nat, Lambda, Lists, etc.
│   ├── types/          -- CoC, SystemF, MLTT, Cubical, etc.
│   ├── advanced/       -- IO, Actors, STM
│   └── meta/           -- Tactics, Reflection, Staging
├── test/               -- Test suites
│   └── RedttTest.hs    -- Parses 725/725 redtt declarations
└── docs/               -- Documentation
    ├── CLAUDE.md       -- AI assistant context
    ├── MATH.md         -- Mathematical foundations
    └── LEGO.md         -- Language reference
```

## Key Features

### Bidirectional Grammar

The same grammar expression works for both parsing and printing:

```lego
-- Grammar
var ::= "$" ident

-- Parse: "$x" → (TmVar "x")
-- Print: (TmVar "x") → "$x"
```

### Pattern Matching in Rules

Rules use pattern variables (`$x`) for structural matching:

```lego
rule beta:
  (app (lam $x $body) $arg) ~> (subst $x $arg $body)
```

### Language Composition

Languages compose via pushouts (categorical colimits):

```lego
-- Arith has: Nat, add, mul
-- Bool has: true, false, if

language Combined := Arith + Bool

-- Combined has everything from both!
test: (if true (add 1 2) 0) ~~> 3
```

### Test-Driven Development

Every `.lego` file can include tests:

```lego
test "basic": (foo bar) ~~> expected
test "parse-only": (foo bar)              -- Just check it parses
test "wildcard": (complex expr) ~~> _     -- Any result OK
```

## Documentation

| File | Purpose |
|------|---------|
| [CLAUDE.md](CLAUDE.md) | AI assistant context & quick reference |
| [MATH.md](MATH.md) | Mathematical foundations (category theory, initial algebras) |
| [LEGO.md](LEGO.md) | Full language reference |
| [TODO.md](TODO.md) | Development roadmap |
| [TOKENIZATION.md](TOKENIZATION.md) | Tokenizer design notes |

## Module Dependency Graph

See [dependencies.svg](dependencies.svg) for the full graph.

```
Internal ← Builtins ← Lego ← Token ← GrammarDef ← GrammarInterp ← GrammarParser ← Eval
```

## Mathematical Foundations

Lego is built on solid category-theoretic foundations:

- **Terms**: Initial algebra of `ExprF` functor (`Term = Fix ExprF`)
- **Grammars**: Free algebra over BNF operations
- **Composition**: Pushouts in the category of languages
- **Reduction**: Catamorphisms (folds) over term structure

See [math-concepts.svg](math-concepts.svg) for the concept map.

## Status

| Component | Status | Notes |
|-----------|--------|-------|
| Grammar interpreter | ✅ | Bidirectional parse/print |
| Rule evaluation | ✅ | Pattern matching + substitution |
| Language composition | ✅ | Pushout-based imports |
| Test framework | ✅ | Wildcards, traces |
| RedTT parsing | ✅ | 725/725 (100%) |
| Lego file tests | ✅ | 234/234 (100%) |

## License

MIT
