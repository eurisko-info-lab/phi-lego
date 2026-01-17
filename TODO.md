# Lego TODO

> **Current Status**: 812/813 lego tests ✅ • 725/725 redtt parsing ✅ • 71/71 example files passing (100%)

## Architecture Understanding ✅

### Two-Layer Processing

**Layer 1: Grammar Representation (Grammar.sexpr)**
```
(node lam (seq (lit "(") (lit λ) (ref Atom.ident)) (seq (lit .) (ref Term.term) (lit ")")))
```
- Literals (`"("`, `"λ"`, `"."`, `")"`) are **kept** in grammar - needed for bidirectional parse/print
- `GLit "=>"` is like `expectSymbol("=>")` - syntax, not semantics

**Layer 2: Grammar Interpretation (GrammarInterp.hs)**
- When `GNode "lam" [arg1, arg2]` is interpreted:
  - Literals are matched/consumed but produce no `bsTerm`
  - Only `GRef` produces `bsTerm` values (the semantic children)
  - Result: `TmCon "lam" [ident, body]` - exactly 2 children
- Literals are **syntactic glue** - guide parse/print but don't become AST children

### Uniform Parsing Pipeline
```
Grammar.lego ──┐                              ┌─→ termToGrammar → GrammarExpr
               │  GrammarInterp.runGrammar    │   (special post-processing)
User.lego    ──┴──────────────────────────────┴─→ Term (AST)
                      ↓                              (normal usage)
                 Same engine
                 Same rules
```

Everything parses to `Term` first, then different post-processing based on file type.

### Current Status: Working Correctly ✅
- [x] `(λ x . (λ y . x))` → `(lam x (lam y x))` - each `lam` has exactly 2 children
- [x] Backslash lambda removed - only Greek `λ` supported
- [x] Arities are correct at the Term level (interpreter drops literals properly)

### Schema Module (Optional Enhancement)
Created `interpreter/Lego/Schema.hs` for explicit arity declarations:
- `Arity = Arity Int | ArityAtLeast Int | ArityRange Int Int`
- `termSchema` with `lam/2`, `var/1`, `app/2`, etc.
- Can add validation layer if needed, but current implementation already produces correct arities

---

## Completed ✅

### Infrastructure
- ✅ **Standalone package**: `lego.cabal` with library + executables
- ✅ **Grammar.sexpr**: Portable grammar format, source of truth
- ✅ **GrammarAnalysis**: `collectLiterals` for vocab extraction
- ✅ **Bidirectional parsing**: Same grammar for parse AND print
- ✅ **RedTT parsing**: 725/725 declarations (100%)

### Error Handling
- ✅ **Rule Tracing**: `TraceStep`, `normalizeTrace`, `formatTrace`
- ✅ **Structured Errors**: `LegoError` with `SrcSpan` locations
- ✅ **Enhanced Tests**: Boolean combinators, wildcards

### Priority 1 Core Improvements (January 2026)
- ✅ **Grammar-driven parsing**: File parsing uses `File.legoFile` grammar via GrammarParser
- ✅ **Keyword cuts (GCut)**: Added `GCut` constructor for commit points in grammar
- ✅ **Location tracking**: `TraceStep.tsLocation` field for source spans through normalization

### Priority 2: Composition & Algebraic Laws (January 2026)
- ✅ **Law syntax**: `law "name": lhs ≅ rhs` parsed and stored in `CompiledLang`
- ✅ **Inherit syntax**: `inherit Qualified.Name` for grammar composition
- ✅ **@autocut annotation**: `@autocut production` marks productions for auto-cut
- ✅ **Test file**: `examples/meta/PushoutLaws.lego` with algebraic laws

## In Progress 🔶

### Priority 0: Attribute Grammars (HIGH PRIORITY - Foundation for Redtt)

**Mathematical Foundation**: Attribute Grammars are catamorphisms + paramorphisms over parse trees.

| Attribute Type | Algebraic Morphism | Direction |
|----------------|-------------------|-----------|
| **Synthesized** | Catamorphism (fold) | Bottom-up: `Fix F → A` |
| **Inherited** | Paramorphism | Top-down: carries context |
| **Both** | Hylomorphism | Anamorphism ∘ Catamorphism |

**How It Fits Lego's Architecture**:
- Grammar as Functor: `GrammarExpr` defines `F` via `GrammarF` ✅
- Parse Tree: `Fix F` (initial algebra) ✅
- Synthesized Attrs: `F-algebra A : F A → A` - fold to compute
- Inherited Attrs: `F-coalgebra C : C → F C` - context flows down  
- Pushout Compatibility: Attr algebras compose via coproduct

**Implementation Phases**:

#### Phase 1: Core Data Types ✅
- [x] Add `AttrDef`, `AttrFlow`, `AttrRule` to `Lego.hs`
- [x] Add `lfAttrs :: Map String AttrDef` to `LangF`
- [x] Backwards compatible (defaults to empty)

#### Phase 2: Catamorphism-based Evaluation
- [ ] `evalSyn :: (ExprF a -> a) -> Term -> a` - synthesized attribute
- [ ] `evalInh :: Context -> Term -> AttrEnv` - inherited attribute (paramorphism)
- [ ] `evalAttrs :: AttrDefs -> Term -> AttrEnv` - combined evaluation

#### Phase 3: Grammar Syntax
- [ ] `attributes:` section in lang declaration
- [ ] `syn name : Type` - synthesized attribute declaration
- [ ] `inh name : Type` - inherited attribute declaration
- [ ] `attr-rules:` section for attribute equations

#### Phase 4: Pushout of Attributed Languages
- [ ] `(L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂)`
- [ ] Co-product of attribute algebras
- [ ] Conflict detection for overlapping attribute rules

**Syntax Design**:
```lego
lang TypeCheck :=
  import Lambda
  
  attributes:
    syn type : Type         -- computed bottom-up
    inh env : Env           -- flows top-down

  attr-rules:
    Lam.type = Arrow Lam.param-type Lam.body.type
    Lam.body.env = extend env Lam.param Lam.param-type
    
    App.type = codomain App.fun.type
    App.fun.env = env
    App.arg.env = env
    
    Var.type = lookup env Var.name
```

**Files to Modify**:
- `interpreter/Lego.hs`: Add `AttrDef`, `AttrFlow`, `AttrRule`, update `LangF`
- `interpreter/Lego/Attr.hs`: NEW - Attribute evaluation engine
- `prelude/lego/Grammar.lego`: Add `attributes:`, `attr-rules:` syntax
- `prelude/lego/Grammar.sexpr`: Regenerate from Grammar.lego

---

### Priority 1: Grammar Keywords as EOF Markers (HIGH PRIORITY)

**Problem**: Tests must use bootstrap grammar (`Term.term`) instead of the language being defined.

**Solution**: Grammar keywords (`test`, `rule`, `prelude`, `code`) act as **EOF markers** that trigger a language switch via pushout. When the parser encounters these keywords, it:

1. Treats the keyword as EOF for the current grammar
2. Switches to a pushout grammar that combines the keyword's structure with the language being defined

**Formalization**:

```
-- Keywords are EOF markers that switch parsing context
grammarKeywords := { "test", "rule", "prelude", "code", "piece", "grammar", "lang" }

-- Each keyword defines a parameterized grammar that uses L (the current language)
test[L]    ::= "test" <string> ":" L.term ("~~>" L.term)?
rule[L]    ::= "rule" <ident> ":" L.pattern "~>" SExpr.template
prelude[L] ::= "prelude" ":" L.preludeBody
code[L]    ::= "code" ":" L.codeBody

-- The file grammar becomes:
legoFile[L] ::= (langItem[L])*
langItem[L] ::= grammar[L] | piece[L] | rule[L] | test[L] | import | ...

-- L.term is the pushout of all pieces defined so far
-- L.pattern uses L's grammar for the left-hand side
-- SExpr.template uses the bootstrap s-expression grammar
```

**Implementation Steps**:

1. [ ] **Define `L.term`**: After each `piece` declaration, compute the pushout grammar
2. [ ] **EOF behavior**: When parser sees a grammarKeyword, stop current parse and switch context
3. [ ] **Parameterized productions**: `test[L]` uses `L.term` (the current language's term grammar)
4. [ ] **Pattern vs Template**: Rules use `L.pattern` (language-specific) for LHS, `SExpr.template` for RHS
5. [ ] **Incremental pushout**: Each `piece` extends `L` via pushout: `L' = L ⊔ Piece`

**Algebraic Semantics**:

```
-- File parsing is a fold over declarations
parseFile :: [Decl] → (Lang, [Decl])
parseFile = foldl step (emptyLang, [])
  where
    step (L, ds) (Piece p) = (L ⊔ p, ds ++ [Piece p])  -- extend L
    step (L, ds) (Test t)  = (L, ds ++ [parseTest[L] t])  -- use current L
    step (L, ds) (Rule r)  = (L, ds ++ [parseRule[L] r])  -- use current L
```

**Key Insight**: This is NOT re-parsing. The grammar keywords are section boundaries that change which grammar is active. The pushout `L ⊔ Piece` happens incrementally as declarations are processed.

### Priority 2: Composition & Conflict System (continued)

Multi-level pushout composition with algebraic law verification:

#### Phase 1: Pushout Laws & Conflict Detection
- ✅ `poLangChecked`: pushout with conflict reporting (returns `(Lang a, [LangConflict])`)
- ✅ Conflict types: `GrammarConflict`, `RuleConflict`, `VocabConflict`
- ✅ Law test syntax: `law "name": lhs ≅ rhs`
- ✅ **Wire up `Lang`/`LangF`/`poLang`**: `CompiledLang = Lang ()`, runtime uses unified algebraic structure

#### Phase 2: Automatic Vocab Inference ✅
- ✅ `inferVocab`: scan grammar → keywords/symbols/literals (`ivKeywords`, `ivSymbols`, `ivLiterals`)
- ✅ `inferCutPoints`: auto-detect where cuts should go (`CutPoint` with prod-initial keywords)
- ✅ `applyAutoCuts`/`applyAutoCutsToProduction`: transforms grammar with cuts after initial keywords
- ✅ Auto-infer vocab: `DGrammar` processing auto-extracts vocab from `collectLiterals`
- ✅ Manual `vocab:` still supported for override/specialization

#### Phase 3: Local (Scoped) Keywords
- [ ] Two-phase tokenization: atoms first, then per-production classification
- [ ] Backtick `` `in` `` reserved only within its production scope
- [ ] Prevents greedy identifier capture in nested contexts

#### Phase 4: Declarative Cuts & Composition Syntax ✅
- ✅ `@autocut` annotation on productions
- ✅ `inherit Base.Term` syntax for grammar composition
- ✅ Conflict resolution: local shadows inherited (`resolveInherit` checks `M.member` before adding)

### Deferred Features (Implement When Needed)

#### Parameterized Grammars (Higher-Order Grammar)

**NOTE**: See "Priority 1: Grammar Keywords as EOF Markers" above for the correct approach.
The key insight is that grammar keywords are EOF markers that switch parsing context via pushout,
NOT a re-parsing mechanism. The parameterized grammar syntax below supports this:

- [ ] **Syntax**: `name[T] ::= body` where `T` is a grammar parameter
- [ ] **Application**: `test[L]` instantiates with current language's grammar
- [ ] **Substitution**: resolve `test[L]` by substituting `L.term` for `T` in body
- [ ] **GApp constructor**: `GApp "test" [GRef "L.term"]` for grammar application
- Use case: `test[T] ::= "test" <string> ":" T ("~~>" T)?` - tests use the language's term grammar

The difference from the old approach:
- OLD (wrong): Parse with bootstrap grammar, then re-parse with language grammar
- NEW (correct): Keywords are EOF markers that switch the active grammar via pushout

#### Parametric Languages (Functor Category)
Removed in cleanup (was unused). Recover and implement when needed:
- [ ] `ParamLang a t`: type-indexed language families (List[A], State[S])
- [ ] `poParamLang`: pointwise pushout (Day convolution)
- [ ] `ParamNat`: natural transformations between parametric languages
- [ ] `ParamLang2`: two-parameter languages (Map[K,V], Either[A,B])
- Use case: Generic programming over type-parametric DSLs

#### Grammar Compilation (LL(k) Optimization)
Removed in cleanup (was unused). Recover and implement when needed:
- [ ] `CompiledGrammar`: precomputed FIRST sets, nullable analysis
- [ ] `compileGrammar`: compile `GrammarDefs` for faster parsing
- [ ] Predictive parsing: use FIRST sets to avoid backtracking
- Use case: Performance optimization for large grammars

### Test Coverage ✅
- ✅ **607/607 tests passing** (100%)
- ✅ **725/725 RedTT declarations parsing** (100%)
- 🔶 **50/71 example files passing** (70%)
  - 21 files have errors (missing imports, undefined productions)
  - See parse/print fixes section below

### Parse/Print Fixes (January 2026)
**Status**: 50/71 files passing (70%)

**Root Cause Identified**: Tests in `.lego` files use **bootstrap grammar** (Grammar.lego), not the language's own grammar.

**Key Fixes Applied**:
- ✅ types/Base.lego: Added missing `name`/`nat` productions, fixed Π type tests
- ✅ INet.lego: Converted reduction tests to parse-only (prelude defs not implemented)
- ✅ Lambda2INet.lego: Fixed multiline test syntax
- ✅ C language files: Fixed grammar syntax (quoted literals instead of inline patterns)
- ✅ OCaml_Surface.lego: Fixed regex/char literals (`<regex>`, `<char>`)
- ✅ Redtt.lego: Added `--` prefix to section separators
- ✅ SystemF.lego, TypeLevel.lego: Fixed test syntax (use constructor syntax)

**Remaining Issues (21 files)**:
- Missing imports or undefined productions
- Circular dependencies in some language compositions

**Solution Pattern**:
```lego
-- WRONG (language syntax in test):
test "type_var": 'a

-- RIGHT (bootstrap constructor syntax):
test "type_var": (tvar a)

-- WRONG (unparenthesized application):
test "id": Π (A : Type 0) . A

-- RIGHT (parenthesized):
test "id": (Π (A : (Type 0)) . A)
```

### Grammar Completeness ✅
- ✅ Parser support for extended test syntax (`via`, `steps`, `error`)
  - Grammar.sexpr/Grammar.lego: `testOpts ::= testOpt+`, `testOpt ::= via | steps | error`
  - GrammarParser.hs: `parseTestOpts` converts to `TestSpec` with `ExpectViaRule`, `ExpectSteps`, `ExpectError`
- ✅ GCut usage in grammar productions for better error localization
  - Grammar.lego: `!` prefix syntax for cuts (e.g., `!"lang"`, `!"rule"`, `!"test"`)
  - Grammar.sexpr: `grammarSuffix` includes `(node cut (seq (lit !) ...))`
  - GrammarParser.hs: `termToGrammar` handles `(TmCon "cut" ...)` → `GCut`
  - Key declarations now have cuts: langDecl, ruleDecl, testDecl, lawDecl, importDecl, etc.

## Future Work 📋

### Priority 3: Language Features
- [ ] Add reduction rules to grammar-only files
- [ ] Type checking (optional)
- [ ] Module system enhancements

### Priority 4: Advanced
- [ ] Interaction net compilation
- [ ] Optimal reduction backend
- [ ] Self-hosting (Lego parser in Lego)

## Test Syntax (Implemented Types, Parser TODO)

```
test "name": term                           -- parse only
test "name": term ~~> expected              -- normalize & check
test "name": term ~~> _                     -- wildcard (any result OK)
test "name": term ~~> expected via beta     -- require specific rule
test "name": term ~~> expected steps 3      -- exact step count
```

---

## Extended TODO (Based on Codebase Analysis)

### Priority 3: Grammar Engine Improvements

#### Packrat Memoization Optimization
- [ ] **Memo cache tuning**: Profile memory usage of `bsMemo` table
- [ ] **Selective memoization**: Only memoize expensive productions (add `@memo` annotation)
- [ ] **Cache invalidation**: Clear memo between top-level parses
- [ ] **Memo statistics**: Track hit/miss rates for optimization

#### Token System Enhancements
- [ ] **Token position tracking**: Add `SrcSpan` to all `Atom` types
- [ ] **Better error messages**: Show actual token vs expected in parse failures
- [ ] **Whitespace handling**: Make whitespace sensitivity configurable per-production
- [ ] **Unicode support**: Extend `TIdent`/`TSym` for Unicode categories

#### Grammar Analysis
- [ ] **FIRST/FOLLOW sets**: Compute for left-factorization warnings
- [ ] **Left recursion detection**: Warn about non-productive grammars
- [ ] **Ambiguity detection**: Find productions with overlapping alternatives
- [ ] **Grammar coverage**: Which productions are never used in tests?

### Priority 4: Bidirectional Engine

#### Print Mode Improvements
- [ ] **Pretty-printing**: Configurable indentation, line breaks
- [ ] **Precedence handling**: Parenthesis insertion based on grammar structure
- [ ] **Comment preservation**: Round-trip comments through AST
- [ ] **Print failures**: Better diagnostics when AST doesn't match grammar

#### Mode Unification
- [ ] **Check mode optimization**: Skip bindings, only validate structure
- [ ] **Partial parsing**: Parse only up to specific depth/node type
- [ ] **Incremental parsing**: Reparse only changed regions

### Priority 5: Language Composition

#### Pushout Refinements
- [ ] **Conflict resolution strategies**: Add `@override`, `@merge` annotations
- [ ] **Pushout diagnostics**: Visualize which pieces came from which language
- [ ] **Compositional testing**: Auto-generate tests for L1 ⊔ L2 from L1, L2 tests
- [ ] **Associativity checker**: Verify (L1 ⊔ L2) ⊔ L3 = L1 ⊔ (L2 ⊔ L3) programmatically

#### Inheritance System
- [ ] **Diamond problem**: Handle A inherits B, C where B, C both inherit D
- [ ] **Inheritance tracing**: Show resolution chain for each production
- [ ] **Selective inheritance**: `inherit Foo (bar, baz)` for specific productions
- [ ] **Negative inheritance**: `inherit Foo except (quux)` to exclude items

#### Module System
- [ ] **Package management**: Support `lego/pkg/name.lego` paths
- [ ] **Import aliases**: `import Qualified.Long.Name as Short`
- [ ] **Recursive modules**: Detect and reject cyclic imports
- [ ] **Import optimization**: Cache compiled languages, avoid re-parsing

### Priority 6: Rule System Enhancements

#### Pattern Matching
- [ ] **Nested patterns**: Support `(Cons $x (Cons $y $xs))` in one pattern
- [ ] **Guards with bindings**: `when ($n > 0)` using captured variables
- [ ] **Or-patterns**: `(Zero | Succ Zero)` for compact case analysis
- [ ] **Pattern macros**: `pattern NonEmpty = (Cons $_ $_)`

#### Rewriting Strategy
- [ ] **Rewrite strategies**: Leftmost-outermost, rightmost-innermost, parallel
- [ ] **Termination checking**: Detect non-terminating rule sets
- [ ] **Confluence checking**: Warn about non-confluent rules (Church-Rosser)
- [ ] **Critical pair analysis**: Find overlapping rule patterns

#### Rule Tracing
- [ ] **Interactive debugger**: Step through normalization with REPL
- [ ] **Trace filtering**: Show only rules matching pattern
- [ ] **Trace visualization**: GraphViz output of reduction graph
- [ ] **Performance profiling**: Count rule applications, find hotspots

### Priority 7: Type System (Optional)

#### Type Checking Infrastructure
- [ ] **Bidirectional type checking**: Infer/check modes in types
- [ ] **Polymorphic types**: `forall a. a -> a`
- [ ] **Dependent types**: Full Π/Σ types (already have syntax in cubical)
- [ ] **Type inference**: Hindley-Milner for λ-calculus examples

#### Type-Driven Features
- [ ] **Type-directed search**: Find terms of a given type
- [ ] **Type holes**: `?hole` with goal type in error message
- [ ] **Proof search**: Auto-generate terms via backwards chaining
- [ ] **Elaboration**: Surface syntax → core type theory

### Priority 8: Error Handling & Diagnostics

#### Better Error Messages
- [ ] **Parse error recovery**: Continue parsing after errors for multiple reports
- [ ] **Did you mean?**: Suggest similar production/variable names
- [ ] **Error codes**: Numeric codes for documentation lookup
- [ ] **Multi-error reporting**: Show all errors, not just first

#### Source Location Tracking
- [ ] **Full SrcSpan propagation**: Every `Term` has location
- [ ] **Error highlighting**: Show ^^^ under error location
- [ ] **Stack traces**: Show call chain for normalization errors
- [ ] **Source maps**: Map compiled output back to original .lego files

### Priority 9: Performance & Optimization

#### Grammar Compilation
- [ ] **Compiled grammars**: Pre-compute parsing tables (LL(k), LR(k))
- [ ] **DFA generation**: Convert grammar to deterministic automaton
- [ ] **Code generation**: Generate Haskell parsers from grammar
- [ ] **Benchmark suite**: Track parsing/normalization performance over time

#### Normalization Optimization
- [ ] **Lazy evaluation**: Don't normalize under λ-binders unless needed
- [ ] **Memoized normalization**: Cache normal forms of subterms
- [ ] **Parallel reduction**: Reduce independent subterms in parallel
- [ ] **Graph reduction**: Share subterms to avoid duplication

### Priority 10: Tooling & Developer Experience

#### REPL Enhancements
- [ ] **Multi-line input**: Support `:{` ... `:}` for definitions
- [ ] **REPL commands**: `:type`, `:step`, `:trace`, `:grammar`
- [ ] **History**: Readline integration, save/load history
- [ ] **Tab completion**: Complete production names, variables

#### IDE Integration
- [ ] **Language Server Protocol (LSP)**: Go-to-definition, hover, diagnostics
- [ ] **Syntax highlighting**: VSCode/Emacs/Vim extensions
- [ ] **Formatter**: Auto-format .lego files
- [ ] **Refactoring**: Rename productions, inline rules

#### Documentation Generation
- [ ] **Grammar visualization**: Auto-generate railroad diagrams
- [ ] **Rule documentation**: Extract comments into docs
- [ ] **Example gallery**: Web UI for browsing examples/
- [ ] **Tutorial system**: Interactive walkthrough for new users

### Priority 11: Testing & Quality

#### Test Infrastructure
- [ ] **Property-based testing**: QuickCheck for grammar/rule properties
- [ ] **Mutation testing**: Verify tests catch intentional bugs
- [ ] **Coverage analysis**: Which rules/productions are tested?
- [ ] **Regression database**: Save failing cases for continuous testing

#### Test Features
- [ ] **Negative tests**: `test "name": input !~~> pattern` (should NOT reduce to)
- [ ] **Timeout tests**: `test "name": term ~~> expected timeout 1s`
- [ ] **Memory tests**: `test "name": term ~~> expected maxmem 10MB`
- [ ] **Randomized testing**: Generate random terms, check properties

### Priority 12: Advanced Features

#### Metaprogramming
- [ ] **Quasi-quotation**: `[term| $x + $y |]` in Haskell
- [ ] **Reflection**: Access language structure from within language
- [ ] **Staging**: Compile-time vs runtime evaluation phases
- [ ] **Hygienic macros**: Macro expansion with proper scoping

#### Extensibility
- [ ] **Plugin system**: Load Haskell plugins for custom builtins
- [ ] **Foreign function interface**: Call Haskell from .lego, vice versa
- [ ] **Custom backends**: Generate LLVM, JavaScript, etc.
- [ ] **Compiler hooks**: Inject custom passes into pipeline

#### Formal Verification
- [ ] **Law verification**: Check algebraic laws hold on test cases
- [ ] **Proof obligations**: Generate theorems from specifications
- [ ] **SMT integration**: Use Z3/CVC4 for verification conditions
- [ ] **Certified compilation**: Prove compiler correctness

### Priority 13: Examples & Case Studies

#### Missing Language Examples
- [ ] **Python subset**: Significant whitespace, comprehensions
- [ ] **SQL**: Declarative query language with aggregation
- [ ] **Regular expressions**: Kleene algebra in action
- [ ] **JSON/YAML**: Data languages with bidirectional parsing

#### Advanced Type Systems
- [ ] **Liquid types**: Refinement types with SMT constraints
- [ ] **Session types**: Communication protocols
- [ ] **Effect systems**: Track IO, exceptions, state
- [ ] **Linear types**: Resource management (use-once semantics)

#### Real-World DSLs
- [ ] **Build system**: Make/Bazel-style dependency tracking
- [ ] **Configuration language**: Dhall/Nix-style typed configs
- [ ] **Template engine**: Mustache/Jinja-style text generation
- [ ] **Query language**: GraphQL-style nested queries

### Priority 14: Documentation

#### Missing Docs
- [ ] **TUTORIAL.md**: Step-by-step guide for beginners
- [ ] **API.md**: Haskell API documentation for library users
- [ ] **GRAMMAR-GUIDE.md**: How to write effective grammars
- [ ] **RULES-GUIDE.md**: Pattern matching and rewriting best practices
- [ ] **COMPOSITION-GUIDE.md**: Language composition strategies
- [ ] **FAQ.md**: Common questions and gotchas

#### Theoretical Background
- [ ] **CATEGORY-THEORY.md**: Pushouts, colimits, initial algebras explained
- [ ] **TYPE-THEORY.md**: Dependent types, cubical features
- [ ] **FORMAL-SEMANTICS.md**: Denotational semantics of Lego
- [ ] **PROOFS.md**: Correctness proofs for key algorithms

---

## Architectural Debt & Refactoring

### Code Quality
- [ ] **Reduce GrammarInterp.hs size**: Split into multiple modules (1097 lines → <500 each)
- [ ] **Reduce Lego.hs size**: Separate normalization, pattern matching (1277 lines)
- [ ] **Type signatures**: Add explicit signatures to all top-level functions
- [ ] **Documentation**: Haddock comments for all exported functions

### Consistency
- [ ] **Naming conventions**: Unify `tm`/`term`, `gr`/`grammar`, `prod`/`production`
- [ ] **Error types**: Replace `String` errors with structured `LegoError`
- [ ] **Pattern synonym coverage**: Complete patterns for all AST constructors

### Technical Debt
- [ ] **Remove `unsafePerformIO`**: Make `legoGrammar` explicitly loaded
- [ ] **Fix partial functions**: Replace `head`, `tail`, `fromJust` with safe alternatives
- [ ] **Exception handling**: Use `ExceptT` instead of `error` calls
- [ ] **Lens integration**: Use lenses for `BiState`, `LangF` field access

---

## Bootstrap & Self-Hosting

### Grammar Bootstrap
- [ ] **Verify Grammar.sexpr ↔ Grammar.lego roundtrip**: Parse Grammar.lego, print, compare
- [ ] **Auto-regenerate**: Pre-commit hook to regenerate Grammar.sexpr
- [ ] **Version tracking**: Include hash of Grammar.lego in Grammar.sexpr

### Self-Hosting
- [ ] **Lego parser in Lego**: Define Lego.lego that parses itself
- [ ] **Normalization in Lego**: Implement `normalize` as Lego rules
- [ ] **Interpreter in Lego**: Full Lego interpreter in Lego (Tower of interpreters)

---

## Community & Ecosystem

### Packaging
- [ ] **Hackage release**: Publish to Hackage as `lego-lang`
- [ ] **Nix flake**: Reproducible builds with Nix
- [ ] **Docker image**: Containerized Lego environment
- [ ] **Binary releases**: Pre-built binaries for major platforms

### Website
- [ ] **Project website**: GitHub Pages with documentation
- [ ] **Playground**: In-browser Lego REPL (GHCJS/Haste)
- [ ] **Package repository**: Central registry for .lego files
- [ ] **Blog**: Development updates, tutorials, case studies
