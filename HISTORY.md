# Git History (from phi-po parent project)

125 commits affecting lego/ directory:

```
462ac81 feat(Eval): use GrammarAnalysis.collectLiterals
192996e refactor: Grammar.sexpr is now the source of truth
6a11808 Fix GenGrammarDef to produce qualified refs in Grammar.sexpr
eb3a771 Wire up Grammar.sexpr as primary grammar source
dddd8d9 Add .lake to gitignore
43dfc86 Add S-expression serialization for grammar
72e1860 Fix isIdentLikeSym to exclude structural MathSymbol operators
dd80383 Clean up Grammar.lego
ff931df Cursor stuff
ee01fb3 interp: Handle 'constr' node same as 'constructor'
a4d3e8f gen: GrammarDef.hs now generated from Grammar.lego
4610da8 GrammarDef generated
33b20b8 Hand-coded parsing removed
e41fd4f Add Π, Σ, ∀ typed binder support to term grammar
64d39c4 Clean up TODOs
d52a82e Grammar-based parsing: 100% redtt library coverage
f27a23c Grammar infrastructure improvements: greedyStar term collection, langDirectBody/pieceDecl wrappers
b405a34 Add C language definitions (Clang, MLIR, Clang2MLIR) with enhanced test syntax
807b9f8 Add boolean calculus to TestExpect and finish location handling
7caeb15 Add enhanced test specification types
31ea0d3 Add structured error types (LegoError)
73355cb Implement rule tracing (normalizeTrace)
9e77336 Add TODO sections to all lego files + error handling roadmap
66aa569 Add executable language TODOs and parser cuts documentation
979306e Normalize more .lego files: move rules inside pieces, use prefix notation
f0839c1 Normalize .lego files with split productions and rules inside pieces
43b4e30 Include file error count in test summary
019870f Improve parse error messages with line/column locations
08caf99 Fix remaining build warnings across lego interpreter
5dacb28 Fix parse-only tests and incomplete pattern matches
c5f96cb Add parenthesized lambda syntax to term/template grammars
07201be Fix redtt-test regression: don't tokenize '/' as regex delimiter
de374a8 Fix infinite loop in def evaluation: TmLit vs TmVar distinction
ab651ab Red moved into langauges
1ee7b56 Fix parsing: hand-coded file parser, proper piece splitting
32cbbb2 Add TRegex, TChar token support and GNode handlers for char/regex/newline/indent
8d34c4b WIP on master: 1bea511 feat(redtt): golden tests for forward-compat surface forms (with/end, V, holes)
1bea511 feat(redtt): golden tests for forward-compat surface forms (with/end, V, holes)
bdf459d RedTT: reach 100% library parse coverage
5504033 RedTT: treat ≃/≈ as qualified-name separators
788eff8 RedTT elim patterns: allow +/slash recursion binders
ebe4465 RedTT: allow + in qualified names; relax decl parse timeout
26601f7 RedTT grammar: slash-qualified binders, Pi telescopes, and safer atom ordering
6f75e22 Improve RedTT parsing coverage
b3f7c37 Interpreter: include GKeyword in FIRST/NULLABLE; reserved literals (e.g., , , ) participate in prediction; stabilizes parsing around keyword boundaries
c22c9ff Reserve  with backticks to prevent greedy <ident>; parse rate ~54% (398/733); failures now inside elim blocks rather than at keyword boundary
4d328c6 Elim: bias to lambda arms in case bodies; coverage unchanged (55%); failures primarily in complex elim blocks
b64dac2 Qualident: allow '^' followed by <number> (e.g., path^1); parse rate remains 55% (407/733); next focus: elim blocks with lambda arms
2b9189e Elim: accept optional leading bar via explicit alternatives; maintain 55% parse rate; remaining failures focus on elim blocks with λ arms
7cc750b Redtt: extend qualident separators (^, ∘) to parse names like not∘not/id/pt and path^1; maintain reserved  and  only in letexpr; overall parse rate 55% (407/733)
ee7f54b Phase 2: Backtick keywords for reserved words (let/in)
2400beb Grammar: Use atom in coeexpr to prevent greedy consumption
782e4e9 Stratified tokenization: atoms + grammar-scoped refinement
5339f7a Add packrat memoization and greedy star for redtt parsing
9724f2c Fix grammar parser: distinguish quoted syntax literals from meta-operators
be7055a Fix grammar parsing: alternation, suffix operators, and literal parens
b281efb Support variable dimensions in comp/coe
6d65bc6 Add opaque modifier for definitions
4bae552 Refine RedTT grammar for better coverage
6fce826 Add medium-priority RedTT grammar constructs
e1decd9 Add high-priority RedTT grammar constructs
4bb1aae Expand RedttParser grammar with critical term constructs
6d3a348 Fix showGrammar to wrap GStar body in parentheses
83396c2 Fix grammar binding scope leakage in GRef
ff235bc Demonstrate fancy redtt features in Redtt.lego
ffef6c2 Add Redtt.lego: language spec for parsing redtt cubical type theory
0719122 Complete Cubical implementation: multiline rules, HITs, coe, RewriteMachine
c444acf Remove duplicate Cubical→INet stub files (keep Cubical2INet.lego)
fa183e1 Comment out speculative tests in compilation pipeline files
7d6b983 Add compilation pipeline: Lambda/Cubical → INet → RewriteMachine
d9500fa Remove Roundtrip.lego (tests not yet working)
7eaf29b Fix all compiler warnings
12076b1 Fix RewriteMachine.hs: Add missing types and complete stubs
daa1049 Cubical.lego: Add explicit dimension grammar (dim, dimvar)
4b5a546 Fix Cubical λᵢ path abstraction parsing and HoTT tests
e6006f9 Separate import (scope) from lang parents (pushout)
a649dde Fix import resolution to use resolved CompiledLangs
b0c9b0f Add example files demonstrating prelude:/code: sections
40c106b Add prelude:/code: sections for function definitions
546476e Fix test parsing: splitAtTopLevelPiece stops at test/rule
866c87d Implement piece composition with inheritance
c1be5a6 Cubical HIT tests: symbol constructors, Torus, Truncation, Quotient, Join
9926e5e Add path reduction rules and composition operations (comp, hcomp, transp)
f3a228c Add cubical Path primitives to ExprF: I, i0, i1, Path, λi, @
19fe4c0 Unify pattern/template via TmLit vs TmVar: $ is surface syntax only
daef715 Simplify metavar: remove angle bracket syntax, consolidate tokPatVar/tokAngleVar/tokAngleDollarVar into tokMetaVar
3493e07 Decommission GrammarParser's takeBalanced: use semantic combinators
2c9fc28 Decommission GrammarParser post-processing: use GrammarInterp bsTerm
61c4a12 Simplify grammar: test syntax to ~~>, remove phi sections, add rule directions
a2c867d lego-v2.0: Add Fix point, unified Term, guards, modal grammar
def7f23 Add CLAUDE.md for Lego language workbench
d610a86 Convert Grammar.lego to valid Lego syntax
f06d1f6 Add Phi as extension of Lego grammar
bb9a348 Fix IO.lego syntax and remove unused exports from GrammarDef.hs
7129ce6 Remove dead code: legoKeywords, legoSymbols from GrammarDef.hs
8bdc00a Fix tokenizer: avoid empty TIdent after $ followed by whitespace
81a98fa Fix warnings in GrammarParser: remove unused functions, fix pattern matches
ec1775a Remove FileParser.hs - consolidated into GrammarParser
c8e6779 Remove parseTests from FileParser (phi-specific)
8c7f35b Decommission FileParser: delegate to GrammarParser
a65aead Remove Phi section-based parsing from FileParser
733e0a8 Add grammar-based file parsing to GrammarParser
5addae5 Remove unused parseLego/parseGrammar stubs
61547b3 Extract builtins to Lego.Builtins module
1cb0aab Eliminate Pattern and Template types: unify with Term
d47182a Unify Term, Pattern, Template, GrammarExpr via Fix + pattern synonyms
79126fe Add TmSyntax/GSyntax distinction for content vs syntax literals
160e715 Refactor: Use grammar-based parseRuleG/parseTestG in FileParser
b81c981 Refactor: Use individual grammars, add test totals, remove phi accommodations
f468428 Consolidate grammar parsing and deduplicate helpers
b1de491 Move String-level parse* functions to GrammarParser
88fc755 Rename Parser.hs → FileParser.hs
a428026 Unplug hard-coded parsers: delegate to grammar interpreter
bfc36d9 Fix import resolution and reorganize lego examples
b9cd60b Add Lego.lego: metacircular self-definition
0afbdc2 Add 31 Lego language extensions in examples/
92a9833 Add Lego REPL for interactive .lego file exploration
45aa87a Unify Lego parser to handle both .lego and .phi syntax
d5f35c1 Add Mode.lego: modal grammar, execution modes, parametric languages
83505d9 Add bidirectional/modal grammar interpretation
78e67fa Add parametric languages to Lego (functor category)
2bd97e9 Implement built-in evaluation rules for Lego
9a6dec2 Fix $var parsing and top-level tests: section
3d17f9b Implement full Lego parser with intra-file import resolution
6fc818e Lego: minimal language for building languages
```
