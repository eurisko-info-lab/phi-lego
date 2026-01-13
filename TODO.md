# Lego TODO

> **Current Status**: 201/240 lego tests • 725/725 redtt parsing (100%)

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

### Priority 2: Composition & Conflict System (continued)

Multi-level pushout composition with algebraic law verification:

#### Phase 1: Pushout Laws & Conflict Detection
- ✅ `poLangChecked`: pushout with conflict reporting (returns `(Lang a, [LangConflict])`)
- ✅ Conflict types: `GrammarConflict`, `RuleConflict`, `VocabConflict`
- ✅ Law test syntax: `law "name": lhs ≅ rhs`
- ✅ **Wire up `Lang`/`LangF`/`poLang`**: `CompiledLang = Lang ()`, runtime uses unified algebraic structure

#### Phase 2: Automatic Vocab Inference
- [ ] `inferVocab`: scan grammar → keywords/symbols/literals
- [ ] `inferCutPoints`: auto-detect where cuts should go (after prod-initial keywords)
- [ ] Remove manual `vocab:` when derivable from grammar

#### Phase 3: Local (Scoped) Keywords
- [ ] Two-phase tokenization: atoms first, then per-production classification
- [ ] Backtick `` `in` `` reserved only within its production scope
- [ ] Prevents greedy identifier capture in nested contexts

#### Phase 4: Declarative Cuts & Composition Syntax
- ✅ `@autocut` annotation on productions
- ✅ `inherit Base.Term` syntax for grammar composition
- [ ] Conflict resolution: local shadows inherited

### Deferred Features (Implement When Needed)

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

### Test Coverage (195/234 = 83%)
- 39 failing tests in `.lego` files
- Most are grammar-only files needing reduction rules
- See [EXECUTABLE-STATUS.md](EXECUTABLE-STATUS.md) for details

### Grammar Completeness
- Parser support for extended test syntax (`via`, `steps`)
- GCut usage in grammar productions for better error localization

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
