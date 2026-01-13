# Tokenization TODO

> **Status**: Phase 2 DONE • RedTT parsing: 725/725 (100%)

## Current State: Complete

- [x] **Phase 1**: Lexer produces atoms (`tokenizeWithKeywords False`)
- [x] **Phase 2**: `GrammarAnalysis.collectLiterals` extracts vocab from grammar
- [x] **Phase 2**: `<ident>` rejects keywords via `isIdentLikeSym` check
- [x] Grammar matches both TIdent and TKeyword permissively
- [x] Redtt uses atoms, Lego uses classified
- [x] **725/725 (100%)** redtt declarations parse

### Problem Solved: Greedy `<ident>` Matching
- **Issue**: `<ident>` matched ALL TIdent, including reserved words like `in`
- **Solution**: `isIdentLikeSym` in GrammarInterp excludes structural operators
- **Result**: Nested let expressions now parse correctly

---

## Phase 2: Keyword Extraction (DONE)

### Goal
Make `<ident>` reject reserved keywords to stop greedy matching.

### Implementation (Completed)

#### Path A: Pragmatic (Use Now) - DONE
Use existing `"..."` syntax + token classification:
1. Extract keywords: `collectLiterals :: GrammarDefs -> S.Set String` (via GrammarAnalysis)
2. Classify tokens: `classifyKeywords keywords tokens`
3. Update `<ident>` matching: reject `TKeyword`
4. No grammar changes needed!

**Status**: Implemented in Eval.hs - uses `GrammarAnalysis.collectLiterals`

#### Path B: Ideal (Full Triple-Quote) - FUTURE
Implement semantic quote types in grammar files:
1. Update tokenizer to recognize `` `...` ``, `'...'`, `"..."`
2. Update grammar parser to create GKeyword/GLit/GSyntax
3. Update `<ident>` to extract and reject `` `...` `` literals
4. Convert RedttParser.lego: `"let"` → `` `let` ``, `"in"` → `` `in` ``

---

## Phase 3: Explicit Grammar Refinement (FUTURE)

### Goal
Make token refinement **explicit in grammar**, not implicit in matching.

### Design

```haskell
-- Grammar declares refinements per piece
piece Term
  vocab:
    keywords: "let" "in" "where"
    symbols: "=" "→" ":"
```

### Why Phase 3 is Optional
- Phase 2 (keyword extraction + rejection) is **algebraically compositional**
- Vocabularies already compose via grammar pushouts
- Explicit vocab declarations add clarity but not functionality
- Wait until we have 5+ pieces that need vocabulary management

---

## Migration Complete

### Phase 1.5 → Phase 2 (DONE)
- Atoms tokenization working
- GKeyword foundation in place
- 725/725 parse rate (100%)

### What Was Fixed
1. `isIdentLikeSym` now excludes structural operators (`->`, `*`, etc.)
2. `collectLiterals` extracts vocabulary from grammar definitions
3. Keyword rejection prevents greedy `<ident>` matching
4. Nested let expressions parse correctly
