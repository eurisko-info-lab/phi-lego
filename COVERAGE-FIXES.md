# Test Coverage Improvement Plan

Based on TEST-COVERAGE.md analysis, here's an actionable plan to fix the major gaps.

## Problem 1: 62 Undefined Production References (mostly 'name')

### Root Cause
Examples reference `name`, `nat`, `expr`, etc. but these aren't defined in Grammar.lego or imported.

### Solution: Create Standard Prelude

Create `prelude/lego/Atoms.lego` with common productions:

```lego
-- Atoms.lego: Standard atomic productions used by all examples
lang Atoms :=

piece Identifiers
  name ::= <ident>        -- Variable/function names
  ident ::= <ident>       -- Alias for consistency

piece Numbers
  nat ::= <digits>        -- Natural number literals
  num ::= <digits>        -- Generic number
  number ::= <digits>     -- Alias

piece Paths
  path ::= <string>       -- File paths (use string tokens)

piece Content
  content ::= <string>    -- File/message content

piece Vars
  var ::= <ident>         -- Variable reference (for some DSLs)
```

Then update examples to:
```lego
import Atoms  -- at top of every file that needs these
```

**Impact:** Fixes 62 undefined references immediately

**Effort:** 2 hours
- 30 min: Create Atoms.lego
- 30 min: Test it works
- 1 hour: Add `import Atoms` to affected files

## Problem 2: Type Theory Examples (0% coverage, 22 parse errors)

### Root Cause Analysis

The error `unexpected 'test' "id_type" ':' '(' 'Π'` occurs because:

1. The test line: `test "id_type": (Π (A : Type 0) . (Π (x : A) . A))`
2. Parser expects a term but gets `(Π ...)`
3. The `Π` syntax from Base.lego: `pi ::= "Π" "(" name ":" term ")" "." term`

**The Issue:** The grammar defines `pi` but uses it in production `term ::= ... | pi | ...`
However, when parsing the test, it's not finding the `pi` alternative.

### Debug Steps

1. Check if Base.lego actually parses:
```bash
cabal run lego-test -- examples/types/Base.lego --verbose
```

2. Check what tokens are produced from `(Π (A : Type 0) . (Π (x : A) . A))`:
   - Should be: `TSym "(", TIdent "Π", TSym "(", ...`
   - But Grammar.lego might not recognize `Π` as a symbol

3. **Hypothesis:** `Π` is a Unicode character that the tokenizer doesn't handle correctly

### Solution Options

**Option A: Fix Unicode Tokenization**
- Update Token.hs to recognize `Π`, `Σ`, `λ` as symbols
- Check if `isSymbol` function handles Unicode

**Option B: Use ASCII Syntax**
- Change examples to use ASCII: `Pi`, `Sigma`, `Lambda`
- Less elegant but guaranteed to work

**Option C: Make Π a keyword**
- Add to vocab: `vocab symbols := ["Π", "Σ", "λ", ...]`
- Register in Grammar.lego

### Quick Test
```bash
# Test if Π tokenizes correctly
echo '(Π x)' | cabal run lego-repl
```

**Impact:** Fixes 22 parse errors, enables 18 type theory files

**Effort:** 4-8 hours
- 2 hours: Debug tokenization
- 2 hours: Fix (either in Token.hs or examples)
- 2 hours: Verify all type examples parse
- 2 hours: Add missing productions (name, nat, etc.)

## Problem 3: 265 Productions Need GCut

### Root Cause
Productions lack explicit cut points, leading to poor error messages.

### Solution: Automated GCut Insertion

Create a tool to automatically add cuts after keywords:

```haskell
-- Example transformation:
-- Before: lam ::= "(" "λ" name "." term ")"
-- After:  lam ::= "(" "λ" @cut name "." term ")"
```

**Strategy:**
1. Identify keyword positions (first literal after production name)
2. Insert `@cut` after keyword
3. Test that error messages improve

**Script:** `scripts/add-gcuts.hs`

```haskell
-- Pseudocode
addGCut :: Production -> Production
addGCut prod@(name, GLit keyword : rest) =
  (name, GLit keyword : GCut : rest)
```

**Impact:** Improves error messages for 265 productions

**Effort:** 6 hours
- 3 hours: Write automation script
- 2 hours: Test on subset
- 1 hour: Apply to all examples

## Problem 4: Language Parser Examples (0% coverage)

### Root Cause
These are complex, self-referential grammars that define parsers for other languages.

### Files Affected
- RedttParser.lego
- OCaml_Surface.lego
- Lisp.lego

### Analysis

**Note:** RedTT parsing works (725/725) via the dedicated redtt-test suite, but RedttParser.lego (the example showing how to write a redtt parser in Lego) fails.

**Likely Issues:**
1. Missing Atoms imports
2. Self-referential grammar issues
3. Complex composition not working

### Solution
1. Start with simplest: Lisp.lego
2. Add Atoms import
3. Test incrementally
4. Document patterns for language parser examples

**Impact:** 3 complex examples working

**Effort:** 8 hours (exploratory)
- Need to debug each individually
- May uncover grammar composition bugs

## Problem 5: Poor Test Expectations (39 tests expect 'unit')

### Root Cause
Tests use `~~> unit` as placeholder instead of proper expectations.

### Solution: Batch Fix

```bash
# Find all instances
grep -r "~~> unit" examples/

# Replace with wildcard
sed -i 's/~~> unit$/~~> _/g' examples/**/*.lego
```

**But:** Should verify these are actually meant to be wildcards, not real unit expectations.

### Manual Review Needed
Some might genuinely expect `unit`, others should specify actual output.

**Impact:** 39 tests properly specified

**Effort:** 2 hours
- 1 hour: Review each case
- 1 hour: Apply fixes

## Implementation Priority

### Phase 1: Quick Wins (1 day)
1. ✅ Create Atoms.lego prelude
2. ✅ Add imports to affected files
3. ✅ Fix test expectations (unit → _)
4. ✅ Test: Should get 230+/240 passing

### Phase 2: Unicode/Tokenization (1 day)
1. Debug Π tokenization
2. Fix in Token.hs or add to vocab
3. Test: Should get type theory examples parsing

### Phase 3: Error Messages (2 days)
1. Write GCut automation
2. Apply to examples
3. Test error message quality

### Phase 4: Language Parsers (2 days)
1. Debug Lisp.lego
2. Debug OCaml_Surface.lego
3. Debug RedttParser.lego
4. Document patterns

## Expected Outcomes

### After Phase 1 (1 day)
- Tests: 230+/240 (95%+)
- Coverage: 50%+ of files working
- Health: C+ grade

### After Phase 2 (2 days)
- Tests: 235+/240 (98%+)
- Coverage: 70%+ of files working
- Type theory: 50%+ coverage
- Health: B grade

### After Phase 3 (4 days)
- Better error messages
- Developer experience improved
- Health: B+ grade

### After Phase 4 (6 days)
- Tests: 238+/240 (99%+)
- Coverage: 90%+ of files working
- Language parsers: working examples
- Health: A- grade

## Detailed Action Items

### Immediate (Today)
- [ ] Create `prelude/lego/Atoms.lego`
- [ ] Test Atoms.lego loads correctly
- [ ] Add `import Atoms` to 5 affected examples
- [ ] Run tests, confirm improvement

### Short-term (This Week)
- [ ] Debug Π tokenization issue
- [ ] Fix all type theory examples
- [ ] Review and fix test expectations
- [ ] Get to 95%+ test pass rate

### Medium-term (This Month)
- [ ] Implement GCut automation
- [ ] Apply to all examples
- [ ] Fix language parser examples
- [ ] Achieve A- health score

## Success Metrics

| Metric | Current | Phase 1 | Phase 2 | Phase 4 |
|--------|---------|---------|---------|---------|
| Test Pass Rate | 83.8% | 95%+ | 98%+ | 99%+ |
| File Coverage | 30% | 50%+ | 70%+ | 90%+ |
| Health Score | 31/100 | 60/100 | 80/100 | 90/100 |
| Grade | D+ | C+ | B | A- |

## Notes

- Focus on Atoms.lego first - highest impact/effort ratio
- Unicode tokenization is critical for type theory
- GCut automation pays dividends long-term
- Language parsers are valuable but lower priority
