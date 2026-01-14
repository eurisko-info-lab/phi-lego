# Lego Test Coverage Report

> Generated: 2026-01-14
> Test Suite: `cabal run lego-test`

## Executive Summary

**Overall Statistics:**
- **Tests Passing**: 201/240 (83.8%)
- **Files Tested**: 70 total
- **Files with Passing Tests**: 21/70 (30.0%)
- **Files with 100% Pass Rate**: 6/70 (8.6%)
- **Rules Defined**: 233 across all test files
- **Grammar Productions**: 379 total productions

**Coverage by Category:**
| Category | Total Files | Files with Tests Passing | Coverage |
|----------|-------------|--------------------------|----------|
| basics/ | 12 | 3 | 25% |
| types/ | 18 | 0 | 0% |
| advanced/ | 5 | 1 | 20% |
| meta/ | 15 | 2 | 13% |
| languages/ | 13 | 0 | 0% |

## Fully Working Examples (100% pass, no errors)

These examples demonstrate complete, working language features:

1. **examples/basics/Arith.lego** (7/7 tests)
   - Basic arithmetic operations
   - Addition, subtraction, multiplication

2. **examples/basics/Nat.lego** (4/4 tests)
   - Natural numbers with Zero/Succ
   - Pattern matching

3. **examples/basics/Lists.lego** (16/16 tests)
   - List operations: append, reverse, map
   - Recursive functions

4. **examples/basics/SKI.lego** (28/28 tests)
   - SKI combinator calculus
   - Beta reduction rules

5. **examples/basics/Church.lego** (6/6 tests)
   - Church encodings
   - Boolean operations

6. **examples/meta/Reflection.lego** (45/45 tests)
   - Meta-programming features
   - AST manipulation

## Partially Working Examples

These files have some passing tests but encounter errors:

| File | Pass Rate | Issues |
|------|-----------|--------|
| examples/basics/Bool.lego | 14/16 (87.5%) | 2 FAIL: unit vs actual value |
| examples/basics/Either.lego | 8/10 (80.0%) | Undefined: 'name', 'num' |
| examples/basics/Lambda.lego | 11/15 (73.3%) | Undefined: 'name' production |
| examples/meta/Staging.lego | 7/10 (70.0%) | Parse errors |
| examples/meta/Quasiquote.lego | 6/9 (66.7%) | Missing productions |

## Major Error Categories

### 1. Parse Errors (27 occurrences)

**Most Common:**
- `unexpected 'test' "id_type"` (22 times) - Type theory examples
- `unexpected 'test' "subtype"` (3 times) - Subtyping examples

**Likely Cause:** Missing or incomplete grammar for dependent type syntax (Π types)

### 2. Undefined Productions (62 total instances)

**Top Missing Productions:**
| Production | References | Likely Needed For |
|------------|------------|-------------------|
| `name` | 62 | Variable/identifier references |
| `Instr.instr` | 14 | Machine instruction examples |
| `term` | 10 | Generic term references |
| `Dimension.dim` | 7 | Cubical type theory |
| `expr` | 6 | Expression syntax |
| `Env.env` | 4 | Environment/context |

**Root Cause:** Many examples reference base grammars (Atom.ident, Term.term, etc.) that may not be properly imported or defined.

### 3. Test Expectation Failures (39 tests)

**Pattern:** Tests expect `unit` but get actual parsed values

**Examples:**
```
FAIL: true_val
  Expected: unit
  Actual:   true

FAIL: read
  Expected: unit
  Actual:   (read_file "foo.txt")
```

**Issue:** Tests use `~~> unit` as a placeholder, but should either:
- Use `~~> _` for wildcard (any result acceptable)
- Specify actual expected output
- Remove normalization check (parse-only test)

## Grammar Optimization Opportunities

**265 productions** could benefit from GCut (grammar cut) for better error messages.

This represents a significant opportunity to improve parse error quality by adding explicit cut points after keywords.

## Untested Features

### Type System Examples (0% coverage)

All 18 files in `examples/types/` fail to parse:
- **CoC.lego** - Calculus of Constructions
- **Cubical.lego** - Cubical Type Theory
- **MLTT.lego** - Martin-Löf Type Theory
- **SystemF.lego** - System F polymorphism
- **HoTT.lego** - Homotopy Type Theory

**Issue:** Dependent type syntax (Π, Σ types) not fully supported in grammar

### Language Parsers (0% coverage)

None of the language parser examples work:
- **RedttParser.lego** - redtt proof assistant syntax
- **OCaml_Surface.lego** - OCaml syntax
- **Lisp.lego** - Lisp S-expressions

**Note:** The RedTT test suite (`cabal test redtt-test`) separately parses 725/725 declarations successfully, indicating the RedTT grammar itself works but the RedttParser.lego example has issues.

## Coverage Gaps

### Missing Base Grammars

Many examples assume standard productions that aren't defined:

**Need to provide:**
- `Atom.ident` - Identifier/variable names
- `Atom.number` - Numeric literals
- `Term.term` - Generic term references
- `Dimension.dim` - Dimension variables for cubical
- `Expr.expr` - Expression syntax

**Solution:** Either:
1. Create standard prelude with common productions
2. Update examples to define these locally
3. Fix import resolution to find these in Grammar.lego

### Test Quality Issues

Many tests use poor expectations:
- `~~> unit` used as placeholder (39 tests)
- Should use `~~> _` for "any output OK"
- Or specify actual expected normalized form

## Recommendations

### Priority 1: Fix Type System Support
- Debug Π type parsing (affects 22 parse errors)
- Add proper grammar for dependent types
- Target: Get at least 50% of types/ examples working

### Priority 2: Provide Standard Prelude
- Define common productions (name, term, expr, etc.)
- Auto-import into all examples
- Document standard vocabulary

### Priority 3: Improve Test Expectations
- Convert `~~> unit` to `~~> _` where appropriate
- Specify actual expected output for normalization tests
- Separate parse-only from normalize tests

### Priority 4: Grammar Cuts
- Add GCut annotations to 265 productions
- Prioritize high-traffic productions (lambda, app, etc.)
- Improves error messages significantly

### Priority 5: Fix Missing Productions
- Resolve 62 undefined production references
- Either define them or remove invalid references
- Focus on top 10 most-referenced

## Detailed Metrics

### Tests by Status
- ✅ **Passing**: 201 tests (83.8%)
- ❌ **Failing**: 39 tests (16.2%)
  - Parse errors: 27
  - Expectation mismatches: 39
  - Undefined productions: affects ~47 files

### File Status
- 🟢 **Perfect** (100% pass, 0 errors): 6 files (8.6%)
- 🟡 **Good** (>50% pass): 15 files (21.4%)
- 🟠 **Poor** (<50% pass): 6 files (8.6%)
- 🔴 **Broken** (0 pass or parse errors): 43 files (61.4%)

### Language Features Tested

**Working:**
- ✅ Arithmetic (Nat, Int, operations)
- ✅ Boolean logic
- ✅ Lists (cons, append, map, reverse)
- ✅ Lambda calculus (basic)
- ✅ Church encodings
- ✅ SKI combinator calculus
- ✅ Pattern matching
- ✅ Recursion
- ✅ Meta-programming (reflection)

**Partially Working:**
- ⚠️ Either/Maybe (missing base productions)
- ⚠️ Lambda calculus (missing 'name' production)
- ⚠️ Effect systems (IO, STM)

**Not Working:**
- ❌ Type theory (CoC, MLTT, Cubical, HoTT)
- ❌ System F / polymorphism
- ❌ Subtyping
- ❌ Language parsers (in examples/)

## Test Health Score

**Overall Score: 31/100**

Breakdown:
- Test pass rate: 84/100 (201/240 passing)
- File coverage: 30/100 (21/70 with passing tests)
- Perfect files: 9/100 (6/70 with 100%)
- Error-free files: 33/100 (23/70 without errors)

**Grade: D+**

The test suite covers core features well but has significant gaps in advanced topics (type theory, effects, language composition).

## Next Steps

1. **Immediate**: Fix the 39 `Expected: unit` test failures by using proper expectations
2. **Short-term**: Define missing base productions (name, term, expr) in prelude
3. **Medium-term**: Debug and fix Π type parsing to enable type theory examples
4. **Long-term**: Achieve 90%+ test pass rate and 60%+ file coverage
