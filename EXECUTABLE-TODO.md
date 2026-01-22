# Making Lego Languages Executable

> **Package**: [lego.cabal](lego.cabal) • See also: [EXECUTABLE-STATUS.md](EXECUTABLE-STATUS.md)

## Status: 65 files, 550 rules, 195/234 tests passing

## Parser Improvements: Keyword Cuts for Error Recovery

### Problem
When parsing fails mid-file, the entire file fails. Better error recovery needed.

### Solution: Cut Keywords
Languages should declare keywords as "cut points" - parsing cannot backtrack past them.

```
-- Proposed syntax in .lego files:
piece cuts
  cuts := ["piece", "rule", "test", "def", "data", "import"]
  -- Position-aware cuts:
  -- ^piece = cut only at line start
  -- ^rule  = cut only at line start
end
```

### Implementation in LegoInterpreter.hs
```haskell
-- Add to parseTopLevel:
parseCut :: Parser ()
parseCut = do
  pos <- getPosition
  when (sourceColumn pos == 1) $ do
    keyword <- choice [string "piece", string "rule", string "test"]
    commitTo  -- no backtracking past this point
```

### Benefits
1. **Error localization**: "Error in piece X after keyword 'rule'"
2. **Partial parsing**: Return valid pieces even if one fails
3. **Performance**: Less backtracking

---

## Language Categories

### 1. BASIC (need normalization rules)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| Nat.lego | 4 | ⚠️ | Full Peano arithmetic |
| Bool.lego | 6 | ⚠️ | Full boolean ops |
| Arith.lego | 8 | ⚠️ | Needs normalization |
| Lambda.lego | 3 | ⚠️ | β-reduction |
| SKI.lego | 3 | ⚠️ | SKI reduction rules |
| Church.lego | 4 | ⚠️ | Church numeral ops |
| Lists.lego | 5 | ⚠️ | List operations |
| Pairs.lego | 4 | ⚠️ | Pair projection |
| Maybe.lego | 3 | ⚠️ | Maybe elimination |
| Either.lego | 3 | ⚠️ | Either elimination |

### 2. ADVANCED (need IO/effect semantics)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| IO.lego | 5 | ❌ | Monad laws, bind |
| Async.lego | 6 | ❌ | Promise semantics |
| Actors.lego | 8 | ❌ | Message passing |
| Concurrent.lego | 7 | ❌ | Fork/join |
| STM.lego | 9 | ❌ | Transaction semantics |

### 3. META (need reflection/staging)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| Meta.lego | 12 | ⚠️ | Quote/splice |
| Staging.lego | 8 | ⚠️ | Multi-stage |
| Reflection.lego | 10 | ⚠️ | Introspection |
| Tactics.lego | 15 | ⚠️ | Tactic monad |

### 4. TYPE THEORY (need type checking)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| CoC.lego | 8 | ⚠️ | Full CoC checking |
| SystemF.lego | 6 | ⚠️ | Type abstraction |
| MLTT.lego | 10 | ⚠️ | Dependent types |
| HoTT.lego | 12 | ⚠️ | Path types |

### 5. CUBICAL (need path/hcom)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| Redtt.lego | 16 | ⚠️ | Full coe/hcom |
| Cooltt.lego | 18 | ⚠️ | Pattern lambdas |
| Cubical.lego | 14 | ⚠️ | Interval ops |

### 6. LANGUAGES (need semantics)
| File | Rules | Status | Missing |
|------|-------|--------|---------|
| OCaml*.lego | 14-18 | ⚠️ | Full ML semantics |
| Haskell.lego | 12 | ⚠️ | Lazy evaluation |
| Lisp.lego | 8 | ⚠️ | S-expr eval |
| Prolog.lego | 10 | ⚠️ | Unification |

---

## Template Syntax Limitations

**DISCOVERED ISSUES** (cause parse failures):

1. **Bracket substitution NOT supported**:
   ```
   -- FAILS: [($x := $arg)] $body
   -- USE:   (subst $x $arg $body)
   ```

2. **Star identifiers NOT supported**:
   ```
   -- FAILS: *1, *2
   -- USE:   fstvar, sndvar (or any valid identifier)
   ```

3. **Reserved keywords cannot be used as identifiers**:
   - piece, lang, test, rule, def, prelude, code, import

---

## Implementation Phases

### Phase 1: Basic Computability (Priority: HIGH)
- [ ] Add β-reduction rule to Lambda.lego
- [ ] Add Peano rules to Nat.lego  
- [ ] Add SKI combinators to SKI.lego
- [ ] Add Church encodings to Church.lego
- [ ] Verify all basics compute to normal forms

### Phase 2: Type Checking (Priority: MEDIUM)
- [ ] Implement bidirectional type checking rules
- [ ] Add universe hierarchy rules
- [ ] Implement dependent function rules
- [ ] Add sigma type rules

### Phase 3: Cubical (Priority: HIGH for HoTT)
- [ ] Implement path type computation
- [ ] Add coe through type formers
- [ ] Implement hcom boundaries
- [ ] Add higher inductive type rules
- [ ] Recover lost redtt examples (hopf, torus map)

### Phase 4: Effects (Priority: LOW)
- [ ] IO monad semantics
- [ ] Async/await
- [ ] Actor model

---

## Files With Lost Content (From Truncation)

### Redtt.lego
Tests simplified or removed during normalization:
- `lamelim_s1`: λ elimination on circle
- `t2c_pt`: torus to circle×circle at point
- `c2t_structure`: inverse map structure
- `hopf_base`: Hopf fibration base
- `hopf_structure`: Full Hopf fibration

### Recovery Strategy
1. Study RedPRL/redtt `test/*.red` for examples
2. Study RedPRL/cooltt `test/*.cooltt` for newer syntax
3. Translate to .lego format with valid template syntax

---

## Per-File TODO Template

Each .lego file should have at end:
```
-- =============================================================================
-- TODO: Executable Language Checklist
-- Category: [BASIC|ADVANCED|META|TYPE|CUBICAL|LANGUAGE]
-- Current: N rules, M tests, K grammars
-- =============================================================================
-- [x] Grammar: parsing works
-- [ ] Rules: computational rules defined
-- [ ] Tests: reduction tests pass
-- [ ] Normalization: terms reduce to normal form
-- Keywords: cuts := [list of cut keywords]
-- =============================================================================
```
