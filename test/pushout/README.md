# Pushout Test Suite

This directory contains test files for the pushout composition system and 
grammar parametrization feature.

## Test Categories

### 1. Basic Pushout (`01_Basic*.lego`)
- Simple language composition via `import`
- Vocabulary merging
- Grammar extension

### 2. Grammar Parametrization (`02_Param*.lego`)
- `test[L]` syntax where L is the current language
- `rule[L]` syntax for patterns using language grammar
- References like `L.term`, `L.pattern`

### 3. Conflicts & Shadows (`03_Conflict*.lego`)
- Grammar productions that shadow imported ones
- Rule conflicts (same name, different behavior)
- Vocab conflicts (keyword vs identifier)

### 4. EOF Markers (`04_EOF*.lego`)
- Keywords as grammar section boundaries
- Context switching at `piece`, `rule`, `test`
- Incremental pushout building

### 5. Edge Cases (`05_Edge*.lego`)
- Empty pushouts
- Self-referential grammars
- Diamond inheritance

## Expected Behaviors

### Warnings (should emit but continue)
- `SHADOW: production 'X.y' shadows imported 'Z.y'`
- `CONFLICT: rule 'foo' has multiple definitions`

### Errors (should fail)
- `ERROR: cyclic import detected`
- `ERROR: undefined production reference 'X.y'`

## Running Tests

```bash
cabal run lego-test -- test/pushout/
```

## Grammar Parametrization Syntax

The key insight is that grammar keywords act as EOF markers:

```lego
-- When parser sees "test", it:
-- 1. Treats "test" as EOF for current grammar
-- 2. Switches to: test[L] ::= "test" <string> ":" L.term ("~~>" L.term)?
-- where L is the pushout of all pieces defined so far

lang MyLang :=
  piece Expr        -- L = Expr
    expr ::= ...
  
  piece More        -- L = Expr ⊔ More
    more ::= ...
  
  test "foo": ...   -- uses L.term = (Expr ⊔ More).term
```
