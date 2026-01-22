# Triple Quote Convention: Semantic Token Types

> **Status**: Design spec • Current implementation uses `collectLiterals` instead

## Problem (SOLVED)

With atom-based tokenization, `<ident>` matches any `TIdent`, including reserved keywords like `in`. This causes greedy application (`appexpr ::= projexpr+`) to consume `in` as an identifier, breaking `let x = a in b`.

**Current Solution**: `isIdentLikeSym` in GrammarInterp.hs excludes structural operators.
This spec describes an alternative explicit syntax for the future.

## Solution: Semantic Quote Types (FUTURE)

Use different quote marks to declare semantic roles:

| Quote | Type | Meaning | Example | `<ident>` match? |
|-------|------|---------|---------|------------------|
| `` `...` `` | Reserved keyword | Global, rejected by `<ident>` | `` `let`, `in` `` | ❌ NO |
| `'...'` | Soft keyword | Context-dependent | `'trans'`, `'symm'` | ✅ YES |
| `"..."` | Syntax literal | Operators, structure | `"→"`, `"("`, `"="` | ✅ YES |

## Example

**Before** (ambiguous):
```lego
letexpr ::= "let" letpat ... "=" term "in" term
```
- Problem: `<ident>` in `qualident` matches `"in"` because both are `TIdent`

**After** (explicit):
```lego
letexpr ::= `let` letpat ... "=" term `in` term
```
- `<ident>` automatically rejects `TIdent "in"` because `` `in` `` is reserved
- Application stops at `in`, nested let works!

## Implementation

### Token Types
```haskell
data Token
  = TIdent String      -- atoms (no classification)
  | TReserved String   -- backtick literals: `let`, `in`
  | TSoft String       -- single quotes: 'trans'
  | TSym String        -- double quotes: "→", "="
```

### Grammar Constructors
```haskell
GKeyword :: String -> GrammarExpr   -- `...` → rejected by <ident>
GLit :: String -> GrammarExpr       -- '...' → soft keyword
GSyntax :: String -> GrammarExpr    -- "..." → syntax
```

### Tokenizer Change
```haskell
go col ind ('`':cs) = 
  let (s, rest) = span (/= '`') cs
  in TReserved s : go ... (drop 1 rest)

go col ind ('\'':cs) = 
  let (s, rest) = span (/= '\'') cs
  in TSoft s : go ... (drop 1 rest)

go col ind ('"':cs) = 
  let (s, rest) = span (/= '"') cs
  in TSym s : go ... (drop 1 rest)
```

### <ident> Matching with Rejection
```haskell
go (GNode "identifier" []) st = case bsMode st of
  Parse -> case bsTokens st of
    (TIdent s : ts) | not (isReserved s reservedSet) -> 
      [st { bsTokens = ts, bsTerm = Just (TmVar s) }]
    _ -> []
  where
    reservedSet = extractReservedKeywords (getAllGrammars st)
```

## Benefits

1. **Self-documenting**: Grammar declares reserved words via `` `...` ``
2. **Compositional**: Reserved word sets compose with grammar pushouts
3. **Type-safe**: Compiler catches when `<ident>` would match reserved word
4. **Algebraic**: Quote types form a hierarchy (reserved ⊂ keywords ⊂ identifiers)

## Migration Path

1. ✅ Add `GKeyword` constructor and `TReserved` token
2. ✅ Update tokenizer to recognize `` `...` ``
3. Update `<ident>` to extract and reject reserved keywords
4. Convert redtt grammar: `"let"` → `` `let` ``, `"in"` → `` `in` ``
5. Test nested let expressions

## Current Status

### Completed (Phase 1)
- ✅ Added `GKeyword` constructor to GrammarExpr (Lego/Internal.hs)
- ✅ Added `extractKeywords` and `extractReservedKeywords` functions
- ✅ Updated Show instance to display `` `...` `` for GKeyword
- ✅ GrammarInterp handles GKeyword matching  
- ✅ Code compiles with new constructor

### Remaining Work (Phase 2)
- ⏳ Tokenizer: Recognize `` `...` `` quotes → new token type
- ⏳ GrammarParser: Handle `` `...` `` in .lego files → GKeyword
- ⏳ GrammarInterp: Make `<ident>` reject reserved keywords
- ⏳ Convert RedttParser.lego to use `` `let` ``, `` `in` ``, etc.

### Alternative: Token Classification (Pragmatic) ✅ DONE

Instead of waiting for full tokenizer changes, use existing infrastructure:
1. Extract keywords from grammar with `GrammarAnalysis.collectLiterals`
2. Classify tokens with `classifyKeywords :: S.Set String -> [Token] -> [Token]`
3. Make `<ident>` check `not (TKeyword ...)` 

**Status**: Implemented in Eval.hs - vocabulary auto-extracted from grammar.

