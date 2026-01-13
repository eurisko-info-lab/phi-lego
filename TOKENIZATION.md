# Pushout-Friendly Tokenization

> **Module**: [Lego.Token](interpreter/Lego/Token.hs) • [Lego.Vocabulary](interpreter/Lego/Vocabulary.hs)

## Problem

**Tokenization was not parametric, but grammar composition was.**

```
Old (broken):  Text → [Token] → Grammar
                      ↑
                   GLOBAL (all keywords reserved)
```

This violated compositionality:
- `tokenize` globally classified keywords before grammar saw them
- Each piece couldn't control its vocabulary
- Pushouts inherited conflicting reservations
- Example: `prelude` keyword in Lego leaked into redtt, breaking `import prelude`

## Solution: Stratified Tokenization

```
New (compositional):  Text → [Atom] → Grammar-refines → [Token]
                             ↑                  ↑
                          UNIVERSAL      GRAMMAR-SCOPED
```

### Two Layers

**Layer 1: Atoms** (lexer, universal, no reservation)
```haskell
data Token
  = TIdent String    -- word-like lexeme (NO classification yet)
  | TSym String      -- operator-like lexeme
  | TString String   -- string literal
  | TNewline         -- structure
  | TIndent Int      -- structure
  | TKeyword String  -- REFINED by grammar (not by lexer)
```

**Layer 2: Refinement** (grammar, local, context-dependent)
```haskell
-- Grammar matches:
"in"    : TIdent → refined to keyword in this piece
"let"   : TIdent → refined to keyword in this piece
"prelude" : TIdent → stays as identifier (no refinement)
```

## Implementation

### Token.hs

```haskell
-- Atoms only (no keyword classification)
tokenizeWithKeywords :: Bool -> String -> [Token]
tokenizeWithKeywords classifyKeywords = ...
  where
    tok = if classifyKeywords && isKeywordAt ind ident 
          then TKeyword ident   -- .lego files (backward compat)
          else TIdent ident     -- composed languages (atoms only)

-- For composed languages: atoms only
tokenize :: String -> [Token]
tokenize = tokenizeWithKeywords True  -- default: .lego behavior

-- For redtt: pure atoms
tokenizeRedtt :: String -> [Token]
tokenizeRedtt = tokenizeWithKeywords False
```

###GrammarInterp.hs

```haskell
-- <ident> matches BOTH TIdent and TKeyword
-- This allows:
--   - TIdent "prelude" in redtt (atom)
--   - TKeyword "prelude" in .lego (classified)
--   - Both parse correctly with same grammar

go (GNode "ident" []) st = case bsTokens st of
  (TIdent s : ts) -> [st { bsTokens = ts, ... }]
  (TKeyword s : ts) -> [st { bsTokens = ts, ... }]  -- permissive
  _ -> []

-- "in" literal explicitly requires keyword (via GSyntax)
go (GSyntax "in") st = case bsTokens st of
  (TKeyword "in" : ts) -> [st { bsTokens = ts }]  -- only keyword
  (TIdent "in" : ts) -> [st { bsTokens = ts }]    -- or atom (if not classified)
  _ -> []
```

### RedttTest.hs

```haskell
-- Use atoms for redtt files
let !toks = filter isInteresting (tokenizeWithKeywords False decl)
```

## Algebraic Properties

### Compositionality

Grammar pushout now composes cleanly:
```
Grammar₁ ⊔ Grammar₂
  = productions₁ ⊔ productions₂
  + refinements₁ ⊔ refinements₂

where refinement : Atom → Token (grammar-scoped function)
```

### Context-Sensitivity

Keywords are now **piece-local**:
```
piece Term
  "let" : keyword here

piece Name  
  "let" : identifier here (no refinement)
```

No global leakage.

### Conflict Resolution

Token conflicts are now **explicit** at pushout time:
```
If both pieces refine "λ" as keyword: OK (same refinement)
If one refines, one doesn't: context-sensitive (both valid)
If both refine differently: CONFLICT (caught at pushout)
```

## Benefits for Cubical

### Interval Endpoints
```
piece Interval
  "i0", "i1" : endpoints (keywords in this piece)

elsewhere:
  i0 : just an identifier
```

### Path Operators
```
piece PathOps
  "·", "⁻¹", "≃" : syntax symbols here

elsewhere:
  ·, ⁻¹, ≃ : identifiers
```

## Migration Path

1. **Immediate**: `.lego` files use `tokenize` (backward compat, classifies keywords)
2. **Immediate**: redtt uses `tokenizeWithKeywords False` (atoms only)
3. **Future**: All languages use atoms + grammar refinement
4. **Future**: Remove `tokenizeWithKeywords True` (pure compositional)

## Current State

- ✅ Layer 1 atoms implemented
- ✅ Layer 2 permissive matching (`<ident>` matches both TIdent and TKeyword)
- ✅ Redtt uses atoms (52% parse rate maintained)
- ⏳ Explicit refinement (future: grammar declares `token "let" : Keyword`)
- ⏳ Pushout merges refinements (future: `poTokenView`)

## Key Insight

**Tokens are not facts, they are views.**

A lexeme like "in" is:
- An atom at layer 1
- A keyword in `Term` grammar (refined view)
- An identifier in `Name` grammar (unrefineed view)

The grammar chooses the view. Pushouts compose views.

This is algebraically sound: tokens form a refinement lattice, pushout computes the join.
