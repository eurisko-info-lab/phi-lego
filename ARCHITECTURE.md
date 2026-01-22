# Simplified Architecture: Grammar vs Schema

## Current Problem

Grammar and Schema are conflated. The grammar tries to do both:
1. Parse surface syntax → tokens
2. Build Terms with correct structure

This creates complexity: `(node lam (seq (lit "(") (lit λ) (ref ident) ...))` 
mixes syntax (`(`, `λ`, `.`) with structure (lam has 2 children).

## Proposed Separation

### Layer 1: Grammar (Surface ↔ S-expr)

Grammar is **purely syntactic** - shuffles tokens to/from s-expr list structure.

```
-- Grammar.lego (simplified)
grammar:
  term ::= "(" "λ" ident "." term ")"   ~> (lam $1 $2)
         | "(" "Π" binder "." term ")"  ~> (Π $1 $2)
         | "(" term term ")"            ~> (app $1 $2)
         | ident                        ~> (var $1)
         | ...
```

The `~>` shows the s-expr shape produced. No `node` markers needed - 
the grammar just arranges tokens into lists.

**Parse**: `(λ x . x)` → tokenize → grammar → `(lam x x)`
**Print**: `(lam x x)` → grammar inverse → `(λ x . x)`

### Layer 2: Schema (S-expr ↔ Term)

Schema defines **valid s-expr shapes** with arities, like Prolog functors.

```haskell
-- Schema.hs
data Schema = Schema
  { constructors :: Map String Arity
  , sorts        :: Map String [String]  -- sort -> valid constructors
  }

data Arity 
  = Arity Int                    -- fixed: lam/2
  | ArityAtLeast Int             -- variadic: app/1+
  | ArityRange Int Int           -- range: case/2-∞

-- Built-in schema for Term
termSchema :: Schema
termSchema = Schema
  { constructors = M.fromList
      [ ("lam", Arity 2)         -- (lam x body)
      , ("var", Arity 1)         -- (var x)
      , ("app", Arity 2)         -- (app f arg)
      , ("Π",   Arity 3)         -- (Π x A B) 
      , ("Σ",   Arity 3)         -- (Σ x A B)
      , ("str", Arity 1)         -- (str "hello")
      , ("num", Arity 1)         -- (num 42)
      ]
  , sorts = M.fromList
      [ ("term", ["lam", "var", "app", "Π", "Σ", "str", "num"])
      ]
  }
```

**Validate**: Check s-expr matches schema
**ToTerm**: `(lam x (var x))` → `TmCon "lam" [TmVar "x", TmCon "var" [TmVar "x"]]`
**FromTerm**: Inverse

### Layer 3: Term (Mathematical Structure)

```haskell
-- Term is the algebra we reason about
data Term
  = TmVar String           -- variable
  | TmCon String [Term]    -- constructor with children
  | TmLit String           -- literal (string/number)
  deriving (Eq, Show)

-- Rules operate on Terms
type Rule = (Term, Term)   -- pattern ~> template
```

## Data Flow

```
Surface String
    │
    ▼ tokenize
[Token]
    │
    ▼ grammar.parse
SExpr                 ←── pure syntax, no semantics
    │
    ▼ schema.validate + toTerm
Term                  ←── mathematical structure
    │
    ▼ rules.normalize
Term
    │
    ▼ schema.fromTerm
SExpr
    │
    ▼ grammar.print
[Token]
    │
    ▼ detokenize
Surface String
```

## Implementation Sketch

### 1. Simplified Grammar

```haskell
-- Grammar is just pattern matching on token lists
data GrammarRule = GrammarRule
  { grName    :: String
  , grPattern :: [GrammarPart]    -- surface pattern
  , grSExpr   :: SExprTemplate    -- s-expr template with holes
  }

data GrammarPart
  = Lit String          -- literal token
  | Ref String          -- reference to another production  
  | Capture Int         -- capture group $1, $2, ...

data SExprTemplate
  = SAtom String
  | SList [SExprTemplate]
  | SHole Int           -- $1, $2, ...

-- Parse: match pattern, fill template
-- Print: match template, fill pattern (inverse)
```

### 2. Schema Validation

```haskell
validateSExpr :: Schema -> String -> SExpr -> Either String ()
validateSExpr schema sort sexpr = case sexpr of
  Atom s -> 
    -- atoms are always valid (variables, literals)
    Right ()
  List (Atom con : args) ->
    case M.lookup con (constructors schema) of
      Nothing -> Left $ "Unknown constructor: " ++ con
      Just (Arity n) 
        | length args /= n -> Left $ con ++ "/" ++ show n ++ " got " ++ show (length args)
        | otherwise -> mapM_ (validateSExpr schema "term") args
  List [] -> Left "Empty list not allowed"
  List (x:_) -> Left $ "Constructor must be atom, got: " ++ show x
```

### 3. SExpr ↔ Term Conversion

```haskell
sexprToTerm :: SExpr -> Term
sexprToTerm (Atom s) = TmVar s
sexprToTerm (List [Atom "str", Atom s]) = TmLit s
sexprToTerm (List [Atom "num", Atom n]) = TmLit n
sexprToTerm (List (Atom con : args)) = TmCon con (map sexprToTerm args)

termToSExpr :: Term -> SExpr
termToSExpr (TmVar s) = Atom s
termToSExpr (TmLit s) = List [Atom "str", Atom s]  -- or detect number
termToSExpr (TmCon con args) = List (Atom con : map termToSExpr args)
```

## Benefits

1. **Grammar is trivial**: Just token shuffling, ~100 lines
2. **Schema is declarative**: Arity checking, sort membership
3. **Term is clean**: Pure algebra, rules just work
4. **Bidirectional for free**: Grammar templates are invertible
5. **Error messages are clear**: Schema says "lam/2 got 3 args"

## Migration Path

1. Keep current system working
2. Add Schema module alongside
3. Gradually move arity checks from Grammar to Schema
4. Simplify Grammar to pure syntax
5. Remove `node` markers from Grammar.sexpr

## Example: Lambda

**Current** (conflated):
```
(prod "Term.term" 
  (alt 
    (node lam (seq (lit "(") (lit λ) (ref Atom.ident) (lit .) (ref Term.term) (lit ")")))
    ...))
```

**Proposed** (separated):

Grammar.lego:
```
term ::= "(" "λ" ident "." term ")"  ~> (lam $1 $2)
```

Schema:
```
lam/2 : term
```

The grammar just produces `(lam x body)`, schema validates arity.
