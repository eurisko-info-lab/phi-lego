# CoolTT Lego Module

A complete Lego specification for parsing and representing [cooltt](https://github.com/RedPRL/cooltt) programs.

## Overview

CoolTT is a proof assistant implementing **Cartesian Cubical Type Theory** with:
- Higher inductive types (Circle, Nat)
- Extension types with cofibration constraints
- V types for univalence
- First-class records (sig/struct)
- Sophisticated module system (sections, views, exports)
- Equational reasoning proofs

## Module Structure (3,064 lines total)

| File | Lines | Description |
|------|-------|-------------|
| [Cooltt.lego](Cooltt.lego) | 728 | Main grammar specification |
| [CoolttTokens.lego](CoolttTokens.lego) | 338 | Tokenizer (from Lex.mll) |
| [CoolttAST.lego](CoolttAST.lego) | 362 | Abstract Syntax Tree |
| [CoolttCubical.lego](CoolttCubical.lego) | 271 | Cubical TT foundations |
| [CoolttExamples.lego](CoolttExamples.lego) | 530 | Parsed examples |
| [CoolttParser.lego](CoolttParser.lego) | 206 | Parser module |
| [CoolttTests.lego](CoolttTests.lego) | 447 | Comprehensive tests |
| README.md | 182 | Documentation |

## Grammar Coverage

The grammar covers all constructs from `vendor/cooltt/src/frontend/Grammar.mly`:

### Terms
- **Variables**: `x`, `foo::bar::baz`
- **Literals**: `0`, `42`, `_`
- **Types**: `type`, `nat`, `circle`, `dim`, `cof`
- **Functions**: `(x : A) → B`, `x ⇒ body`
- **Pairs**: `[a, b]`, `(x : A) × B`
- **Projections**: `fst`, `snd`, `t.field`

### Records
- **Signatures**: `sig def x : A def y : B end` or `sig [x : A, y : B]`
- **Structures**: `struct def x := a def y := b end` or `struct [x := a, y := b]`
- **Include**: `include r renaming [x -> y]`
- **Patches**: `tp # [field := value]`

### Cofibrations
- **Equality**: `i = 0`, `i = 1`
- **Boundary**: `∂ i`
- **Lattice**: `φ ∨ ψ`, `φ ∧ ψ`
- **Constants**: `⊤`, `⊥`

### Extension Types
```
ext i => A with [i=0 => a | i=1 => b]
```

### Sub Types
```
sub A φ a   -- elements of A equal to a when φ holds
```

### Cubical Operations
- **Coercion**: `coe (i => A) r r' a`
- **Homogeneous composition**: `hcom A r r' φ u`
- **Fill**: `hfill A r φ u`
- **Heterogeneous composition**: `com (i => A) r r' φ u`

### V Types (Univalence)
```
V r A B e        -- Glue type
vproj t          -- V projection
cap t            -- Cap/boundary
```

### Eliminators
```
elim [
| zero => z
| suc {n => ih} => s
]
```

### Equations
```
equation nat begin
  t0 =[ p ] t1 =[ q ] t2
end
```

### Declarations
- `def f (x : A) : B := body`
- `abstract def f : A := body`
- `axiom f : A`
- `import path [modifier]`
- `section prefix begin ... end [modifier]`
- `view [?]`, `export [...]`, `repack [...]`

## Unicode Support

CoolTT supports emoji alternatives for many constructs:

| Keyword | Unicode | Emoji |
|---------|---------|-------|
| `nat` | | 🔢 |
| `circle` | | 🍪 |
| `loop` | | ➰ |
| `sig` | | ✏ |
| `struct` | | 🍱 |
| `def` | | 📌 |
| `axiom` | | 🛐 |
| `import` | | 📥 |
| `begin` | | ▶️ |
| `end` | | ⏹️ |
| `section` | | 📦 |
| `view` | | 👁️ |
| `export` | | 📤 |
| `repack` | | 🎁 |
| `V` | | 🥦 |

## Comparison with RedTT

| Feature | RedTT | CoolTT |
|---------|-------|--------|
| Path types | `[i] A [...]` | `ext i => A with [...]` |
| Sub types | ❌ | `sub A φ a` |
| Records | ❌ | `sig`/`struct` |
| Equations | ❌ | `equation ... begin ... end` |
| Sections | ❌ | `section ... begin ... end` |
| Module exports | Limited | Full `view`/`export`/`repack` |

## Examples

### Path Type (Sugar)
```cooltt
def path (A : type) (x y : A) : type :=
  ext i => A with [i=0 => x | i=1 => y]
```

### Reflexivity
```cooltt
def refl (A : type) (x : A) : path A x x :=
  i => x
```

### Addition on Naturals
```cooltt
abstract
def + : nat → nat → nat :=
  elim [
  | zero => n => n
  | suc {_ => ih} => n => suc {ih n}
  ]
```

### Records
```cooltt
def point : type :=
  sig [x : nat, y : nat]

def origin : point := 
  struct [x := 0, y := 0]
```

### Equational Proof
```cooltt
def +-right-unit : (x : nat) → path nat {+ x 0} x :=
  elim [
  | zero => +-left-unit 0
  | suc {y => ih} =>
    equation nat begin
      + {suc y} 0 =[ +-suc-l y 0 ]
      suc {+ y 0} =[ i => suc {ih i} ]
      suc y
    end
  ]
```

## References

- [CoolTT Repository](https://github.com/RedPRL/cooltt)
- [Grammar.mly](../../vendor/cooltt/src/frontend/Grammar.mly)
- [Lex.mll](../../vendor/cooltt/src/frontend/Lex.mll)
- [ConcreteSyntaxData.ml](../../vendor/cooltt/src/frontend/ConcreteSyntaxData.ml)
- [Test Suite](../../vendor/cooltt/test/)
