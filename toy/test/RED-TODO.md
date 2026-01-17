# Redtt: Roadmap to Computational Executability

## Current Status

| Component | Status | Notes |
|-----------|--------|-------|
| **Parsing** | ✅ 100% | 733/733 declarations, 111 productions |
| **Grammar** | ✅ Done | 23 logical pieces with cross-references |
| **Tokenizer** | ✅ Done | Grammar-driven with FIRST/FOLLOW keywords |
| **Core IR** | 🔲 Skeleton | Rules defined, not yet executable |
| **Elaboration** | 🔲 TODO | Surface → Core transformation |
| **Reduction** | 🔲 TODO | β-reduction, Kan operations |
| **Validation** | 🔲 TODO | Scope/type checking |

## Architecture

```
.red file
    │
    ▼ (Redtt.lego grammar)
Surface AST (parsed Term)
    │
    ▼ (Elaboration rules)
Core IR (de Bruijn indexed)
    │
    ▼ (Reduction rules)
Normal Form
    │
    ▼ (Quote/Print rules)
Output
```

## Phase 1: Core IR Representation

### 1.1 Term Constructors

Define the Core IR as Term constructors that our rules can manipulate:

```
-- Type formers
(Univ kind lvl)           -- type pre/kan ^n
(Pi $dom $cod)            -- (x : A) → B
(Sg $dom $cod)            -- (x : A) × B  
(Ext $dims $ty $sys)      -- [i j] A [sys]
(Path $A $a $b)           -- path A a b (sugar for Ext)
(V $r $ty0 $ty1 $equiv)   -- V-types
(Data $lbl $params)       -- inductive types

-- Introductions
(Lam $x $body)            -- λ x. e
(ExtLam $xs $body)        -- λ [i]. e
(Cons $a $b)              -- (a, b)
(Refl $a)                 -- reflexivity
(VIn $r $tm0 $tm1)        -- V intro
(Intro $dlbl $clbl $args) -- data constructor

-- Eliminations
(App $f $x)               -- application
(ExtApp $f $dims)         -- dimension application
(Fst $p) (Snd $p)         -- projections
(Elim $scrut $mot $cls)   -- elimination
(VProj $v) (Cap $v)       -- V projections

-- Kan operations
(Coe $r $r' $ty $tm)      -- coercion
(HCom $r $r' $ty $cap $sys)  -- homogeneous composition
(Com $r $r' $ty $cap $sys)   -- heterogeneous composition

-- Variables
(Var $name)               -- named (surface)
(Ix $n)                   -- de Bruijn index (core)
(Meta $name)              -- metavariable/hole
```

### 1.2 Binding Representation

```
-- Named binding (surface)
(Bnd $name $body)

-- De Bruijn binding (core)  
(Abs $body)               -- binds index 0

-- N-ary binding for extension types
(NAbs $n $body)           -- binds indices 0..n-1
```

## Phase 2: Elaboration (Surface → Core)

### 2.1 Name Resolution

```lego
-- Resolve named variable to de Bruijn index
rule resolve-var: (elaborate (Var $x) $env) ~>
  (Ix (lookup $x $env)) ;

-- Extend environment under binder
rule elab-lam: (elaborate (lam $x $body) $env) ~>
  (Lam (elaborate $body (extend $x $env))) ;
```

### 2.2 Bidirectional Type Checking

```lego
-- Checking mode: term ⇐ type
rule check-lam: (check (lam $x $body) (Pi $dom $cod)) ~>
  (Lam (check $body (subst $cod $x (Ix 0)))) ;

-- Inference mode: term ⇒ type
rule infer-app: (infer (App $f $x)) ~>
  (let (Pi $dom $cod) (infer $f)
   (let _ (check $x $dom)
    (subst $cod (Ix 0) $x))) ;
```

### 2.3 Pattern Compilation

```lego
-- Tuple pattern
rule elab-tup-pat: (elaborate (λ (,$x $y) $body) $env) ~>
  (Lam (Let (Fst (Ix 0)) 
        (Let (Snd (Ix 1))
         (elaborate $body (extend $y (extend $x $env)))))) ;

-- Inline elim pattern
rule elab-elim-pat: (elaborate (λ [| $clauses] $body) $env) ~>
  (Lam (Elim (Ix 0) (elaborate $body $env) (elab-clauses $clauses $env))) ;
```

## Phase 3: Reduction Rules

### 3.1 β-Reduction

```lego
rule beta-lam: (App (Lam $body) $arg) ~> (subst $body (Ix 0) $arg) ;
rule beta-fst: (Fst (Cons $a $b)) ~> $a ;
rule beta-snd: (Snd (Cons $a $b)) ~> $b ;
rule beta-let: (Let $val $body) ~> (subst $body (Ix 0) $val) ;
```

### 3.2 Dimension Operations

```lego
rule dim-app-0: (ExtApp (ExtLam $body) Dim0) ~> (subst $body (Ix 0) Dim0) ;
rule dim-app-1: (ExtApp (ExtLam $body) Dim1) ~> (subst $body (Ix 0) Dim1) ;

-- Path application to refl
rule path-refl: (ExtApp (Refl $a) $r) ~> $a ;
```

### 3.3 Kan Operations

```lego
-- Coercion at same point
rule coe-refl: (Coe $r $r $ty $tm) ~> $tm ;

-- HCom at same point
rule hcom-refl: (HCom $r $r $ty $cap $sys) ~> $cap ;

-- Coe through constant type
rule coe-const: (Coe $r $r' (Abs $A) $tm) ~> $tm 
  when (not-free 0 $A) ;

-- Coe through Pi
rule coe-pi: (Coe $r $r' (Abs (Pi $dom $cod)) $f) ~>
  (Lam (let $x' (Coe $r' $r (Abs $dom) (Ix 0))
        (Coe $r $r' (Abs (subst $cod (Ix 0) $x')) (App $f $x')))) ;

-- Coe through Sg
rule coe-sg: (Coe $r $r' (Abs (Sg $dom $cod)) $p) ~>
  (let $a  (Fst $p)
   (let $a' (Coe $r $r' (Abs $dom) $a)
    (let $b  (Snd $p)
     (let $b' (Coe $r $r' (Abs (subst $cod (Ix 0) (Coe $r $i (Abs $dom) $a))) $b)
      (Cons $a' $b'))))) ;
```

### 3.4 V-Type Computation (Univalence)

```lego
rule v-0: (V Dim0 $ty0 $ty1 $equiv) ~> $ty0 ;
rule v-1: (V Dim1 $ty0 $ty1 $equiv) ~> $ty1 ;
rule vin-0: (VIn Dim0 $tm0 $tm1) ~> $tm0 ;
rule vin-1: (VIn Dim1 $tm0 $tm1) ~> $tm1 ;

-- VProj computes via the equivalence
rule vproj: (VProj (VIn $r $tm0 $tm1)) ~>
  (hcom 0 1 $ty1 $tm1 [(r=0) → (equiv-fun $equiv $tm0)]) ;
```

### 3.5 Data Elimination

```lego
rule elim-intro: (Elim (Intro $dlbl $clbl $args) $mot $clauses) ~>
  (apply-clause (lookup $clbl $clauses) $args) ;

-- With induction hypothesis
rule elim-intro-ih: (Elim (Intro $dlbl $clbl $args $rec) $mot $clauses) ~>
  (apply-clause-ih (lookup $clbl $clauses) $args 
    (map (λ $r (Elim $r $mot $clauses)) $rec)) ;
```

## Phase 4: Substitution Engine

### 4.1 Core Substitution

```lego
-- Variable hit
rule subst-hit: (subst (Ix 0) (Ix 0) $v) ~> $v ;

-- Variable miss (shift)
rule subst-miss: (subst (Ix $n) (Ix 0) $v) ~> (Ix (pred $n)) 
  when (> $n 0) ;

-- Under binder
rule subst-lam: (subst (Lam $body) (Ix 0) $v) ~>
  (Lam (subst $body (Ix 1) (shift $v))) ;

-- Structural
rule subst-app: (subst (App $f $x) $i $v) ~>
  (App (subst $f $i $v) (subst $x $i $v)) ;
```

### 4.2 Shifting

```lego
rule shift-ix: (shift (Ix $n)) ~> (Ix (succ $n)) ;
rule shift-lam: (shift (Lam $body)) ~> (Lam (shift-above 1 $body)) ;
rule shift-app: (shift (App $f $x)) ~> (App (shift $f) (shift $x)) ;
```

## Phase 5: Validation

### 5.1 Scope Checking

```lego
-- Check all variables are bound
rule scope-var: (scope-check (Ix $n) $depth) ~>
  (if (< $n $depth) ok (error "unbound variable")) ;

rule scope-lam: (scope-check (Lam $body) $depth) ~>
  (scope-check $body (succ $depth)) ;
```

### 5.2 Universe Checking

```lego
-- Type : Type^1, Type^n : Type^(n+1)
rule univ-check: (type-of (Univ $k $n)) ~> (Univ $k (succ $n)) ;

-- Pi preserves universe level
rule pi-univ: (type-of (Pi $dom $cod)) ~>
  (Univ kan (max (level $dom) (level $cod))) ;
```

### 5.3 Kan Condition Verification

```lego
-- Verify boundary coherence for hcom
rule hcom-boundary: (verify-hcom $r $r' $ty $cap $sys) ~>
  (and (all-faces-agree $sys $r $cap)
       (all-pairs-compatible $sys)) ;
```

## Phase 6: Higher Inductive Types

### 6.1 Circle (S¹)

```lego
data S1 where
  | base : S1
  | loop : path S1 base base

rule elim-s1-base: (Elim base $mot [base → $b | loop → $l]) ~> $b ;
rule elim-s1-loop: (Elim (loop @$i) $mot [base → $b | loop → $l]) ~> ($l @$i) ;
```

### 6.2 Interval Endpoints

```lego
rule loop-0: (loop @Dim0) ~> base ;
rule loop-1: (loop @Dim1) ~> base ;
```

## Implementation Priority

1. **Substitution engine** - Foundation for everything
2. **β-reduction** - Basic computation
3. **Name resolution** - Surface → Core
4. **Scope checking** - Catch errors early
5. **Kan operations** - Cubical computation
6. **Type checking** - Full validation
7. **HITs** - Advanced features

## Test Cases (from redtt library)

```bash
# Basic
vendor/redtt/library/prelude.red          # Core definitions
vendor/redtt/library/data/bool.red        # Simple data type
vendor/redtt/library/data/nat.red         # Natural numbers

# Paths
vendor/redtt/library/paths/bool.red       # Bool path operations  
vendor/redtt/library/paths/nat.red        # Nat path operations

# Advanced
vendor/redtt/library/cool/mulclosure.red  # Multiplicative closure
vendor/redtt/library/cool/gcd.red         # GCD with deep nesting
vendor/redtt/library/cool/univalence.red  # Univalence theorem
```

## References

- **redtt source**: `vendor/redtt/src/core/*.ml`
- **cooltt source**: `vendor/cooltt/src/core/*.ml` (newer, cleaner)
- **Cubical Agda**: Similar approach, well-documented
- **CCHM paper**: Cubical Type Theory: a constructive interpretation of the univalence axiom
