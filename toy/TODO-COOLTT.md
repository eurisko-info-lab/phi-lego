# TODO: cooltt/redtt Feature Parity

This document tracks missing features needed for full cooltt/redtt compatibility.

## Priority 1: Core Infrastructure

### [x] Conversion Module (`Conversion.lean`) ✓ DONE
Equality and subtyping checking for types and terms.
- [x] `equate_tp` - Type equality checking
- [x] `equate_con` - Term equality checking  
- [x] `equate_cut` → `equate_neutral` - Neutral term equality
- [x] `equate_cof` - Cofibration equality
- [x] `equate_dim` - Dimension equality
- [ ] Handle stuck/neutral terms (partial)
- [ ] `approx_cof` - Cofibration approximation

### [x] RefineMonad (`RefineMonad.lean`) ✓ DONE
Monadic infrastructure for elaboration/refinement.
- [x] `RefineM` monad with state for unification
- [x] `RefineEnv` → `LocalEnv` for tracking locals
- [x] `GlobalEnv` for globals, holes
- [x] Error handling: `RefineError`, `refineError`
- [x] `abstract` for binding variables
- [x] Span/location tracking for errors
- [ ] Full quote/eval integration

## Priority 2: Evaluation & Building

### [ ] Full Semantics (`Semantics.lean`)
Complete evaluation with Kan operations.
- [ ] `do_rigid_coe` - Rigid coercion computation
- [ ] `do_rigid_hcom` - Rigid hcom computation  
- [ ] `dispatch_rigid_coe` - Determine coe reduction strategy
- [ ] `dispatch_rigid_hcom` - Determine hcom reduction strategy
- [ ] Full V-type computation rules
- [ ] Full FHCom computation rules
- [ ] `splice_tm` / `splice_tp` - Splicing operations

### [x] TermBuilder (`TermBuilder.lean`) ✓ DONE
De Bruijn-free term construction.
- [x] `BuildM` monad with level tracking
- [x] `lam`, `pi`, `sigma`, `path`, `plam`, `sub` binders
- [x] `ap`, `papp`, `fst`, `snd` eliminators
- [x] `dim0`, `dim1`, dimension builders
- [x] `top`, `bot`, `eq`, `cof_and`, `cof_or`, `boundary` cofibrations
- [x] `coe`, `hcom`, `com` Kan operations
- [x] `v`, `vIn`, `vProj` V-type constructors
- [x] Helper combinators: `lams`, `pis`, `const`
- [ ] `Equiv` module (equivalence type helpers)
- [ ] `Kan` module (type-specific Kan ops)

## Priority 3: Extended Tactics

### [ ] Extend Tactic Module (`Tactic.lean`)
Full refiner tactics matching cooltt.
- [ ] `Univ` tactics:
  - [ ] `code_v` - V-type code formation
  - [ ] `ext` - Extension type formation
  - [ ] `hcom`, `com`, `coe` - Kan operation tactics
  - [ ] `hcom_chk` - Checking variant of hcom
- [ ] `El`, `ElV`, `ElHCom` modules for element types
- [ ] `Path` module: `intro`, `elim`
- [ ] `Cof` module: `eq`, `le`, `join`, `meet`, `boundary`, `split`
- [ ] `Prf` module for proof formation
- [ ] `Telescope`, `KanTelescope` for records
- [ ] `Structural` module:
  - [ ] `let_`, `let_syn`
  - [ ] `lookup_var`
  - [ ] `generalize`
  - [ ] `unfold`
  - [ ] `abstract`
- [ ] `Probe`, `Hole` modules for debugging

## Priority 4: Elaboration

### [ ] Elaboration Module (`Elaborate.lean`)
Connect surface syntax to tactics.
- [ ] `chk_tm` - Checking elaboration
- [ ] `syn_tm` - Synthesis elaboration
- [ ] `chk_tp` - Type elaboration
- [ ] `chk_tp_in_tele` - Telescopic type elaboration
- [ ] Handle all concrete syntax constructs
- [ ] Integration with Tactic module

## Priority 5: Type Extensions

### [ ] Glue Types
For univalence.
- [ ] `Glue` type formation
- [ ] `glue` introduction
- [ ] `unglue` elimination
- [ ] Kan operations for Glue

### [ ] Extension Types (n-ary)
Currently only paths (1-ary).
- [ ] `Ext` n-ary formation
- [ ] `ExtLam` introduction
- [ ] `ExtApp` elimination
- [ ] Boundary handling

### [ ] Signatures/Records
Dependent records with labels.
- [ ] `Signature` type formation
- [ ] `Struct` introduction
- [ ] `Proj` elimination
- [ ] `Telescope` infrastructure

### [ ] User-defined Data Types (from redtt)
- [ ] Data type declarations
- [ ] Constructor introduction
- [ ] Eliminator generation
- [ ] Positivity checking

## Priority 6: Domain/Semantic Types

### [ ] Expand Domain Types (`Core.lean`)
Full semantic domain.
- [ ] `D.con` - Semantic values
- [ ] `D.tp` - Semantic types  
- [ ] `D.cut` - Neutral terms with type
- [ ] `D.env` - Evaluation environments
- [ ] `D.tm_clo`, `D.tp_clo` - Closures
- [ ] `D.kan_tele` - Kan telescopes
- [ ] `D.tele` - Regular telescopes

## Current Status

### Completed Modules
- [x] `Core.lean` - Basic IR with Expr type
- [x] `Cofibration.lean` - Cofibration logic
- [x] `Splice.lean` - Term splicing
- [x] `Tactic.lean` - Basic bidirectional tactics (Tp, Chk, Syn)
- [x] `Kan.lean` - Basic Kan operations
- [x] `VType.lean` - V-type support
- [x] `FHCom.lean` - FHCom support
- [x] `ExtType.lean` - Extension types (paths)
- [x] `SubType.lean` - Sub types
- [x] `HIT.lean` - Higher inductive types (Nat, Circle)
- [x] `Signature.lean` - Basic signatures
- [x] `Quote.lean` - NbE quotation
- [x] `Unify.lean` - Basic unification
- [x] `GlobalEnv.lean` - Global environment
- [x] `Elaborate.lean` - Basic elaboration
- [x] `Datatype.lean` - Basic datatypes
- [x] `Module.lean` - Module system

### Test Coverage
- 662 tests passing
- Core IR, paths, Kan ops, cofibrations covered
- Type checking, elaboration basics covered
