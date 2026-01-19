/-
  Cool - cooltt-specific Extensions to CubicalTT
  Generated from Cool.lego via Rosetta pipeline

  Reference: https://github.com/RedPRL/cooltt

  Key additions:
  - Built-in HITs (Nat, Circle)
  - Signatures and structures
  - El types (universe decoding)
  - Extended cofibration operations
  - Gel types
  - Locked cofibrations
-/

import Cool.Nat
import Cool.Circle
import Cool.Signature
import Cool.El
import Cool.CofExt
import Cool.Gel
import Cool.LockedCof

namespace Cool

/-! ## Cool Language Summary

Cool extends CubicalTT with:

### Natural Numbers (Nat)
- `Nat` - Natural numbers type
- `zero` - Zero constructor
- `suc n` - Successor constructor
- `natElim P z s n` - Eliminator
- Beta rules: reduces on zero and suc

### Circle (Circle)
- `S¹` - Circle type
- `base` - Base point
- `loop i` - Loop at dimension i
- `S¹Elim P b l x` - Eliminator
- `loop 0 ~> base`, `loop 1 ~> base`

### Signatures (Signature)
- `sig { fields }` - Signature (record type)
- `struct { assigns }` - Structure (record value)
- `t . x` - Field projection
- `(struct { x := a ... }) . x ~> a`

### Universe Decoding (El)
- `El a` - Decode universe code
- `code A` - Encode type as code
- `El (code A) ~> A`

### Extended Cofibrations (CofExt)
- `∂ i` - Boundary cofibration
- `strict φ` - Strict cofibration
- `∂ i ~> (i = 0) ∨ (i = 1)`

### Gel Types (Gel)
- `Gel i A B equiv` - Gel type
- `gel i a` - Gel introduction
- `ungel i g` - Gel elimination
- Reduces at endpoints

### Locked Cofibrations (LockedCof)
- `lock φ a` - Lock under cofibration
- `unlock φ a` - Unlock under cofibration
- `unlock φ (lock φ a) ~> a` when φ holds
-/

end Cool
