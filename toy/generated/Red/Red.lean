/-
  Red - redtt-specific Extensions to CubicalTT
  Generated from Red.lego via Rosetta pipeline

  Reference: https://github.com/RedPRL/redtt

  Key additions:
  - Extension types (Ext)
  - Generalized hcom/com (ghcom, gcom)
  - User-defined data types with HIT constructors
  - Twin variables for boundary coherence
  - Restriction types
  - Fibrant homogeneous composition
  - Box/Cap structure
-/

import Red.ExtType
import Red.GCom
import Red.Data
import Red.Twin
import Red.Restrict
import Red.FHcom
import Red.BoxCap

namespace Red

/-! ## Red Language Summary

Red extends CubicalTT with:

### Extension Types (ExtType)
- `Ext x . A [φ ↦ u]` - Extension types
- `extLam x . body` - Extension lambda
- `extApp t r` - Extension application
- Beta rule: `extApp (extLam x . body) r ~> [x := r] body`

### Generalized Composition (GCom)
- `ghcom r ~> s A sys a` - Generalized homogeneous composition
- `gcom r ~> s (i . A) sys a` - Generalized composition
- Reflexivity: both reduce to `a` when `r = s`

### User-defined HITs (Data)
- `data Name params where constrs` - Data type declaration
- Constructor boundaries for HITs
- Elimination rules

### Twin Variables (Twin)
- `twin x y r a` - Twin variable for boundary coherence
- `twin x y 0 a ~> [y := x] a`
- `twin x y 1 a ~> a`

### Restriction Types (Restrict)
- `A ↾ φ` - Restrict A to cofibration φ

### Fibrant Hcom (FHcom)
- `fhcom r ~> s A sys a` - Fibrant homogeneous composition
- Reflexivity: `fhcom r ~> r A sys a ~> a`

### Box/Cap (BoxCap)
- `box r ~> s sys a` - Box construction
- `cap r ~> s sys a` - Cap projection
- `cap r ~> s sys (box r ~> s sys' a) ~> a` when `r = s`
-/

end Red
