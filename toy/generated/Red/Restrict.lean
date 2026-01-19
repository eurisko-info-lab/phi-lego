/-
  Red.Restrict - Restriction types
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.Restrict

/-! ## Syntax -/

/-- Restriction type: A ↾ φ -/
inductive Term
  | restrict (A : Term) (φ : Cof) : Term

/-! ## Typing Rules -/

/-- restrictForm: (A ↾ φ) : U when A : U -/
structure RestrictForm where
  A : Term
  φ : Cof
  A_type : hasType A U

end Red.Restrict
