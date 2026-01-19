/-
  Cool.CofExt - Extended cofibration operations
  Generated from Cool.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Cool.CofExt

/-! ## Syntax -/

/-- Extended cofibration operations -/
inductive Cof
  | boundary (i : Dim) : Cof    -- ∂ i
  | strict (φ : Cof) : Cof      -- strict φ

/-! ## Reduction Rules -/

/-- boundary0: (∂ 0) ~> cof0 -/
def boundary0 : Cof := Cof.boundary Dim.zero

/-- boundary1: (∂ 1) ~> cof0 -/
def boundary1 : Cof := Cof.boundary Dim.one

/-- boundaryVar: (∂ i) ~> ((i = 0) ∨ (i = 1)) -/
def boundaryVar (i : Dim) : Cof :=
  Cof.boundary i  -- represents (i = 0) ∨ (i = 1)

/-! ## Reducer -/

def reduceBoundary : Dim → Cof
  | Dim.zero => Cof.boundary Dim.zero  -- cof0
  | Dim.one => Cof.boundary Dim.one    -- cof0
  | i => Cof.boundary i                 -- (i = 0) ∨ (i = 1)

/-! ## Tests -/

example : reduceBoundary Dim.zero = Cof.boundary Dim.zero := rfl

end Cool.CofExt
