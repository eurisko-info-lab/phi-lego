/-
  Cool.CofExt - Extended cofibration operations
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.CofExt

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

/-! ## Syntax -/

/-- Extended cofibration operations -/
inductive Cof : Type where
  | boundary (i : Dim) : Cof    -- ∂ i
  | strict (φ : Cof) : Cof      -- strict φ
  | top : Cof
  | bot : Cof
  | eq (i j : Dim) : Cof
  | join (φ ψ : Cof) : Cof
  | meet (φ ψ : Cof) : Cof
  deriving Repr, BEq

/-! ## Reduction Rules -/

/-- boundaryVar: (∂ i) ~> ((i = 0) ∨ (i = 1)) -/
def boundaryExpand (i : Dim) : Cof :=
  Cof.join (Cof.eq i Dim.zero) (Cof.eq i Dim.one)

/-! ## Reducer -/

def reduce : Cof → Cof
  | Cof.boundary i =>
    match i with
    | Dim.zero => Cof.bot  -- boundary at 0 is false
    | Dim.one => Cof.bot   -- boundary at 1 is false
    | _ => boundaryExpand i
  | c => c

/-! ## Tests -/

example : reduce (Cof.boundary Dim.zero) = Cof.bot := rfl

end Cool.CofExt
