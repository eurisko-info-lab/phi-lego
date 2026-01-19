/-
  Red.ExtType - Extension types
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.ExtType

/-! ## Syntax -/

/-- Extension type: Ext_x.A [φ ↦ u] -/
inductive Term
  | Ext (x : String) (A : Term) (sys : List (Cof × Term)) : Term
  | extLam (x : String) (body : Term) : Term
  | extApp (t : Term) (r : Dim) : Term

/-! ## Reduction Rules -/

/-- extBeta: (extApp (extLam x . body) r) ~> [x := r] body -/
def extBeta (x : String) (body : Term) (r : Dim) : Term :=
  subst x r body

/-! ## Typing Rules -/

/-- ExtForm: (Ext x . A [φ ↦ u]) : U when [x : I] A : U -/
structure ExtForm where
  x : String
  A : Term
  sys : List (Cof × Term)
  deriving_type : ∀ (i : Dim), hasType A U

/-! ## Tests -/

example : extBeta "i" (Term.extApp (Term.Ext "f" sorry []) (Dim.var "i")) Dim.zero =
          (Term.extApp (Term.Ext "f" sorry []) Dim.zero) := rfl

end Red.ExtType
