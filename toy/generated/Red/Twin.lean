/-
  Red.Twin - Twin variables for boundary coherence
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.Twin

/-! ## Syntax -/

/-- Twin variable: twin x y r a -/
inductive Term
  | twin (x y : String) (r : Dim) (a : Term) : Term

/-! ## Reduction Rules -/

/-- twin0: (twin x y 0 a) ~> [y := x] a -/
def twin0 (x y : String) (a : Term) : Term :=
  subst y (Term.var x) a

/-- twin1: (twin x y 1 a) ~> a -/
def twin1 (x y : String) (a : Term) : Term := a

/-! ## Reduction -/

def reduce : Term → Term
  | Term.twin x y r a =>
    match r with
    | Dim.zero => twin0 x y a
    | Dim.one => twin1 x y a
    | _ => Term.twin x y r a

end Red.Twin
