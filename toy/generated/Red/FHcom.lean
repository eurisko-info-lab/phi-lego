/-
  Red.FHcom - Fibrant homogeneous composition
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.FHcom

/-! ## Syntax -/

/-- Fibrant homogeneous composition -/
inductive Term
  | fhcom (r s : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term

/-! ## Reduction Rules -/

/-- fhcomRefl: (fhcom r ~> r A sys a) ~> a -/
def fhcomRefl (r : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term := a

/-! ## Reducer -/

def reduce : Term → Term
  | Term.fhcom r s A sys a =>
    if r = s then a else Term.fhcom r s A sys a

end Red.FHcom
