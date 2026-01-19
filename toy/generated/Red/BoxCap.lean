/-
  Red.BoxCap - Box-cap structure for fhcom
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.BoxCap

/-! ## Syntax -/

/-- Box and cap operations -/
inductive Term
  | box (r s : Dim) (sys : List (Cof × Term)) (a : Term) : Term
  | cap (r s : Dim) (sys : List (Cof × Term)) (a : Term) : Term

/-! ## Reduction Rules -/

/-- capBox: (cap r ~> s sys (box r ~> s sys' a)) ~> a when r = s -/
def capBox (r s : Dim) (sys sys' : List (Cof × Term)) (a : Term) : Option Term :=
  if r = s then some a else none

/-! ## Reducer -/

def reduce : Term → Term
  | Term.cap r s sys (Term.box r' s' sys' a) =>
    if r = s && r = r' && s = s' then a
    else Term.cap r s sys (Term.box r' s' sys' a)
  | t => t

end Red.BoxCap
