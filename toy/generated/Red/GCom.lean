/-
  Red.GCom - Generalized composition
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.GCom

/-! ## Syntax -/

/-- Generalized homogeneous composition -/
inductive Term
  | ghcom (r s : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term
  | gcom (r s : Dim) (x : String) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term

/-! ## Reduction Rules -/

/-- ghcomRefl: (ghcom r ~> r A sys a) ~> a -/
def ghcomRefl (r : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term := a

/-- gcomRefl: (gcom r ~> r (i . A) sys a) ~> a -/
def gcomRefl (r : Dim) (x : String) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term := a

/-! ## Tests -/

-- ghcom r ~> r A sys a reduces to a
example (A : Term) (sys : List (Cof × Term)) (a : Term) :
  ghcomRefl Dim.zero A sys a = a := rfl

end Red.GCom
