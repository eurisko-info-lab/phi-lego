/-
  Red.Data - User-defined data types (HITs)
  Generated from Red.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Red.Data

/-! ## Syntax -/

/-- Parameter declaration -/
structure Param where
  name : String
  tp : Term

/-- Boundary specification -/
structure Bound where
  cof : Cof
  tm : Term

/-- Constructor declaration -/
structure Constr where
  name : String
  tp : Term
  bounds : List Bound := []

/-- Data type declaration -/
structure DataDecl where
  name : String
  params : List Param
  constrs : List Constr

/-! ## Reduction Rules -/

/-- introElim: (elim e (C ms) (intro c as)) ~> ((ms c) as) -/
def introElim (e : Term) (C : Term) (ms : String → Term → Term)
              (c : String) (as : List Term) : Term :=
  ms c (Term.app (Term.var c) as)

end Red.Data
