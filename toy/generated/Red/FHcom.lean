/-
  Red.FHcom - Fibrant homogeneous composition
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.FHcom

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

inductive Cof where
  | top : Cof
  | bot : Cof
  | eq (i j : Dim) : Cof
  deriving Repr, BEq

/-! ## Syntax -/

/-- Fibrant hcom terms -/
inductive Term : Type where
  | fhcom (r s : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- fhcomRefl: (fhcom r ~> r A sys a) ~> a -/
def fhcomRefl (_A : Term) (_sys : List (Cof × Term)) (a : Term) : Term := a

/-! ## Reducer -/

def reduce : Term → Term
  | Term.fhcom r s A sys a => if r == s then a else Term.fhcom r s A sys a
  | t => t

/-! ## Tests -/

#check reduce (Term.fhcom Dim.zero Dim.zero (Term.var "A") [] (Term.var "a"))

end Red.FHcom
