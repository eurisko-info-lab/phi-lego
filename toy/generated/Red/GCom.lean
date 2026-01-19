/-
  Red.GCom - Generalized composition
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.GCom

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

/-- Term type with generalized composition -/
inductive Term : Type where
  | ghcom (r s : Dim) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term
  | gcom (r s : Dim) (x : String) (A : Term) (sys : List (Cof × Term)) (a : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- ghcomRefl: (ghcom r ~> r A sys a) ~> a -/
def ghcomRefl (_A : Term) (_sys : List (Cof × Term)) (a : Term) : Term := a

/-- gcomRefl: (gcom r ~> r (i . A) sys a) ~> a -/
def gcomRefl (_x : String) (_A : Term) (_sys : List (Cof × Term)) (a : Term) : Term := a

/-! ## Reducer -/

def reduce : Term → Term
  | Term.ghcom r s A sys a => if r == s then a else Term.ghcom r s A sys a
  | Term.gcom r s x A sys a => if r == s then a else Term.gcom r s x A sys a
  | t => t

/-! ## Tests -/

#check reduce (Term.ghcom Dim.zero Dim.zero (Term.var "A") [] (Term.var "a"))

end Red.GCom
