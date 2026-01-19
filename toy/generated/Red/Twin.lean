/-
  Red.Twin - Twin variables for boundary coherence
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.Twin

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

/-! ## Syntax -/

/-- Twin variable terms -/
inductive Term : Type where
  | twin (x y : String) (r : Dim) (a : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Substitution -/

/-- Substitute variable for variable in term -/
partial def substVar (from_ to_ : String) : Term → Term
  | Term.twin x y r a =>
    let x' := if x == from_ then to_ else x
    let y' := if y == from_ then to_ else y
    Term.twin x' y' r (substVar from_ to_ a)
  | Term.var name => Term.var (if name == from_ then to_ else name)

/-! ## Reduction Rules -/

/-- twin0: (twin x y 0 a) ~> [y := x] a -/
def twin0 (x y : String) (a : Term) : Term :=
  substVar y x a

/-- twin1: (twin x y 1 a) ~> a -/
def twin1 (_x _y : String) (a : Term) : Term := a

/-! ## Reducer -/

def reduce : Term → Term
  | Term.twin x y Dim.zero a => twin0 x y a
  | Term.twin _ _ Dim.one a => a
  | t => t

/-! ## Tests -/

#check reduce (Term.twin "x" "y" Dim.zero (Term.var "y"))

end Red.Twin
