/-
  Red.BoxCap - Box-cap structure for fhcom
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.BoxCap

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

/-- Box and cap terms -/
inductive Term : Type where
  | box (r s : Dim) (sys : List (Cof × Term)) (a : Term) : Term
  | cap (r s : Dim) (sys : List (Cof × Term)) (a : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- capBox: (cap r ~> s sys (box r ~> s sys' a)) ~> a when r = s -/
def capBox (r s : Dim) (a : Term) : Option Term :=
  if r == s then some a else none

/-! ## Reducer -/

def reduce : Term → Term
  | Term.cap r s sys (Term.box r' s' _ a) =>
    if r == s && r == r' && s == s' then a
    else Term.cap r s sys (Term.box r' s' sys a)
  | t => t

/-! ## Tests -/

#check reduce (Term.cap Dim.zero Dim.zero [] (Term.box Dim.zero Dim.zero [] (Term.var "a")))

end Red.BoxCap
