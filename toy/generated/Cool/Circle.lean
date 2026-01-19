/-
  Cool.Circle - Circle S¹ as HIT
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Circle

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

/-! ## Syntax -/

/-- Circle type terms -/
inductive Term : Type where
  | S1 : Term
  | base : Term
  | loop (i : Dim) : Term
  | S1Elim (P b l x : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- loopBase0: (loop 0) ~> base -/
def loopBase0 : Term := Term.base

/-- loopBase1: (loop 1) ~> base -/
def loopBase1 : Term := Term.base

/-- S1ElimBase: (S¹Elim P b l base) ~> b -/
def S1ElimBase (_P b _l : Term) : Term := b

/-- S1ElimLoop: (S¹Elim P b l (loop i)) ~> (l @ i) -/
def S1ElimLoop (_P _b l : Term) (_i : Dim) : Term := l  -- simplified

/-! ## Typing Rules (axiomatized) -/

axiom S1Form : True
axiom baseType : True
axiom loopType : True

/-! ## Reducer -/

def reduce : Term → Term
  | Term.loop Dim.zero => Term.base
  | Term.loop Dim.one => Term.base
  | Term.S1Elim _P b _l Term.base => b
  | t => t

/-! ## Tests -/

example : reduce (Term.loop Dim.zero) = Term.base := rfl
example : reduce (Term.loop Dim.one) = Term.base := rfl
example : reduce (Term.S1Elim Term.S1 Term.base Term.base Term.base) = Term.base := rfl

end Cool.Circle
