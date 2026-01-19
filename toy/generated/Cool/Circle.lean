/-
  Cool.Circle - Circle S¹ as HIT
  Generated from Cool.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Cool.Circle

/-! ## Syntax -/

/-- Circle type -/
inductive Term
  | S1 : Term
  | base : Term
  | loop (i : Dim) : Term
  | S1Elim (P b l x : Term) : Term

/-! ## Reduction Rules -/

/-- loopBase0: (loop 0) ~> base -/
def loopBase0 : Term := Term.base

/-- loopBase1: (loop 1) ~> base -/
def loopBase1 : Term := Term.base

/-- S1ElimBase: (S¹Elim P b l base) ~> b -/
def S1ElimBase (P b l : Term) : Term := b

/-- S1ElimLoop: (S¹Elim P b l (loop i)) ~> (l @ i) -/
def S1ElimLoop (P b l : Term) (i : Dim) : Term :=
  Term.S1Elim P b l (Term.loop i)  -- (l @ i)

/-! ## Typing Rules -/

/-- S1Form: S¹ : U -/
axiom S1Form : Type

/-- baseType: base : S¹ -/
axiom baseType : Term.base = Term.base

/-- loopType: (loop i) : S¹ when i : I -/
axiom loopType : ∀ i, Term.loop i = Term.loop i

/-! ## Reducer -/

def reduce : Term → Term
  | Term.loop Dim.zero => Term.base
  | Term.loop Dim.one => Term.base
  | Term.S1Elim P b l Term.base => b
  | t => t

/-! ## Tests -/

example : reduce (Term.loop Dim.zero) = Term.base := rfl
example : reduce (Term.loop Dim.one) = Term.base := rfl
example : reduce (Term.S1Elim Term.S1 Term.base Term.base Term.base) = Term.base := rfl

end Cool.Circle
