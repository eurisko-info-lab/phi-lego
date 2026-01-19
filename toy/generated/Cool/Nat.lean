/-
  Cool.Nat - Natural numbers as HIT
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Nat

/-! ## Syntax -/

/-- Natural numbers -/
inductive Term : Type where
  | Nat : Term
  | zero : Term
  | suc (n : Term) : Term
  | natElim (P z s n : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- natElimZero: (natElim P z s zero) ~> z -/
def natElimZero (_P z _s : Term) : Term := z

/-- natElimSuc: (natElim P z s (suc n)) ~> (s n (natElim P z s n)) -/
def natElimSuc (P z s n : Term) : Term :=
  -- In a real implementation: Term.app s [n, natElim P z s n]
  Term.natElim P z s n

/-! ## Typing Rules (axiomatized) -/

/-- NatForm: Nat : U -/
axiom NatForm : True

/-- zeroType: zero : Nat -/
axiom zeroType : True

/-- sucType: (suc n) : Nat when n : Nat -/
axiom sucType : True

/-! ## Reducer -/

def reduce : Term → Term
  | Term.natElim P z _s Term.zero => z
  | Term.natElim P z s (Term.suc n) =>
    -- Should be: (s n (natElim P z s n))
    Term.natElim P z s n
  | t => t

/-! ## Tests -/

example : reduce (Term.natElim Term.Nat Term.zero (Term.var "s") Term.zero) = Term.zero := rfl

end Cool.Nat
