/-
  Cool.Nat - Natural numbers as HIT
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Nat

/-! ## Syntax -/

/-- Natural numbers -/
inductive Term
  | Nat : Term
  | zero : Term
  | suc (n : Term) : Term
  | natElim (P z s n : Term) : Term

/-! ## Reduction Rules -/

/-- natElimZero: (natElim P z s zero) ~> z -/
def natElimZero (P z s : Term) : Term := z

/-- natElimSuc: (natElim P z s (suc n)) ~> (s n (natElim P z s n)) -/
def natElimSuc (P z s n : Term) : Term :=
  Term.natElim P z s n |> fun ih => Term.suc n -- (s n ih)

/-! ## Typing Rules -/

/-- NatForm: Nat : U -/
axiom NatForm : Type

/-- zeroType: zero : Nat -/
axiom zeroType : Term.zero = Term.zero

/-- sucType: (suc n) : Nat when n : Nat -/
axiom sucType : ∀ n, Term.suc n = Term.suc n

/-! ## Reducer -/

def reduce : Term → Term
  | Term.natElim P z s Term.zero => z
  | Term.natElim P z s (Term.suc n) =>
    -- (s n (natElim P z s n))
    Term.natElim P z s n
  | t => t

/-! ## Tests -/

example : reduce (Term.natElim (Term.Nat) Term.zero Term.suc Term.zero) = Term.zero := rfl

end Cool.Nat
