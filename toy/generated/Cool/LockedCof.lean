/-
  Cool.LockedCof - Locked cofibrations for modalities
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.LockedCof

/-! ## Core Types -/

inductive Cof where
  | top : Cof
  | bot : Cof
  | var (name : String) : Cof
  deriving Repr, BEq

/-! ## Syntax -/

/-- Locked cofibration operations -/
inductive Term : Type where
  | lock (φ : Cof) (a : Term) : Term
  | unlock (φ : Cof) (a : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- unlockLock: (unlock φ (lock φ a)) ~> a when φ -/
def unlockLock (φ : Cof) (a : Term) (φ_holds : Bool) : Term :=
  if φ_holds then a else Term.unlock φ (Term.lock φ a)

/-! ## Reducer -/

def reduce : Term → Term
  | Term.unlock φ (Term.lock φ' a) =>
    if φ == φ' then a else Term.unlock φ (Term.lock φ' a)
  | t => t

end Cool.LockedCof
