/-
  Cool.LockedCof - Locked cofibrations for modalities
  Generated from Cool.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Cool.LockedCof

/-! ## Syntax -/

/-- Locked cofibration operations -/
inductive Term
  | lock (φ : Cof) (a : Term) : Term
  | unlock (φ : Cof) (a : Term) : Term

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
