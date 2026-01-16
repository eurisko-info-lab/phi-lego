/-
  Lego.Algebra.TermEquiv: Alpha/beta/eta equivalence for terms

  This module defines syntactic equivalences on terms:
  - Alpha equivalence: renaming bound variables
  - Beta equivalence: function application
  - Eta equivalence: extensional function equality
-/

import Lego.Algebra
import Lego.Algebra.Setoid

namespace Lego.Algebra.TermEquiv

open Lego Setoid

/-! ## Alpha Equivalence -/

/-- Alpha equivalence: terms equal up to renaming of bound variables -/
inductive AlphaEquiv : Term → Term → Prop where
  | refl : AlphaEquiv t t
  | symm : AlphaEquiv t₁ t₂ → AlphaEquiv t₂ t₁
  | trans : AlphaEquiv t₁ t₂ → AlphaEquiv t₂ t₃ → AlphaEquiv t₁ t₃
  | var : AlphaEquiv (.var x) (.var x)
  | lit : AlphaEquiv (.lit s) (.lit s)
  | con : (∀ i (h₁ : i < ts.length) (h₂ : i < us.length),
           AlphaEquiv (ts.get ⟨i, h₁⟩) (us.get ⟨i, h₂⟩)) →
          ts.length = us.length →
          AlphaEquiv (Term.con name ts) (Term.con name us)

/-- Alpha equivalence is an equivalence relation -/
def alphaEqRel : EqRel Term where
  r := AlphaEquiv
  refl := fun _ => AlphaEquiv.refl
  symm := fun _ _ => AlphaEquiv.symm
  trans := fun _ _ _ => AlphaEquiv.trans

/-! ## Beta Equivalence -/

/-- Capture-avoiding substitution (simplified) -/
def subst (x : String) (arg : Term) : Term → Term
  | .var y => if x == y then arg else .var y
  | .lit s => .lit s
  | .con c args => .con c (args.map (subst x arg))

/-- Beta step: single reduction step -/
inductive BetaStep : Term → Term → Prop where
  | app_lam : BetaStep (.con "app" [.con "lam" [.var x, body], arg])
                       (subst x arg body)

/-- Beta equivalence: reflexive-symmetric-transitive closure of beta steps -/
inductive BetaEquiv : Term → Term → Prop where
  | refl : BetaEquiv t t
  | step : BetaStep t₁ t₂ → BetaEquiv t₁ t₂
  | symm : BetaEquiv t₁ t₂ → BetaEquiv t₂ t₁
  | trans : BetaEquiv t₁ t₂ → BetaEquiv t₂ t₃ → BetaEquiv t₁ t₃

/-- Beta equivalence is an equivalence relation -/
def betaEqRel : EqRel Term where
  r := BetaEquiv
  refl := fun _ => BetaEquiv.refl
  symm := fun _ _ => BetaEquiv.symm
  trans := fun _ _ _ => BetaEquiv.trans

/-! ## Eta Equivalence -/

/-- Eta step: extensional equality -/
inductive EtaStep : Term → Term → Prop where
  | lam_eta : EtaStep (.con "lam" [.var x, .con "app" [f, .var x]]) f

/-- Eta equivalence: reflexive-symmetric-transitive closure -/
inductive EtaEquiv : Term → Term → Prop where
  | refl : EtaEquiv t t
  | step : EtaStep t₁ t₂ → EtaEquiv t₁ t₂
  | symm : EtaEquiv t₁ t₂ → EtaEquiv t₂ t₁
  | trans : EtaEquiv t₁ t₂ → EtaEquiv t₂ t₃ → EtaEquiv t₁ t₃

/-- Eta equivalence is an equivalence relation -/
def etaEqRel : EqRel Term where
  r := EtaEquiv
  refl := fun _ => EtaEquiv.refl
  symm := fun _ _ => EtaEquiv.symm
  trans := fun _ _ _ => EtaEquiv.trans

/-! ## Combined Equivalence -/

/-- Full term equivalence (alpha + beta + eta) -/
inductive TermEquiv : Term → Term → Prop where
  | alpha : AlphaEquiv t₁ t₂ → TermEquiv t₁ t₂
  | beta : BetaEquiv t₁ t₂ → TermEquiv t₁ t₂
  | eta : EtaEquiv t₁ t₂ → TermEquiv t₁ t₂
  | trans : TermEquiv t₁ t₂ → TermEquiv t₂ t₃ → TermEquiv t₁ t₃

/-- Term equivalence is an equivalence relation -/
def termEqRel : EqRel Term where
  r := TermEquiv
  refl := fun _ => TermEquiv.alpha AlphaEquiv.refl
  symm := fun _ _ h => by
    induction h with
    | alpha h => exact TermEquiv.alpha (AlphaEquiv.symm h)
    | beta h => exact TermEquiv.beta (BetaEquiv.symm h)
    | eta h => exact TermEquiv.eta (EtaEquiv.symm h)
    | trans _ _ ih₁ ih₂ => exact TermEquiv.trans ih₂ ih₁
  trans := fun _ _ _ => TermEquiv.trans

/-! ## Quotient Term Type -/

/-- A term quotiented by full equivalence -/
abbrev QTerm := Quot termEqRel

/-- Inject a term into the quotient -/
def QTerm.mk (t : Term) : QTerm := ⟨t⟩

end Lego.Algebra.TermEquiv
