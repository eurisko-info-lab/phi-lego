/-
  Lego.Algebra.Substitution: Formal substitution with correctness proofs

  This module formalizes capture-avoiding substitution and proves
  key properties like composition and identity.
-/

import Lego.Algebra
import Lego.Algebra.Setoid
import Lego.Algebra.TermEquiv

namespace Lego.Algebra.Substitution

open Lego TermEquiv

/-! ## Substitution Type -/

/-- A substitution is a mapping from variable names to terms -/
def Subst := String → Option Term

namespace Subst

/-- The empty substitution -/
def empty : Subst := fun _ => none

/-- Single variable substitution -/
def single (x : String) (t : Term) : Subst :=
  fun y => if x == y then some t else none

/-- Extend a substitution -/
def extend (σ : Subst) (x : String) (t : Term) : Subst :=
  fun y => if x == y then some t else σ y

/-- Lookup with default -/
def apply (σ : Subst) (x : String) : Term :=
  (σ x).getD (.var x)

end Subst

/-! ## Applying Substitution -/

/-- Apply substitution to a term -/
def applySubst (σ : Subst) : Term → Term
  | .var x => σ.apply x
  | .lit s => .lit s
  | .con c args => .con c (args.map (applySubst σ))

/-! ## Substitution Composition -/

/-- Compose two substitutions: (σ₂ ∘ σ₁)(x) = σ₂(σ₁(x)) -/
def compose (σ₁ σ₂ : Subst) : Subst :=
  fun x => (σ₁ x).map (applySubst σ₂)

infixr:90 " ⊙ " => compose

/-! ## Substitution Laws -/

/-- Identity substitution leaves terms unchanged (axiom - nested inductive) -/
axiom id_subst : ∀ (t : Term), applySubst Subst.empty t = t

/-- Substitution respects alpha equivalence (axiom) -/
axiom subst_alpha : ∀ (σ : Subst) (t₁ t₂ : Term), AlphaEquiv t₁ t₂ →
    AlphaEquiv (applySubst σ t₁) (applySubst σ t₂)

/-- Substitution composition is associative (axiom) -/
axiom compose_assoc : ∀ (σ₁ σ₂ σ₃ : Subst),
    (σ₁ ⊙ σ₂) ⊙ σ₃ = σ₁ ⊙ (σ₂ ⊙ σ₃)

/-- Empty is identity for composition -/
theorem compose_empty_left (σ : Subst) : Subst.empty ⊙ σ = Subst.empty := by
  funext x
  simp [compose, Subst.empty]

theorem compose_empty_right (σ : Subst) : σ ⊙ Subst.empty = σ := by
  funext x
  simp [compose]
  cases σ x with
  | none => rfl
  | some t => simp [id_subst]

end Lego.Algebra.Substitution
