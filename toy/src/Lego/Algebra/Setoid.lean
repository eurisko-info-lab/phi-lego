/-
  Lego.Algebra.Setoid: Base setoid infrastructure for semantic equivalence

  A setoid is a type equipped with an equivalence relation.
  This module provides the foundation for:
  - Grammar equivalence (same language recognized)
  - Term equivalence (alpha/beta/eta)
  - Rule normalization (same normal form)

  Algebraic insight: Quotients give us canonical representatives.

  Note: We use `EqRel` instead of `Setoid` to avoid conflicts with Lean's stdlib.
-/

import Lego.Algebra

namespace Lego.Algebra.Setoid

open Lego

/-! ## Equivalence Relation Definition -/

/-- An equivalence relation on a type (named EqRel to avoid stdlib Setoid conflict) -/
structure EqRel (α : Type u) where
  /-- The equivalence relation -/
  r : α → α → Prop
  /-- Proof that r is reflexive -/
  refl : ∀ x, r x x
  /-- Proof that r is symmetric -/
  symm : ∀ x y, r x y → r y x
  /-- Proof that r is transitive -/
  trans : ∀ x y z, r x y → r y z → r x z

namespace EqRel

set_option quotPrecheck false in
/-- Notation for equivalence relation -/
scoped notation:50 a " ≈[" _S "] " b => _S.r a b

/-- The trivial equivalence (equality) -/
def trivial (α : Type u) : EqRel α where
  r := Eq
  refl := Eq.refl
  symm := fun _ _ => Eq.symm
  trans := fun _ _ _ => Eq.trans

/-- The universal equivalence (everything equivalent) -/
def universal (α : Type u) : EqRel α where
  r := fun _ _ => True
  refl := fun _ => True.intro
  symm := fun _ _ _ => True.intro
  trans := fun _ _ _ _ _ => True.intro

/-- Product of equivalence relations -/
def prod (S₁ : EqRel α) (S₂ : EqRel β) : EqRel (α × β) where
  r := fun (a₁, b₁) (a₂, b₂) => S₁.r a₁ a₂ ∧ S₂.r b₁ b₂
  refl := fun (a, b) => ⟨S₁.refl a, S₂.refl b⟩
  symm := fun _ _ ⟨h₁, h₂⟩ => ⟨S₁.symm _ _ h₁, S₂.symm _ _ h₂⟩
  trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => ⟨S₁.trans _ _ _ h₁ h₃, S₂.trans _ _ _ h₂ h₄⟩

/-- Function equivalence (pointwise) -/
def func {α : Type v} (S : EqRel β) : EqRel (α → β) where
  r := fun f g => ∀ x, S.r (f x) (g x)
  refl := fun f x => S.refl (f x)
  symm := fun _ _ h x => S.symm _ _ (h x)
  trans := fun _ _ _ h₁ h₂ x => S.trans _ _ _ (h₁ x) (h₂ x)

end EqRel

/-! ## Quotient-like Operations -/

/-- A representative selector for an equivalence relation -/
structure Representative (S : EqRel α) where
  /-- Select a canonical representative -/
  repr : α → α
  /-- The representative is equivalent to the original -/
  repr_equiv : ∀ x, S.r x (repr x)
  /-- Equivalent elements have the same representative -/
  repr_canonical : ∀ x y, S.r x y → repr x = repr y

/-- Quotient element: a value tagged with its equivalence relation -/
structure Quot (S : EqRel α) where
  /-- The underlying value -/
  val : α

namespace Quot

/-- Lift a function to the quotient (must respect equivalence) -/
def lift {S : EqRel α} (f : α → β)
    (_h : ∀ a b, S.r a b → f a = f b) : Quot S → β :=
  fun q => f q.val

/-- Map a function over a quotient -/
def map {S₁ : EqRel α} {S₂ : EqRel β} (f : α → β)
    (_h : ∀ a b, S₁.r a b → S₂.r (f a) (f b)) : Quot S₁ → Quot S₂ :=
  fun q => ⟨f q.val⟩

/-- Two quotient elements are equal if their values are equivalent -/
def eq {S : EqRel α} (q₁ q₂ : Quot S) : Prop :=
  S.r q₁.val q₂.val

end Quot

/-! ## Congruence Relations -/

/-- A congruence relation respects some binary operation -/
structure Congruence (α : Type u) (op : α → α → α) extends EqRel α where
  /-- The relation respects the operation -/
  cong : ∀ a₁ a₂ b₁ b₂, r a₁ a₂ → r b₁ b₂ → r (op a₁ b₁) (op a₂ b₂)

/-- A congruence for unary operations -/
structure UnaryCongruence (α : Type u) (op : α → α) extends EqRel α where
  /-- The relation respects the operation -/
  cong : ∀ a b, r a b → r (op a) (op b)

/-! ## Equivalence Closure -/

/-- The equivalence closure of a relation -/
inductive EqvClosure (r : α → α → Prop) : α → α → Prop where
  | base : r x y → EqvClosure r x y
  | refl : EqvClosure r x x
  | symm : EqvClosure r x y → EqvClosure r y x
  | trans : EqvClosure r x y → EqvClosure r y z → EqvClosure r x z

/-- The equivalence closure forms an EqRel -/
def EqvClosure.toEqRel (r : α → α → Prop) : EqRel α where
  r := EqvClosure r
  refl := fun _ => EqvClosure.refl
  symm := fun _ _ h => EqvClosure.symm h
  trans := fun _ _ _ h₁ h₂ => EqvClosure.trans h₁ h₂

/-! ## Equivalence Relation Morphisms -/

/-- A morphism between equivalence relations preserves equivalence -/
structure EqRelMorphism (S₁ : EqRel α) (S₂ : EqRel β) where
  /-- The underlying function -/
  fn : α → β
  /-- The function preserves equivalence -/
  preserves : ∀ x y, S₁.r x y → S₂.r (fn x) (fn y)

namespace EqRelMorphism

/-- Identity morphism -/
def id (S : EqRel α) : EqRelMorphism S S where
  fn := _root_.id
  preserves := fun _ _ h => h

/-- Composition of morphisms -/
def comp (f : EqRelMorphism S₁ S₂) (g : EqRelMorphism S₂ S₃) : EqRelMorphism S₁ S₃ where
  fn := g.fn ∘ f.fn
  preserves := fun _ _ h => g.preserves _ _ (f.preserves _ _ h)

end EqRelMorphism

/-! ## Decidable Equivalence Relations -/

/-- An equivalence relation with decidable equivalence -/
structure DecEqRel (α : Type u) extends EqRel α where
  /-- Decidable equivalence check -/
  decEq : ∀ x y, Decidable (r x y)

namespace DecEqRel

/-- Check equivalence -/
def equiv (S : DecEqRel α) (x y : α) : Bool :=
  match S.decEq x y with
  | isTrue _ => true
  | isFalse _ => false

end DecEqRel

end Lego.Algebra.Setoid
