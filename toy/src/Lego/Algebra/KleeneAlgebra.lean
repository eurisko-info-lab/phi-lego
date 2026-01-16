/-
  Lego.Algebra.KleeneAlgebra: Grammar as Kleene algebra with formal laws

  A Kleene algebra provides the algebraic foundation for regular expressions
  and grammars. This captures: alternation (|), sequence (⬝), star (*).
  
  Key insight: Grammar combinators form a Kleene algebra, giving us
  free theorems about grammar equivalence.
-/

import Lego.Algebra
import Lego.Algebra.Setoid

namespace Lego.Algebra.KleeneAlgebra

open Lego

/-! ## Kleene Algebra Definition -/

/-- A Kleene algebra is a semiring with iteration (star) -/
class KleeneAlgebra (α : Type u) extends Add α, Mul α, One α, Zero α, LE α where
  /-- Alternative is commutative -/
  alt_comm : ∀ x y : α, x + y = y + x
  /-- Alternative is associative -/
  alt_assoc : ∀ x y z : α, (x + y) + z = x + (y + z)
  /-- Zero is identity for alternative -/
  alt_zero : ∀ x : α, x + 0 = x
  /-- Alternative is idempotent -/
  alt_idem : ∀ x : α, x + x = x
  /-- Sequence is associative -/
  seq_assoc : ∀ x y z : α, (x * y) * z = x * (y * z)
  /-- One is identity for sequence -/
  seq_one_left : ∀ x : α, 1 * x = x
  seq_one_right : ∀ x : α, x * 1 = x
  /-- Zero annihilates sequence -/
  seq_zero_left : ∀ x : α, 0 * x = 0
  seq_zero_right : ∀ x : α, x * 0 = 0
  /-- Left distributivity -/
  distrib_left : ∀ x y z : α, x * (y + z) = x * y + x * z
  /-- Right distributivity -/
  distrib_right : ∀ x y z : α, (x + y) * z = x * z + y * z
  /-- Star operation -/
  star : α → α
  /-- Star unfold: 1 + x * x* = x* -/
  star_unfold : ∀ x : α, 1 + x * star x = star x
  /-- Star induction left -/
  star_ind_left : ∀ x y z : α, y + x * z ≤ z → star x * y ≤ z
  /-- Star induction right -/  
  star_ind_right : ∀ x y z : α, y + z * x ≤ z → y * star x ≤ z

/-- Notation for star -/
postfix:max "*" => KleeneAlgebra.star

namespace KleeneAlgebra

/-- Star of zero is one -/
theorem star_zero [KleeneAlgebra α] : (0 : α)* = 1 := by sorry

/-- Star of one is one -/
theorem star_one [KleeneAlgebra α] : (1 : α)* = 1 := by sorry

/-- Star is monotonic -/
theorem star_mono [KleeneAlgebra α] {x y : α} (h : x ≤ y) : x* ≤ y* := by sorry

/-- Double star -/
theorem star_star [KleeneAlgebra α] (x : α) : (x*)* = x* := by sorry

end KleeneAlgebra

/-! ## Grammar Kleene Algebra -/

/-- Grammar equivalence: two grammars accept the same language -/
inductive GrammarEquiv : GrammarExpr → GrammarExpr → Prop where
  | refl : ∀ g, GrammarEquiv g g
  | symm : GrammarEquiv g₁ g₂ → GrammarEquiv g₂ g₁
  | trans : GrammarEquiv g₁ g₂ → GrammarEquiv g₂ g₃ → GrammarEquiv g₁ g₃
  | alt_comm : GrammarEquiv (GrammarExpr.alt g₁ g₂) (GrammarExpr.alt g₂ g₁)
  | alt_assoc : GrammarEquiv (GrammarExpr.alt (GrammarExpr.alt g₁ g₂) g₃) 
                             (GrammarExpr.alt g₁ (GrammarExpr.alt g₂ g₃))
  | seq_assoc : GrammarEquiv ((g₁ ⬝ g₂) ⬝ g₃) (g₁ ⬝ (g₂ ⬝ g₃))
  | star_unfold : GrammarEquiv (GrammarExpr.alt GrammarExpr.empty (g ⬝ g.star)) g.star

/-- Grammar equivalence is an equivalence relation -/
def grammarEqRel : Setoid.EqRel GrammarExpr where
  r := GrammarEquiv
  refl := GrammarEquiv.refl
  symm := fun _ _ => GrammarEquiv.symm
  trans := fun _ _ _ => GrammarEquiv.trans

/-! ## Derived Properties -/

/-- Alternative is commutative -/
theorem alt_comm' (g₁ g₂ : GrammarExpr) : GrammarEquiv (GrammarExpr.alt g₁ g₂) (GrammarExpr.alt g₂ g₁) :=
  GrammarEquiv.alt_comm

/-- Alternative is associative -/
theorem alt_assoc' (g₁ g₂ g₃ : GrammarExpr) : 
    GrammarEquiv (GrammarExpr.alt (GrammarExpr.alt g₁ g₂) g₃) 
                 (GrammarExpr.alt g₁ (GrammarExpr.alt g₂ g₃)) :=
  GrammarEquiv.alt_assoc

/-- Sequence is associative -/
theorem seq_assoc' (g₁ g₂ g₃ : GrammarExpr) : 
    GrammarEquiv ((g₁ ⬝ g₂) ⬝ g₃) (g₁ ⬝ (g₂ ⬝ g₃)) :=
  GrammarEquiv.seq_assoc

/-- Star unfolds -/
theorem star_unfold' (g : GrammarExpr) : 
    GrammarEquiv (GrammarExpr.alt GrammarExpr.empty (g ⬝ g.star)) g.star :=
  GrammarEquiv.star_unfold

/-! ## Grammar without star (finite iterations only) -/

/-- Check if a grammar uses star -/
def hasStar : GrammarExpr → Bool
  | .mk .empty => false
  | .mk (.lit _) => false
  | .mk (.ref _) => false
  | .mk (.seq g₁ g₂) => hasStar g₁ || hasStar g₂
  | .mk (.alt g₁ g₂) => hasStar g₁ || hasStar g₂
  | .mk (.star _) => true
  | .mk (.bind _ g) => hasStar g
  | .mk (.node _ g) => hasStar g

/-- A finite grammar has no star -/
def isFinite (g : GrammarExpr) : Prop := hasStar g = false

end Lego.Algebra.KleeneAlgebra
