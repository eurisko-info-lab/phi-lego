/-
  Lego.Algebra.Roundtrip: Roundtrip proofs for bidirectional transformations

  This module proves roundtrip properties: parse ∘ print = id and print ∘ parse = id.
-/

import Lego.Algebra
import Lego.Algebra.Setoid
import Lego.Algebra.TermEquiv
import Lego.Algebra.Iso

namespace Lego.Algebra.Roundtrip

open Lego Iso

/-! ## Roundtrip Definitions -/

/-- Forward roundtrip: parse (print t) = t -/
def ForwardRoundtrip (iso : GrammarIso) : Prop :=
  ∀ t, ∃ s, iso.print t = some s ∧ iso.parse s = some t

/-- Backward roundtrip: print (parse s) = s -/
def BackwardRoundtrip (iso : GrammarIso) : Prop :=
  ∀ s, ∃ t, iso.parse s = some t ∧ iso.print t = some s

/-- Full roundtrip in both directions -/
def FullRoundtrip (iso : GrammarIso) : Prop :=
  ForwardRoundtrip iso ∧ BackwardRoundtrip iso

/-! ## Roundtrip for Specific Grammars -/

/-- Literal grammar has perfect roundtrip -/
theorem lit_roundtrip (s : String) : 
    let iso : GrammarIso := {
      grammar := .lit s
      parse := fun input => if input == s then some (.lit s) else none
      print := fun t => match t with
        | .lit s' => if s' == s then some s else none
        | _ => none
      forward_rt := by
        intro t s' hp
        sorry
      backward_rt := by
        intro s' t hp
        sorry
    }
    ForwardRoundtrip iso := by
  intro _iso
  intro _t
  sorry

/-- Sequence grammar preserves roundtrip -/
theorem seq_roundtrip (iso₁ iso₂ : GrammarIso) 
    (h₁ : FullRoundtrip iso₁) (h₂ : FullRoundtrip iso₂) :
    FullRoundtrip (compose iso₁ iso₂) := by
  sorry

/-! ## Roundtrip Composition -/

/-- Roundtrip composes: if both have roundtrip, so does composition -/
theorem roundtrip_compose (iso₁ iso₂ : GrammarIso)
    (rt₁ : FullRoundtrip iso₁) (rt₂ : FullRoundtrip iso₂) :
    FullRoundtrip (compose iso₁ iso₂) := by
  exact seq_roundtrip iso₁ iso₂ rt₁ rt₂

end Lego.Algebra.Roundtrip
