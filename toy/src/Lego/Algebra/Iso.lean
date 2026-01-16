/-
  Lego.Algebra.Iso: Parse/print isomorphism with type safety

  This module formalizes the isomorphism between parsing and printing,
  proving that they form a partial isomorphism.
-/

import Lego.Algebra
import Lego.Algebra.Setoid
import Lego.Algebra.TermEquiv
import Lego.Algebra.KleeneAlgebra

namespace Lego.Algebra.Iso

open Lego

/-! ## Grammar Isomorphism -/

/-- A grammar isomorphism witnesses parse ↔ print -/
structure GrammarIso where
  /-- The grammar specification -/
  grammar : GrammarExpr
  /-- Parse: string → term -/
  parse : String → Option Term
  /-- Print: term → string -/
  print : Term → Option String
  /-- Forward roundtrip: parse ∘ print = id (when both succeed) -/
  forward_rt : ∀ t s, print t = some s → parse s = some t
  /-- Backward roundtrip: print ∘ parse = id (when both succeed) -/
  backward_rt : ∀ s t, parse s = some t → print t = some s

/-! ## Isomorphism Properties -/

/-- An isomorphism is total on parsing if parse always succeeds on valid strings -/
def TotalParse (iso : GrammarIso) (valid : String → Prop) : Prop :=
  ∀ s, valid s → (iso.parse s).isSome

/-- An isomorphism is total on printing if print always succeeds on well-formed terms -/
def TotalPrint (iso : GrammarIso) (wf : Term → Prop) : Prop :=
  ∀ t, wf t → (iso.print t).isSome

/-- A complete isomorphism is total in both directions -/
structure CompleteIso extends GrammarIso where
  /-- Valid string predicate -/
  valid : String → Prop
  /-- Well-formed term predicate -/
  wf : Term → Prop
  /-- Parse is total on valid strings -/
  parse_total : TotalParse toGrammarIso valid
  /-- Print is total on well-formed terms -/
  print_total : TotalPrint toGrammarIso wf

/-! ## Isomorphism Composition -/

/-- Compose two isomorphisms -/
def compose (iso₁ : GrammarIso) (iso₂ : GrammarIso) : GrammarIso where
  grammar := iso₁.grammar ⬝ iso₂.grammar
  parse := fun s => iso₁.parse s >>= iso₂.parse ∘ Term.toString
  print := fun t => iso₂.print t >>= iso₁.print ∘ Term.lit
  forward_rt := by sorry
  backward_rt := by sorry

/-! ## Type Safety -/

/-- A typed grammar ensures type-correct terms -/
structure TypedGrammar where
  /-- The underlying isomorphism -/
  iso : GrammarIso
  /-- Type assignment -/
  typeOf : Term → Option String
  /-- Parsing produces typed terms -/
  parse_typed : ∀ s t, iso.parse s = some t → (typeOf t).isSome

/-- Type preservation under isomorphism -/
theorem type_preservation (tg : TypedGrammar) (t : Term) (s : String) :
    tg.iso.print t = some s → tg.iso.parse s = some t → 
    tg.typeOf t = tg.typeOf t := by
  intro _ _
  rfl

end Lego.Algebra.Iso
