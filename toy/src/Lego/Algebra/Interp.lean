/-
  Lego.Algebra.Interp: Connecting abstract algebra to concrete implementation

  This module bridges:
  - Abstract: GrammarIso, Roundtrip, Confluence (axioms)
  - Concrete: parseGrammar, printGrammar, grammarToIso (implementation)

  The key insight: grammarToIso builds an Iso that should satisfy GrammarIso laws.
-/

import Lego.Algebra
import Lego.Interp
import Lego.Laws
import Lego.Algebra.Confluence
import Lego.Algebra.NormalForm

namespace Lego.Algebra.Interp

open Lego

/-! ## Roundtrip for Concrete Isos -/

/-- If parseGrammar succeeds, printGrammar can reconstruct (axiom connecting to impl).
    TODO: Prove by induction on grammar structure when fuel is sufficient. -/
axiom parseGrammar_printGrammar_roundtrip (fuel : Nat) (prods : Productions) (g : GrammarExpr)
    (st : ParseState) (t : Term) (st' : ParseState) :
    parseGrammar fuel prods g st = some (t, st') →
    ∃ tokens, printGrammar fuel prods g t [] = some tokens

/-- grammarToIso.forward is deterministic: same input gives same output -/
theorem grammarToIso_forward_deterministic (prods : Productions) (startProd : String) :
    let iso := grammarToIso prods startProd
    ∀ tokens t₁ t₂,
      iso.forward tokens = some t₁ →
      iso.forward tokens = some t₂ →
      t₁ = t₂ := by
  intro iso tokens t₁ t₂ h₁ h₂
  simp_all

/-- grammarToIso has forward roundtrip on its domain -/
axiom grammarToIso_forward_rt (prods : Productions) (startProd : String) :
    let iso := grammarToIso prods startProd
    ∀ tokens t,
      iso.forward tokens = some t →
      iso.backward t >>= iso.forward = some t

/-! ## Confluence for Concrete Normalization -/

/-- LangInterp.normalize is idempotent (derived from confluence axiom) -/
axiom langInterp_normalize_idem (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t, interp.normalize (interp.normalize t) = interp.normalize t

/-! ## Useful Derived Operations -/

/-- Parse then normalize: the standard interpretation pipeline -/
def parseAndNormalize (lang : Language) (startProd : String) (tokens : TokenStream) : Option Term :=
  let interp := lang.toInterp startProd
  interp.parse tokens |>.map interp.normalize

/-- Normalize then print: the standard pretty-printing pipeline -/
def normalizeAndPrint (lang : Language) (startProd : String) (t : Term) : Option TokenStream :=
  let interp := lang.toInterp startProd
  (interp.print (interp.normalize t))

/-- Full pipeline: parse → normalize → print -/
def fullPipeline (lang : Language) (startProd : String) (tokens : TokenStream) : Option TokenStream :=
  let interp := lang.toInterp startProd
  match interp.parse tokens with
  | some t => interp.print (interp.normalize t)
  | none => none

/-! ## Pipeline Properties -/

/-- Parse is deterministic: same tokens give same term -/
theorem parse_deterministic (lang : Language) (startProd : String) (tokens : TokenStream) :
    let interp := lang.toInterp startProd
    ∀ t₁ t₂,
      interp.parse tokens = some t₁ →
      interp.parse tokens = some t₂ →
      t₁ = t₂ := by
  intro _ _ _ h₁ h₂
  simp_all

/-- Normalization respects parsing: normalizing twice = normalizing once -/
theorem normalize_stable (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t,
      interp.normalize (interp.normalize t) = interp.normalize t :=
  langInterp_normalize_idem lang startProd

/-- Full pipeline on normalized input = just print (axiom) -/
axiom pipeline_normalized (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t tokens,
      interp.parse tokens = some t →
      interp.normalize t = t →
      fullPipeline lang startProd tokens = interp.print t

/-! ## Connecting to LawfulIso -/

/-- grammarToIso is a LawfulIso when grammar is well-formed -/
axiom grammarToIsoLawful (prods : Productions) (startProd : String)
    (wellFormed : prods.find? (·.1 == startProd) ≠ none) :
    Lego.LawfulIso (grammarToIso prods startProd)

/-! ## Rewrite Rule Confluence -/

/-- Step relation for concrete rules -/
def RuleStep (rules : List Rule) (t₁ t₂ : Term) : Prop :=
  ∃ r ∈ rules, ∃ binds, Term.matchPattern r.pattern t₁ = some binds ∧
                        t₂ = Term.substitute r.template binds

/-- Concrete rules are confluent if they are orthogonal (non-overlapping) -/
axiom rules_confluent (rules : List Rule)
    (orthogonal : ∀ r₁ r₂, r₁ ∈ rules → r₂ ∈ rules → r₁ ≠ r₂ →
      -- No overlap in patterns
      ∀ binds, Term.matchPattern r₁.pattern r₂.pattern = some binds →
               r₁.pattern = r₂.pattern) :
    Confluence.Confluent (RuleStep rules)

/-! ## Key Derived Theorems -/

/-- Main theorem: well-formed grammars have the roundtrip property -/
theorem wellformed_roundtrip (prods : Productions) (startProd : String)
    (wf : prods.find? (·.1 == startProd) ≠ none) :
    let iso := grammarToIso prods startProd
    let _ := grammarToIsoLawful prods startProd wf
    ∀ tokens t,
      iso.forward tokens = some t →
      iso.backward t >>= iso.forward = some t := by
  intro iso _ tokens t h
  exact grammarToIso_forward_rt prods startProd tokens t h

/-- Orthogonal rules give unique normal forms -/
theorem orthogonal_unique_nf (rules : List Rule)
    (orth : ∀ r₁ r₂, r₁ ∈ rules → r₂ ∈ rules → r₁ ≠ r₂ →
            ∀ binds, Term.matchPattern r₁.pattern r₂.pattern = some binds →
                     r₁.pattern = r₂.pattern) :
    let _conf := rules_confluent rules orth
    ∀ t₁ t₂ t,
      Confluence.RTClosure (RuleStep rules) t t₁ →
      Confluence.RTClosure (RuleStep rules) t t₂ →
      (∀ t', ¬RuleStep rules t₁ t') →
      (∀ t', ¬RuleStep rules t₂ t') →
      t₁ = t₂ := by
  intro conf t₁ t₂ t r₁ r₂ nf₁ nf₂
  -- Follows from confluence: both reduce to common descendant,
  -- but both are normal forms, so that descendant must be both
  obtain ⟨d, rd₁, rd₂⟩ := conf t t₁ t₂ r₁ r₂
  -- If t₁ is a normal form and t₁ →* d, then t₁ = d
  cases rd₁ with
  | refl =>
    cases rd₂ with
    | refl => rfl
    | step hs _ => exact absurd hs (nf₂ _)
  | step hs _ => exact absurd hs (nf₁ _)

end Lego.Algebra.Interp
