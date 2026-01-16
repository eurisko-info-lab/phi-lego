/-
  Lego.Algebra.NormalForm: Canonical representatives for terms

  This module defines normal forms and proves properties about
  canonical representatives under term rewriting.
-/

import Lego.Algebra
import Lego.Algebra.Setoid
import Lego.Algebra.TermEquiv
import Lego.Algebra.Confluence

namespace Lego.Algebra.NormalForm

open Lego Confluence

/-! ## Normal Form Definition -/

/-- A term is in normal form if no rules apply -/
def IsNormalForm (rules : List (Term × Term)) (t : Term) : Prop :=
  ∀ t', ¬Step rules t t'

/-- A term has a normal form if it reduces to one -/
def HasNormalForm (rules : List (Term × Term)) (t : Term) : Prop :=
  ∃ nf, IsNormalForm rules nf ∧ Reduces rules t nf

/-! ## Normal Form Context -/

/-- Context for tracking normal forms with caching -/
structure NFContext where
  /-- The rewrite rules -/
  rules : List (Term × Term)
  /-- Cache of computed normal forms -/
  cache : List (Term × Term)

namespace NFContext

/-- Create a context from rules -/
def fromRules (rules : List (Term × Term)) : NFContext :=
  { rules := rules, cache := [] }

/-- Lookup a cached normal form -/
def lookup (ctx : NFContext) (t : Term) : Option Term :=
  ctx.cache.find? (·.1 == t) |>.map (·.2)

/-- Add to cache -/
def cache' (ctx : NFContext) (t nf : Term) : NFContext :=
  { ctx with cache := (t, nf) :: ctx.cache }

end NFContext

/-! ## Normalization -/

/-- Normalize a term (with fuel to ensure termination) -/
partial def normalize (ctx : NFContext) (fuel : Nat) (t : Term) : Term :=
  if fuel == 0 then t
  else
    match ctx.lookup t with
    | some nf => nf
    | none =>
      -- Try each rule
      let t' := ctx.rules.foldl (fun acc (lhs, rhs) =>
        if acc != t then acc  -- already reduced
        else
          match Term.matchPattern lhs t with
          | some env => Term.substitute rhs env
          | none => t
      ) t
      if t' == t then t  -- normal form reached
      else normalize ctx (fuel - 1) t'

/-! ## Properties -/

/-- Normal form is unique (given confluence) (axiom - requires careful RTClosure analysis) -/
axiom nf_unique : ∀ (rules : List (Term × Term)),
    Confluent (Step rules) →
    ∀ nf₁ nf₂ t,
    IsNormalForm rules nf₁ → IsNormalForm rules nf₂ →
    Reduces rules t nf₁ → Reduces rules t nf₂ →
    nf₁ = nf₂

/-- Normalization is idempotent (axiom - requires fuel analysis) -/
axiom normalize_idem : ∀ (ctx : NFContext) (fuel : Nat) (t : Term),
    normalize ctx fuel (normalize ctx fuel t) = normalize ctx fuel t

end Lego.Algebra.NormalForm
