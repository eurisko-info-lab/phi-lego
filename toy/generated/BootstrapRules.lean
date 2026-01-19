/-
  Bootstrap Rules and Helper Functions

  This module contains:
  1. Hand-coded helper functions (combineSeq, splitSeq, wrapNode, unwrapNode)
     used by the interpreter during parsing
  2. Generated rewrite rules from Bootstrap.lego that express the same logic

  Eventually the hand-coded functions can be replaced by applying the rules,
  but for now we keep both for bootstrapping.

  Regenerate with:
    lake exe tolean --rules test/Bootstrap.lego -o generated/BootstrapRules.lean
-/

import Lego.Algebra

namespace Lego.Generated.Bootstrap

open Lego

/-! ## Helper Functions (used by Interp.lean) -/

/-- Combine two terms into a sequence -/
def combineSeq (t1 t2 : Term) : Term :=
  match t1, t2 with
  | .con "seq" ts, .con "seq" us => .con "seq" (ts ++ us)
  | .con "seq" ts, t => .con "seq" (ts ++ [t])
  | t, .con "seq" us => .con "seq" (t :: us)
  | .con "unit" [], t => t
  | t, .con "unit" [] => t
  | t1, t2 => .con "seq" [t1, t2]

/-- Split first element from a sequence -/
def splitSeq (t : Term) : Term × Term :=
  match t with
  | .con "seq" (h :: rest) => (h, .con "seq" rest)
  | t => (t, .con "unit" [])

/-- Wrap a term with a node name -/
def wrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con "seq" ts => .con name ts
  | _ => .con name [t]

/-- Unwrap a node if name matches -/
def unwrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con n ts => if n == name then .con "seq" ts else t
  | _ => t


/-- No rules defined -/
def allRules : List Rule := []

/-- Stub rule interpreter (no rules to apply) -/
def ruleInterp : Iso Term Term := Language.combineRules allRules

/-- Stub normalizer (just returns term as-is since no rules) -/
def normalize (t : Term) : Term := t

end Lego.Generated.Bootstrap
