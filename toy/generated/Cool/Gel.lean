/-
  Cool.Gel - Gel types (generalized extension)
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Gel

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

/-! ## Syntax -/

/-- Gel types and operations -/
inductive Term : Type where
  | Gel (i : Dim) (A B equiv : Term) : Term
  | gel (i : Dim) (a : Term) : Term
  | ungel (i : Dim) (g : Term) : Term
  | fst (t : Term) : Term
  | snd (t : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- gel0: (gel 0 a) ~> (fst a) -/
def gel0 (a : Term) : Term := Term.fst a

/-- gel1: (gel 1 a) ~> (snd a) -/
def gel1 (a : Term) : Term := Term.snd a

/-- ungel0: (ungel 0 g) ~> ((g .equiv) (g .val)) -/
def ungel0 (g : Term) : Term := Term.ungel Dim.zero g  -- simplified

/-- ungel1: (ungel 1 g) ~> (g .val) -/
def ungel1 (g : Term) : Term := Term.ungel Dim.one g   -- simplified

/-! ## Reducer -/

def reduce : Term → Term
  | Term.gel Dim.zero a => gel0 a
  | Term.gel Dim.one a => gel1 a
  | t => t

end Cool.Gel
