/-
  Cool.Gel - Gel types (generalized extension)
  Generated from Cool.lego via Rosetta pipeline
-/

import Lego.Cubical.Core

namespace Cool.Gel

/-! ## Syntax -/

/-- Gel types and operations -/
inductive Term
  | Gel (i : Dim) (A B equiv : Term) : Term
  | gel (i : Dim) (a : Term) : Term
  | ungel (i : Dim) (g : Term) : Term

/-! ## Reduction Rules -/

/-- gel0: (gel 0 a) ~> (fst a) -/
def gel0 (a : Term) : Term := Term.gel Dim.zero a  -- represents fst a

/-- gel1: (gel 1 a) ~> (snd a) -/
def gel1 (a : Term) : Term := Term.gel Dim.one a   -- represents snd a

/-- ungel0: (ungel 0 g) ~> ((g .equiv) (g .val)) -/
def ungel0 (g : Term) : Term := Term.ungel Dim.zero g

/-- ungel1: (ungel 1 g) ~> (g .val) -/
def ungel1 (g : Term) : Term := Term.ungel Dim.one g

/-! ## Reducer -/

def reduceGel : Dim → Term → Term
  | Dim.zero, a => gel0 a
  | Dim.one, a => gel1 a
  | i, a => Term.gel i a

def reduceUngel : Dim → Term → Term
  | Dim.zero, g => ungel0 g
  | Dim.one, g => ungel1 g
  | i, g => Term.ungel i g

end Cool.Gel
