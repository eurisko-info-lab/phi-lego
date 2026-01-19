/-
  Red.Restrict - Restriction types
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.Restrict

/-! ## Core Types -/

inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

inductive Cof where
  | top : Cof
  | bot : Cof
  | eq (i j : Dim) : Cof
  deriving Repr, BEq

/-! ## Syntax -/

/-- Restriction type terms -/
inductive Term : Type where
  | restrict (A : Term) (φ : Cof) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Typing Rules -/

/-- restrictForm: (A ↾ φ) : U when A : U
    This is a typing judgment, represented as a structure -/
structure RestrictForm where
  A : Term
  φ : Cof
  deriving Repr

end Red.Restrict
