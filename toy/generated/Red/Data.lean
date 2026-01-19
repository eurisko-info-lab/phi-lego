/-
  Red.Data - User-defined data types (HITs)
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.Data

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

/-! ## Term Syntax -/

/-- Generic term type -/
inductive Term : Type where
  | var (name : String) : Term
  | app (f : Term) (args : List Term) : Term
  | intro (constr : String) (args : List Term) : Term
  | elim (scrutinee : Term) (motive : Term) (branches : List (String × Term)) : Term
  deriving Repr

/-! ## Data Type Declarations -/

/-- Parameter declaration -/
structure Param where
  name : String
  tp : Term
  deriving Repr

/-- Boundary specification for HITs -/
structure Bound where
  cof : Cof
  tm : Term
  deriving Repr

/-- Constructor declaration -/
structure Constr where
  name : String
  tp : Term
  bounds : List Bound := []
  deriving Repr

/-- Data type declaration -/
structure DataDecl where
  name : String
  params : List Param
  constrs : List Constr
  deriving Repr

/-! ## Reduction Rules -/

/-- introElim: (elim (intro c as) motive branches) ~> (branches[c] as) -/
def introElim (c : String) (_args : List Term) (branches : List (String × Term)) : Option Term :=
  branches.find? (fun (name, _) => name == c) |>.map (·.2)

/-! ## Reducer -/

def reduce : Term → Term
  | Term.elim (Term.intro c args) motive branches =>
    match introElim c args branches with
    | some t => t
    | none => Term.elim (Term.intro c args) motive branches
  | t => t

end Red.Data
