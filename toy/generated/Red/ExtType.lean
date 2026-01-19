/-
  Red.ExtType - Extension types
  Generated from Red.lego via Rosetta pipeline
-/

namespace Red.ExtType

/-! ## Core Types -/

/-- Dimension type (interval element) -/
inductive Dim where
  | zero : Dim
  | one : Dim
  | var (name : String) : Dim
  deriving Repr, BEq

/-- Cofibration type -/
inductive Cof where
  | top : Cof
  | bot : Cof
  | eq (i j : Dim) : Cof
  deriving Repr, BEq

/-! ## Syntax -/

/-- Extension type terms -/
inductive Term : Type where
  | Ext (x : String) (A : Term) (sys : List (Cof × Term)) : Term
  | extLam (x : String) (body : Term) : Term
  | extApp (t : Term) (r : Dim) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Substitution -/

/-- Substitute dimension for variable in term -/
partial def substDim (x : String) (r : Dim) : Term → Term
  | Term.Ext y A sys =>
    Term.Ext y (substDim x r A) (sys.map fun (c, t) => (c, substDim x r t))
  | Term.extLam y body =>
    if y == x then Term.extLam y body else Term.extLam y (substDim x r body)
  | Term.extApp t r' => Term.extApp (substDim x r t) r'
  | Term.var name => Term.var name

/-! ## Reduction Rules -/

/-- extBeta: (extApp (extLam x . body) r) ~> [x := r] body -/
def extBeta (x : String) (body : Term) (r : Dim) : Term :=
  substDim x r body

/-! ## Reducer -/

/-- Single-step reduction -/
def reduce : Term → Term
  | Term.extApp (Term.extLam x body) r => extBeta x body r
  | t => t

/-! ## Tests -/

-- Note: Tests require custom equality due to recursive types
#check reduce (Term.extApp (Term.extLam "i" (Term.var "f")) Dim.zero)

end Red.ExtType
