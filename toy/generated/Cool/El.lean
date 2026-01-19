/-
  Cool.El - Universe decoding: El A
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.El

/-! ## Syntax -/

/-- El and code operations -/
inductive Term : Type where
  | El (a : Term) : Term
  | code (A : Term) : Term
  | var (name : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- ElCode: (El (code A)) ~> A -/
def ElCode (A : Term) : Term := A

/-! ## Typing Rules (axiomatized) -/

axiom ElForm : True

/-! ## Reducer -/

def reduce : Term → Term
  | Term.El (Term.code A) => A
  | t => t

/-! ## Tests -/

example : reduce (Term.El (Term.code (Term.var "A"))) = Term.var "A" := rfl

end Cool.El
