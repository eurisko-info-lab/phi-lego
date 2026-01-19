/-
  Cool.El - Universe decoding: El A
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.El

/-! ## Syntax -/

/-- El and code operations -/
inductive Term
  | El (a : Term) : Term
  | code (A : Term) : Term

/-! ## Reduction Rules -/

/-- ElCode: (El (code A)) ~> A -/
def ElCode (A : Term) : Term := A

/-! ## Typing Rules -/

/-- ElForm: (El a) : U when a : U -/
structure ElForm where
  a : Term
  a_type : True  -- placeholder for a : U

/-! ## Reducer -/

def reduce : Term → Term
  | Term.El (Term.code A) => A
  | t => t

/-! ## Tests -/

example : reduce (Term.El (Term.code (Term.El Term.code))) =
          Term.El Term.code := rfl

end Cool.El
