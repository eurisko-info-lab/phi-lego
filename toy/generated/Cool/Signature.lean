/-
  Cool.Signature - Signatures (record types)
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Signature

/-! ## Syntax -/

/-- Field in a signature -/
structure Field where
  name : String
  tp : Term

/-- Assignment in a struct -/
structure Assign where
  name : String
  val : Term

/-- Signature and struct terms -/
inductive Term
  | sig (fields : List Field) : Term
  | struct (assigns : List Assign) : Term
  | proj (t : Term) (field : String) : Term

/-! ## Reduction Rules -/

/-- projStruct: ((struct { x := a rest }) . x) ~> a -/
def projStruct (assigns : List Assign) (x : String) : Option Term :=
  assigns.find? (fun a => a.name == x) |>.map Assign.val

/-! ## Typing Rules -/

/-- sigForm: (sig { fs }) : U when fs valid -/
structure SigForm where
  fields : List Field
  fields_valid : True  -- placeholder

/-! ## Reducer -/

def reduce : Term → Term
  | Term.proj (Term.struct assigns) x =>
    match projStruct assigns x with
    | some v => v
    | none => Term.proj (Term.struct assigns) x
  | t => t

/-! ## Tests -/

example : projStruct [⟨"x", Term.sig []⟩] "x" = some (Term.sig []) := rfl

end Cool.Signature
