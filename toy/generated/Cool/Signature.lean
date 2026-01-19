/-
  Cool.Signature - Signatures (record types)
  Generated from Cool.lego via Rosetta pipeline
-/

namespace Cool.Signature

/-! ## Syntax -/

/-- Generic term placeholder -/
inductive Term : Type where
  | var (name : String) : Term
  | sig (fields : List (String × Term)) : Term
  | struct (assigns : List (String × Term)) : Term
  | proj (t : Term) (field : String) : Term
  deriving Repr

/-! ## Reduction Rules -/

/-- projStruct: ((struct { x := a rest }) . x) ~> a -/
def projStruct (assigns : List (String × Term)) (x : String) : Option Term :=
  assigns.find? (fun (name, _) => name == x) |>.map (·.2)

/-! ## Typing Rules (axiomatized) -/

axiom sigForm : True

/-! ## Reducer -/

def reduce : Term → Term
  | Term.proj (Term.struct assigns) x =>
    match projStruct assigns x with
    | some v => v
    | none => Term.proj (Term.struct assigns) x
  | t => t

/-! ## Tests -/

example : projStruct [("x", Term.var "a")] "x" = some (Term.var "a") := rfl

end Cool.Signature
