/-
  Lego.Cubical.Core - Re-exports for generated code
  
  Provides the core types needed by generated Red and Cool modules.
-/

-- Re-export the main Core module
import Lego.Cubical.Core as Lego.Core

namespace Lego.Cubical

-- Export commonly used types
export Lego.Core (Level Term Dim Cof)

-- Placeholder types for generated code that need these
-- These should be replaced with actual imports from Core

/-- Dimension type (interval) -/
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
  | join (φ ψ : Cof) : Cof
  | meet (φ ψ : Cof) : Cof
  deriving Repr, BEq

/-- Generic term placeholder -/
inductive Term where
  | var (name : String) : Term
  | app (f : Term) (args : List Term) : Term
  deriving Repr

/-- Universe type -/
def U : Term := Term.var "U"

/-- Substitution placeholder -/
def subst (x : String) (v : α) (body : β) : β := body

/-- Type checking placeholder -/
def hasType (t : Term) (T : Term) : Prop := True

end Lego.Cubical
