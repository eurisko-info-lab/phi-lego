/-
  Lego.Red.Glue: Glue Types for Univalence

  Glue types are a fundamental construct in cubical type theory that enable univalence.
  They allow "gluing" a type A along a cofibration φ with an equivalent type T.

  Mathematical Structure:
  - Glue A φ T e : Type when A : Type, φ : Cof, T : [φ] → Type, e : [φ] (x:T) → Equiv (T x) A
  - When φ = ⊥: Glue A ⊥ T e ≡ A
  - When φ = ⊤: Glue A ⊤ T e ≡ T

  Relationship to V-types:
  - V r A B e ≡ Glue B (r=0) (λ_. A) (λ_. e)  (when r=0)
  - V-types are a special case with φ being dimension equality

  Key operations:
  - glue t a : Glue A φ T e  (introduction)
  - unglue g : A              (elimination)
  - Kan structure: coe and hcom for Glue types

  Based on CCHM and cooltt's Glue implementation.
-/

import Lego.Red.Core
import Lego.Red.Cofibration
import Lego.Red.Kan

namespace Lego.Red.Glue

open Lego.Core
open Lego.Core.Expr
open Lego.Red.Kan
open Lego.Red.Cofibration

/-! ## Glue Type Information

    A Glue type `Glue A φ T e` has:
    - base : A (the base type)
    - cof  : φ (cofibration where gluing happens)
    - top  : T (type to glue when φ holds)
    - equiv : e (equivalence between T and A when φ holds)
-/

/-- Information about a Glue type -/
structure GlueInfo where
  base : Expr      -- A : Type (base type)
  cof : Expr       -- φ : Cof (cofibration)
  top : Expr       -- T : [φ] → Type (partial type)
  equiv : Expr     -- e : [φ] (x:T) → Equiv (T x) A
  deriving Repr, BEq

namespace GlueInfo

/-- Create GlueInfo from a glue type expression -/
def fromExpr? : Expr → Option GlueInfo
  | .glue a phi t e => some ⟨a, phi, t, e⟩
  | _ => none

/-- Convert back to an Expr -/
def toExpr (info : GlueInfo) : Expr :=
  .glue info.base info.cof info.top info.equiv

/-- Check if cofibration is definitely true -/
def cofIsTop (info : GlueInfo) : Bool :=
  Cofibration.isTop info.cof

/-- Check if cofibration is definitely false -/
def cofIsBot (info : GlueInfo) : Bool :=
  Cofibration.isBot info.cof

/-- Reduce Glue type when cofibration is trivial -/
def reduce (info : GlueInfo) : Option Expr :=
  if info.cofIsBot then
    -- Glue A ⊥ T e ≡ A
    some info.base
  else if info.cofIsTop then
    -- Glue A ⊤ T e ≡ T (fully glued)
    some info.top
  else
    none

end GlueInfo

/-! ## Glue Element Information

    A glue element `glueElem t a` contains:
    - partial : t (the partial element for T when φ)
    - base : a (the base element of A)
-/

/-- Information about a glue introduction term -/
structure GlueElemInfo where
  partial_ : Expr   -- t : [φ] → T
  base : Expr       -- a : A
  deriving Repr, BEq

namespace GlueElemInfo

/-- Create from expression -/
def fromExpr? : Expr → Option GlueElemInfo
  | .glueElem t a => some ⟨t, a⟩
  | _ => none

/-- Convert to expression -/
def toExpr (info : GlueElemInfo) : Expr :=
  .glueElem info.partial_ info.base

end GlueElemInfo

/-! ## Smart Constructors

    Build Glue types and elements with simplification.
-/

/-- Create a Glue type with reduction -/
def mkGlue (base cof top equiv : Expr) : Expr :=
  let info : GlueInfo := ⟨base, cof, top, equiv⟩
  match info.reduce with
  | some reduced => reduced
  | none => info.toExpr

/-- Create a glue element -/
def mkGlueElem (partial_ base : Expr) : Expr :=
  .glueElem partial_ base

/-- Create an unglue elimination -/
def mkUnglue (g : Expr) : Expr :=
  .unglue g

/-! ## Kan Operations for Glue Types

    Glue types have Kan structure derived from the base type A and the equivalence.
-/

/-- Coercion in Glue types

    coe r r' (λi. Glue A[i] φ[i] T[i] e[i]) g

    The key insight: use the equivalence to transport along both the base and glued parts.
-/
def coeGlue (r r' : Expr) (info : GlueInfo) (g : Expr) : Expr :=
  -- Simplified implementation: extract base and coerce it
  -- Full implementation would handle the equivalence properly
  let baseCoerced := Expr.coe info.base r r' (mkUnglue g)
  baseCoerced

/-- Homogeneous composition in Glue types

    hcom r r' (Glue A φ T e) [ψ → tube] cap

    Compose using the base type's hcom and adjust with equivalence.
-/
def hcomGlue (r r' : Expr) (info : GlueInfo) (cof : Expr) (tube : Expr) (cap : Expr) : Expr :=
  -- Simplified: hcom in base type
  let baseHcom := Expr.hcom r r' info.base cof (mkUnglue cap)
  baseHcom

/-! ## Type Checking Support

    Helpers for type-checking Glue types and operations.
-/

/-- Check that a term is a valid Glue type -/
def isGlueType (e : Expr) : Bool :=
  match GlueInfo.fromExpr? e with
  | some _ => true
  | none => false

/-- Check that a term is a glue element -/
def isGlueElem (e : Expr) : Bool :=
  match GlueElemInfo.fromExpr? e with
  | some _ => true
  | none => false

/-- Extract the base type from a Glue type -/
def getBaseType (e : Expr) : Option Expr :=
  (GlueInfo.fromExpr? e).map (·.base)

/-- Extract the gluing cofibration -/
def getCofibration (e : Expr) : Option Expr :=
  (GlueInfo.fromExpr? e).map (·.cof)

/-! ## Univalence via Glue

    The key use of Glue types is constructing paths between equivalent types.

    ua : Equiv A B → Path Type A B
    ua e = λi. Glue B (i=0) (λ_. A) (λ_. e)

    At i=0: Glue B ⊤ A e ≡ A (via equivalence)
    At i=1: Glue B ⊥ A e ≡ B
-/

/-- Construct a path between types from an equivalence (univalence) -/
def ua (tyA tyB equiv : Expr) : Expr :=
  -- λi. Glue B (i=0) (λ_. A) (λ_. e)
  let dimVar := dimVar 0
  let cof := Cofibration.eq dimVar dim0
  let glueType := mkGlue tyB cof tyA equiv
  Expr.plam glueType

/-- Transport along ua: transport (ua e) ≡ e.fst -/
def uaTransport (equiv a : Expr) : Expr :=
  -- Applying the equivalence function to a
  Expr.app (Expr.fst equiv) a

/-! ## Evaluation Support

    Normalize Glue types when possible.
-/

/-- Reduce a Glue type expression if possible -/
def reduceGlue (e : Expr) : Expr :=
  match GlueInfo.fromExpr? e with
  | some info =>
    match info.reduce with
    | some reduced => reduced
    | none => e
  | none => e

/-- Reduce a glue element when cofibration is known -/
def reduceGlueElem (cof partial_ base : Expr) : Expr :=
  if Cofibration.isTop cof then
    partial_  -- When φ = ⊤, glue t a reduces to t
  else if Cofibration.isBot cof then
    base     -- When φ = ⊥, glue t a reduces to a
  else
    mkGlueElem partial_ base

/-- Reduce an unglue when we know the argument -/
def reduceUnglue (g : Expr) : Expr :=
  match GlueElemInfo.fromExpr? g with
  | some info => info.base  -- unglue (glue t a) ≡ a
  | none => mkUnglue g

/-! ## Strict Glue (for better computational behavior)

    Strict Glue types are definitionally equal to the base when cofibration is false.
    This is important for computational univalence.
-/

/-- Strictly reduce Glue type (for computation) -/
def strictReduceGlue (info : GlueInfo) : Expr :=
  match info.reduce with
  | some reduced => reduced
  | none => info.toExpr

end Lego.Red.Glue
