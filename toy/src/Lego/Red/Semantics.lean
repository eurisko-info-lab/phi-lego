/-
  Lego.Red.Semantics: Full Evaluation with Kan Operations

  Mathematical Structure:
  - Normalization by evaluation (NbE)
  - Rigid coe/hcom computation
  - Splicing for constructing intermediate terms

  Based on cooltt's Semantics.ml module.

  Key insight from cooltt:
  "The heart of the semantic domain is the handling of 'rigid' Kan operations:
   coe and hcom that cannot reduce further. These must be computed
   according to the specific type constructor (Pi, Sigma, Path, etc.)."
-/

import Lego.Red.Core
import Lego.Red.Cofibration
import Lego.Red.Conversion
import Lego.Red.TermBuilder

namespace Lego.Red.Semantics

open Lego.Core
open Lego.Core.Expr
open Cofibration
open TermBuilder

/-! ## Evaluation Context -/

/-- Evaluation context: variable environment + fuel -/
structure EvalCtx where
  /-- Variable environment (values for bound variables) -/
  env : Array Expr := #[]
  /-- Fuel for normalization (prevents infinite loops) -/
  fuel : Nat := 1000
  deriving Repr

namespace EvalCtx

def empty : EvalCtx := {}

def extend (ctx : EvalCtx) (v : Expr) : EvalCtx :=
  { ctx with env := ctx.env.push v }

def lookup (ctx : EvalCtx) (ix : Nat) : Option Expr :=
  if ix < ctx.env.size then
    ctx.env[ctx.env.size - 1 - ix]?
  else none

def decFuel (ctx : EvalCtx) : EvalCtx :=
  { ctx with fuel := ctx.fuel - 1 }

end EvalCtx

/-! ## Dispatch Result

    When computing rigid coe/hcom, we first dispatch to determine the strategy.
-/

/-- Result of dispatching a rigid operation -/
inductive DispatchResult where
  | done : DispatchResult  -- Cannot reduce (stuck)
  | reduce : DispatchResult  -- Can reduce according to type structure
  deriving Repr, BEq

/-! ## Stable vs Unstable Codes

    Codes are classified as:
    - Stable: Always canonical (Pi, Sigma, Path, Nat, Circle, Univ)
    - Unstable: May need further computation (V, HCom, etc.)
-/

/-- Check if a code is stable -/
def isStableCode : Expr → Bool
  | .pi _ _ => true
  | .sigma _ _ => true
  | .path _ _ _ => true
  | .nat => true
  | .circle => true
  | .univ _ => true
  | .sub _ _ _ => true
  | _ => false

/-- Check if a code is an unstable V type -/
def isVCode : Expr → Bool
  | .v _ _ _ _ => true
  | _ => false

/-- Check if a code is an unstable HCom type -/
def isHComCode : Expr → Bool
  | .hcom _ _ _ _ _ => true
  | _ => false

/-! ## Core Evaluation -/

/-- Evaluate an expression to weak head normal form -/
partial def eval (ctx : EvalCtx) (e : Expr) : Expr :=
  if ctx.fuel == 0 then e else
  let ctx' := ctx.decFuel
  match e with
  -- Variables
  | .ix n =>
    match ctx.lookup n with
    | some v => eval ctx' v
    | none => e

  -- Lambda and application
  | .lam body => e  -- Already in WHNF
  | .app f a =>
    let vf := eval ctx' f
    let va := eval ctx' a
    match vf with
    | .lam body => eval ctx' (subst 0 va body)
    | _ => .app vf va

  -- Pairs and projections
  | .pair a b => .pair (eval ctx' a) (eval ctx' b)
  | .fst p =>
    match eval ctx' p with
    | .pair a _ => eval ctx' a
    | vp => .fst vp
  | .snd p =>
    match eval ctx' p with
    | .pair _ b => eval ctx' b
    | vp => .snd vp

  -- Path types
  | .plam body => e
  | .papp p r =>
    let vp := eval ctx' p
    let vr := eval ctx' r
    match vp with
    | .plam body => eval ctx' (subst 0 vr body)
    | _ => .papp vp vr

  -- Subtypes
  | .subIn t => .subIn (eval ctx' t)
  | .subOut t =>
    match eval ctx' t with
    | .subIn v => eval ctx' v
    | vt => .subOut vt

  -- Natural numbers
  | .zero => e
  | .suc n => .suc (eval ctx' n)

  -- Circle
  | .base => e
  | .loop r => .loop (eval ctx' r)

  -- Dimensions and cofibrations
  | .dim0 => e
  | .dim1 => e
  | .top => e
  | .bot => e
  | .eq r s => .eq (eval ctx' r) (eval ctx' s)
  | .and φ ψ => .and (eval ctx' φ) (eval ctx' ψ)
  | .or φ ψ => .or (eval ctx' φ) (eval ctx' ψ)

  -- Types (already in WHNF)
  | .pi dom cod => .pi (eval ctx' dom) cod  -- Don't eval under binders
  | .sigma a b => .sigma (eval ctx' a) b
  | .path tp l r => .path (eval ctx' tp) (eval ctx' l) (eval ctx' r)
  | .nat => e
  | .circle => e
  | .univ _ => e
  | .sub a φ t => .sub (eval ctx' a) (eval ctx' φ) t

  -- V types
  | .v r a b equiv => .v (eval ctx' r) (eval ctx' a) (eval ctx' b) (eval ctx' equiv)
  | .vIn r p t => .vIn (eval ctx' r) (eval ctx' p) (eval ctx' t)
  | .vProj r v => .vProj (eval ctx' r) (eval ctx' v)

  -- Kan operations
  | .coe line r s t =>
    let vr := eval ctx' r
    let vs := eval ctx' s
    if dimEq vr vs then eval ctx' t
    else doRigidCoe ctx' (eval ctx' line) vr vs (eval ctx' t)

  | .hcom tp r s φ u =>
    let vr := eval ctx' r
    let vs := eval ctx' s
    let vφ := eval ctx' φ
    if dimEq vr vs || cofTrue vφ then
      -- r = s or φ is true: return cap
      eval ctx' (.app (.app u vs) (.lit "prf"))
    else doRigidHCom ctx' (eval ctx' tp) vr vs vφ (eval ctx' u)

  -- Default
  | _ => e

/-! ## Dimension and Cofibration Helpers -/

/-- Check if two dimensions are definitionally equal -/
where
  dimEq (r s : Expr) : Bool :=
    match r, s with
    | .dim0, .dim0 => true
    | .dim1, .dim1 => true
    | .ix n, .ix m => n == m
    | _, _ => false

/-- Check if a cofibration is trivially true -/
  cofTrue (φ : Expr) : Bool :=
    match φ with
    | .top => true
    | .eq r s => dimEq r s
    | .or φ ψ => cofTrue φ || cofTrue ψ
    | _ => false

/-! ## Rigid Coe Computation

    Coercion along a line of types. The key insight is that coe
    reduces differently for each type constructor:
    - Nat, Circle, Univ: Identity (degenerate)
    - Pi: Contravariantly in domain, covariantly in codomain
    - Sigma: Component-wise
    - Path: Squeeze construction
-/

/-- Compute rigid coercion -/
  doRigidCoe (ctx : EvalCtx) (line : Expr) (r s : Expr) (con : Expr) : Expr :=
    if ctx.fuel == 0 then .coe line r s con else
    let ctx' := ctx.decFuel
    -- Dispatch based on the type code at the endpoint
    let code := eval ctx' (.app line s)
    match code with
    -- Degenerate cases: no coercion needed
    | .nat => con
    | .circle => con
    | .univ _ => con

    -- Pi type: coe (λi. Π(A i)(B i)) r s f
    --   = λx. coe (λi. B i (coe (λi. A i) s i x)) r s (f (coe (λi. A i) s r x))
    | .pi _ _ =>
      -- Simplified: just wrap in coe for now
      .coe line r s con

    -- Sigma type: coe (λi. Σ(A i)(B i)) r s ⟨a, b⟩
    --   = ⟨coe A r s a, coe (λi. B i (coe A r i a)) r s b⟩
    | .sigma _ _ =>
      .coe line r s con

    -- Path type: coe (λi. Path (A i) (l i) (r i)) r s p
    --   = λj. com A r s (∂j) [j=0 ↦ l, j=1 ↦ r] (p j)
    | .path _ _ _ =>
      .coe line r s con

    -- V type: needs special handling
    | .v vr _ _ _ =>
      .coe line r s con

    -- Default: stuck
    | _ => .coe line r s con

/-! ## Rigid HCom Computation

    Homogeneous composition. Like coe, hcom reduces differently
    for each type constructor.
-/

/-- Compute rigid hcom -/
  doRigidHCom (ctx : EvalCtx) (code : Expr) (r s : Expr) (φ : Expr) (bdy : Expr) : Expr :=
    if ctx.fuel == 0 then .hcom code r s φ bdy else
    let ctx' := ctx.decFuel
    match code with
    -- Pi type: hcom (Π A B) r s φ u = λx. hcom (B x) r s φ (λi p. u i p x)
    | .pi _dom cod =>
      .lam (.hcom cod r s φ
        (.lam (.lam (.app (.app (.app (shift 0 (shift 0 bdy)) (.ix 1)) (.ix 0)) (.ix 2)))))

    -- Sigma type: component-wise
    | .sigma a _b =>
      let fstLine := .lam (.hcom a r (.ix 0) φ
        (.lam (.lam (.fst (.app (.app (shift 0 (shift 0 bdy)) (.ix 1)) (.ix 0))))))
      let fst_s := .app fstLine s
      -- Simplified: just return hcom for now
      .hcom code r s φ bdy

    -- Path type: hcom (Path A l r) = ...
    | .path _ _ _ =>
      .hcom code r s φ bdy

    -- Nat: fhcom (frozen hcom)
    | .nat =>
      .hcom code r s φ bdy

    -- Circle: fhcom
    | .circle =>
      .hcom code r s φ bdy

    -- Universe: hcom in Univ creates an unstable HCom code
    | .univ _ =>
      .hcom code r s φ bdy

    -- V type: hcom-v rule
    | .v _ _ _ _ =>
      .hcom code r s φ bdy

    -- Default: stuck
    | _ => .hcom code r s φ bdy

/-! ## Splicing Operations

    Splicing is used to construct intermediate terms during Kan computations.
    It allows mixing semantic values with syntactic term construction.
-/

/-- Splice context tracking bound variables during construction -/
structure SpliceCtx where
  bindings : Array (String × Expr) := #[]
  level : Nat := 0
  deriving Repr

namespace SpliceCtx

def empty : SpliceCtx := {}

def bind (ctx : SpliceCtx) (name : String) (v : Expr) : SpliceCtx × Expr :=
  let var := .ix ctx.level
  ({ ctx with
     bindings := ctx.bindings.push (name, v),
     level := ctx.level + 1 }, var)

end SpliceCtx

/-- Splice a dimension value into a term -/
def spliceDim (ctx : SpliceCtx) (d : Expr) (k : SpliceCtx → Expr → Expr) : Expr :=
  match d with
  | .dim0 => k ctx .dim0
  | .dim1 => k ctx .dim1
  | _ =>
    let (ctx', var) := ctx.bind "i" d
    k ctx' var

/-- Splice a cofibration value into a term -/
def spliceCof (ctx : SpliceCtx) (φ : Expr) (k : SpliceCtx → Expr → Expr) : Expr :=
  match φ with
  | .top => k ctx .top
  | .bot => k ctx .bot
  | _ =>
    let (ctx', var) := ctx.bind "φ" φ
    k ctx' var

/-- Splice a general value into a term -/
def spliceCon (ctx : SpliceCtx) (con : Expr) (k : SpliceCtx → Expr → Expr) : Expr :=
  let (ctx', var) := ctx.bind "x" con
  k ctx' var

/-! ## Do Operations (Semantic Application, Projection, etc.) -/

/-- Apply a semantic function to an argument -/
def doAp (ctx : EvalCtx) (f : Expr) (a : Expr) : Expr :=
  eval ctx (.app f a)

/-- Apply a function to two arguments -/
def doAp2 (ctx : EvalCtx) (f : Expr) (a b : Expr) : Expr :=
  doAp ctx (doAp ctx f a) b

/-- Take first projection -/
def doFst (ctx : EvalCtx) (p : Expr) : Expr :=
  eval ctx (.fst p)

/-- Take second projection -/
def doSnd (ctx : EvalCtx) (p : Expr) : Expr :=
  eval ctx (.snd p)

/-- Compute path application -/
def doPApp (ctx : EvalCtx) (p : Expr) (r : Expr) : Expr :=
  eval ctx (.papp p r)

/-- Compute sub-out -/
def doSubOut (ctx : EvalCtx) (t : Expr) : Expr :=
  eval ctx (.subOut t)

/-! ## El (Universe Decoding) -/

/-- Decode a universe code to a type -/
def doEl (ctx : EvalCtx) (code : Expr) : Expr :=
  let vcode := eval ctx code
  match vcode with
  | .lit "nat-code" => .nat
  | .lit "circle-code" => .circle
  | _ => vcode  -- Already a type

/-! ## Rigid Cap and VProj -/

/-- Compute cap (extract cap from box or create neutral) -/
def doRigidCap (ctx : EvalCtx) (r s : Expr) (φ : Expr) (code : Expr) (box : Expr) : Expr :=
  let vbox := eval ctx box
  match vbox with
  -- Direct box: extract cap
  | _ => .lit s!"cap({repr r},{repr s},{repr φ},{repr code},{repr vbox})"

/-- Compute vproj (project from V type) -/
def doRigidVProj (ctx : EvalCtx) (r : Expr) (pcode code pequiv : Expr) (v : Expr) : Expr :=
  let vv := eval ctx v
  match vv with
  | .vIn _ _ base => base
  | _ => .vProj r vv

/-! ## Top-level Evaluation -/

/-- Evaluate with default context -/
def evaluate (e : Expr) : Expr :=
  eval EvalCtx.empty e

/-- Evaluate to WHNF -/
def whnf (e : Expr) : Expr :=
  eval EvalCtx.empty e

/-- Evaluate type to WHNF -/
def whnfTp (tp : Expr) : Expr :=
  whnf tp

/-! ## Instantiation Helpers -/

/-- Instantiate a closure with a value -/
def instClo (ctx : EvalCtx) (body : Expr) (v : Expr) : Expr :=
  eval ctx (subst 0 v body)

/-- Instantiate a type closure -/
def instTpClo (ctx : EvalCtx) (body : Expr) (v : Expr) : Expr :=
  instClo ctx body v

end Lego.Red.Semantics
