/-
  Lego.Red.Splice: Splicing values into terms under binders

  Mathematical Structure:
  - Splicing is a form of metaprogramming for constructing terms
  - Avoids de Bruijn arithmetic when working with binders
  - Based on cooltt's Splice module design

  Key insight from cooltt:
  "Constructing values in the semantic domain that go underneath binders is
  very difficult! In general you need to be able to form exactly the right
  closure for each binder. An alternative is to create a term in an extended
  context, and then evaluate that in an environment that contains the values
  you want to splice into it."

  This module provides:
  - Foreign value binding: bring semantic values into term context
  - Dimension splicing: splice dimension values
  - Cofibration splicing: splice cofibration values
  - Closure splicing: splice closures as lambda bodies
  - Term building: construct terms with spliced values

  Algebra:
  - Splice is a state monad tracking the environment
  - foreign : Value → (Term → Splice α) → Splice α (continuation-passing)
  - compile : Splice Term → (Env × Term) (extract result)
-/

import Lego.Red.Core
import Lego.Red.Cofibration

namespace Lego.Red.Splice

open Lego.Core
open Lego.Core.Expr
open Cofibration

/-! ## Splice Environment

    Tracks values that have been spliced into the term context.
-/

/-- Environment for splice operations -/
structure SpliceEnv where
  /-- Spliced term-level values (conenv in cooltt) -/
  conEnv : List Expr
  /-- Spliced type-level values (tpenv in cooltt) -/
  tpEnv : List Expr
  deriving Repr, BEq

namespace SpliceEnv

/-- Empty splice environment -/
def empty : SpliceEnv := { conEnv := [], tpEnv := [] }

/-- Add a term-level value to environment -/
def addCon (env : SpliceEnv) (e : Expr) : SpliceEnv :=
  { env with conEnv := e :: env.conEnv }

/-- Add a type-level value to environment -/
def addTp (env : SpliceEnv) (e : Expr) : SpliceEnv :=
  { env with tpEnv := e :: env.tpEnv }

/-- Get the current term-level de Bruijn level -/
def conLevel (env : SpliceEnv) : Nat := env.conEnv.length

/-- Get the current type-level de Bruijn level -/
def tpLevel (env : SpliceEnv) : Nat := env.tpEnv.length

end SpliceEnv

/-! ## Splice Monad

    A state monad for building terms with spliced values.
-/

/-- Splice computation -/
abbrev Splice (α : Type) := SpliceEnv → α × SpliceEnv

namespace Splice

/-- Run a splice computation starting from empty environment -/
def run (s : Splice α) : α × SpliceEnv := s SpliceEnv.empty

/-- Get the result, discarding the environment -/
def eval (s : Splice α) : α := (run s).1

/-- Get the environment only -/
def getEnv (s : Splice α) : SpliceEnv := (run s).2

instance : Monad Splice where
  pure a := fun env => (a, env)
  bind m f := fun env =>
    let (a, env') := m env
    f a env'

instance : MonadState SpliceEnv Splice where
  get := fun env => (env, env)
  set newEnv := fun _ => ((), newEnv)
  modifyGet f := fun env => f env

/-- Lift a pure value into Splice -/
def pure (a : α) : Splice α := fun env => (a, env)

/-- Read the current environment -/
def read : Splice SpliceEnv := fun env => (env, env)

end Splice

/-! ## Foreign Value Binding

    Bring semantic values into term context as de Bruijn variables.
-/

/-- Splice a term-level value, returning a variable that refers to it -/
def foreign (con : Expr) (k : Expr → Splice α) : Splice α := fun env =>
  let lvl := env.conEnv.length
  let env' := env.addCon con
  -- Create a variable at the current level
  let var := ix lvl
  k var env'

/-- Splice multiple term-level values -/
def foreignList (cons : List Expr) (k : List Expr → Splice α) : Splice α :=
  match cons with
  | [] => k []
  | con :: rest =>
    foreign con fun v =>
    foreignList rest fun vs =>
    k (v :: vs)

/-- Splice a dimension value -/
def foreignDim (d : Expr) (k : Expr → Splice α) : Splice α :=
  foreign (dimToExpr d) k
where
  dimToExpr : Expr → Expr
    | e => e  -- Dimensions are already expressions

/-- Splice a cofibration value -/
def foreignCof (φ : Expr) (k : Expr → Splice α) : Splice α :=
  -- Cofibrations are represented as expressions directly
  foreign φ k

/-- Splice a closure as a lambda body -/
def foreignClo (clo : Expr) (k : Expr → Splice α) : Splice α :=
  -- Wrap the closure body in a lambda
  foreign (lam clo) k

/-- Splice a type-level value -/
def foreignTp (tp : Expr) (k : Expr → Splice α) : Splice α := fun env =>
  let lvl := env.tpEnv.length
  let env' := env.addTp tp
  -- Create a type variable at the current level
  let var := ix lvl  -- Could distinguish type vars if needed
  k var env'

/-! ## Term Building

    Helper functions for building terms with spliced values.
-/

/-- Build a term directly in splice context -/
def term (m : Expr) : Splice Expr := Splice.pure m

/-- Build a lambda abstraction -/
def mkLam (body : Expr → Splice Expr) : Splice Expr := fun env =>
  let lvl := env.conEnv.length
  let (bodyExpr, env') := body (ix lvl) env
  (lam bodyExpr, env')

/-- Build a path lambda -/
def mkPlam (body : Expr → Splice Expr) : Splice Expr := fun env =>
  let lvl := env.conEnv.length
  let (bodyExpr, env') := body (dimVar lvl) env
  (plam bodyExpr, env')

/-- Build a pi type -/
def mkPi (domain : Expr) (body : Expr → Splice Expr) : Splice Expr := fun env =>
  let lvl := env.conEnv.length
  let env' := env.addCon (ix lvl)
  let (codomainExpr, env'') := body (ix lvl) env'
  (pi domain codomainExpr, env'')

/-- Build a sigma type -/
def mkSigma (base : Expr) (body : Expr → Splice Expr) : Splice Expr := fun env =>
  let lvl := env.conEnv.length
  let env' := env.addCon (ix lvl)
  let (familyExpr, env'') := body (ix lvl) env'
  (sigma base familyExpr, env'')

/-- Build an application -/
def mkApp (fn : Expr) (arg : Expr) : Splice Expr :=
  Splice.pure (app fn arg)

/-- Build multiple applications -/
def mkApps (fn : Expr) (args : List Expr) : Splice Expr :=
  Splice.pure (args.foldl app fn)

/-- Build a path application -/
def mkPapp (p : Expr) (r : Expr) : Splice Expr :=
  Splice.pure (papp p r)

/-! ## Cofibration Split Building -/

/-- Build a cofibration split (case analysis) -/
def mkCofSplit (branches : List (Expr × Expr)) : Splice Expr :=
  Splice.pure (sys branches)

/-- Helper for building split with two branches -/
def mkSplit2 (φ₁ : Expr) (e₁ : Expr) (φ₂ : Expr) (e₂ : Expr) : Splice Expr :=
  mkCofSplit [(φ₁, e₁), (φ₂, e₂)]

/-! ## Compile Splice to Term

    Extract the final term and environment.
-/

/-- Compile a splice computation -/
def compile (s : Splice Expr) : SpliceEnv × Expr :=
  let (term, env) := s SpliceEnv.empty
  (env, term)

/-- Extract just the term -/
def compileToTerm (s : Splice Expr) : Expr := (compile s).2

/-! ## Convenient Namespace for Foreign Operations

    Matches cooltt's Splice.F module.
-/

namespace F

def con {α : Type} := @foreign α
def tp {α : Type} := @foreignTp α
def cons {α : Type} := @foreignList α
def dim {α : Type} := @foreignDim α
def cof {α : Type} := @foreignCof α
def clo {α : Type} := @foreignClo α

end F

/-! ## Macros for Common Patterns

    Matches cooltt's Splice.Macro module.
-/

namespace Macro

/-- Build cap boundary: [r=r' → box; φ → coe code r' r box] -/
def cap (r r' : Expr) (φ : Expr) (code : Expr) (boxExpr : Expr) : Splice Expr :=
  term <|
    sys [
      (CofBuilder.eq r r', boxExpr),
      (φ, coe code r' r boxExpr)
    ]

/-- Build vproj boundary: [r=0 → fwd pequiv v; r=1 → v] -/
def vproj (r : Expr) (pcode code pequiv v : Expr) : Splice Expr :=
  term <|
    sys [
      (CofBuilder.eq r dim0, app (app pequiv (lit "prf")) v),
      (CofBuilder.eq r dim1, v)
    ]

/-- Build vin boundary: [r=0 → pivot prf; r=1 → base] -/
def vin (r : Expr) (pivot baseExpr : Expr) : Splice Expr :=
  term <|
    sys [
      (CofBuilder.eq r dim0, app pivot (lit "prf")),
      (CofBuilder.eq r dim1, baseExpr)
    ]

/-- Build commuting split: distribute action over split branches -/
def commuteSplit (self : Expr) (phis : List Expr)
    (action : Expr → Expr) : Splice Expr :=
  let branches := phis.map fun φ =>
    (φ, action (app self (lit "prf")))
  mkCofSplit branches

end Macro

/-! ## Boundary Splicing

    Matches cooltt's Splice.Bdry module for boundary operations.
-/

namespace Bdry

/-- Compute boundary cofibration for cap operation -/
def capBdry (r r' : Expr) (φ : Expr) : Expr :=
  CofBuilder.joinAll [CofBuilder.eq r r', φ]

/-- Compute boundary for vproj -/
def vprojBdry (r : Expr) : Expr :=
  CofBuilder.boundary r

/-- Compute boundary for vin -/
def vinBdry (r : Expr) : Expr :=
  CofBuilder.boundary r

end Bdry

/-! ## Evaluation with Spliced Environment

    Evaluate a term in an environment extended with spliced values.
-/

/-- Build evaluation environment from splice env -/
def buildEvalEnv (senv : SpliceEnv) : List Expr :=
  senv.conEnv.reverse

/-- Substitute spliced values into a term -/
partial def substSpliced (env : List Expr) (e : Expr) : Expr :=
  match e with
  | .ix n =>
    if h : n < env.length then env[n]'h else e
  | .app f a => app (substSpliced env f) (substSpliced env a)
  | .lam b => lam (substSpliced (ix 0 :: env.map shift) b)
  | .pi d c => pi (substSpliced env d) (substSpliced (ix 0 :: env.map shift) c)
  | .sigma b f => sigma (substSpliced env b) (substSpliced (ix 0 :: env.map shift) f)
  | .pair a b => pair (substSpliced env a) (substSpliced env b)
  | .fst p => fst (substSpliced env p)
  | .snd p => snd (substSpliced env p)
  | .plam b => plam (substSpliced env b)
  | .papp p r => papp (substSpliced env p) (substSpliced env r)
  | .coe a s t p => coe (substSpliced env a) (substSpliced env s) (substSpliced env t) (substSpliced env p)
  | .hcom r r' ty φ cap => hcom (substSpliced env r) (substSpliced env r') (substSpliced env ty)
                                (substSpliced env φ) (substSpliced env cap)
  | .sys branches => sys (branches.map fun (φ, e) => (substSpliced env φ, substSpliced env e))
  | .sub a φ u => sub (substSpliced env a) (substSpliced env φ) (substSpliced env u)
  | .subIn e => subIn (substSpliced env e)
  | .subOut e => subOut (substSpliced env e)
  | .glue a φ t equiv => glue (substSpliced env a) (substSpliced env φ) (substSpliced env t) (substSpliced env equiv)
  | .glueElem t a => glueElem (substSpliced env t) (substSpliced env a)
  | .unglue e => unglue (substSpliced env e)
  | .cof_and a b => cof_and (substSpliced env a) (substSpliced env b)
  | .cof_or a b => cof_or (substSpliced env a) (substSpliced env b)
  | .cof_eq a b => cof_eq (substSpliced env a) (substSpliced env b)
  | _ => e
where
  shift : Expr → Expr
    | .ix n => ix (n + 1)
    | e => e

/-- Splice and evaluate: compile splice then substitute -/
def spliceAndEval (s : Splice Expr) : Expr :=
  let (env, term) := compile s
  let evalEnv := buildEvalEnv env
  substSpliced evalEnv term

end Lego.Red.Splice
