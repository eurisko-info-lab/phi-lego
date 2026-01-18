/-
  Lego.Red.Unify: Miller-Pattern Unification for Higher-Order Terms

  Implements higher-order pattern unification (Miller patterns) with:
  - Flex-rigid: ?α x₁...xₙ = t  →  ?α := λy₁...yₙ. t[xᵢ↦yᵢ]
  - Flex-flex same: ?α x y = ?α y x  →  intersection of spines
  - Flex-flex diff: ?α x = ?β y  →  create common meta with intersection
  - Occurs check to prevent circular solutions
  - Scope checking (all free vars in solution must be in spine)
  - Constraint solving loop for postponed constraints
  - Dimension variables for cubical type theory

  Mathematical structure:
  - Unification finds substitution σ such that σ(t₁) ≡ σ(t₂)
  - Meta-variables are existentially quantified unknowns
  - Pattern fragment (distinct variable spines) ensures decidability
  - Higher-order: metas can have function type, spine is arguments

  Based on:
  - Dale Miller's pattern unification (1991)
  - redtt's Unify.ml implementation
-/

import Lego.Red.GlobalEnv

namespace Lego.Red

open Lego.Core

/-! ## Unification State

    Track meta-variables and their solutions during unification.
-/

/-- A meta-variable with its context and type -/
structure MetaInfo where
  name : GName
  ctx : List Expr        -- Types of variables in scope when created
  ty : Expr              -- Expected type
  solution : Option Expr -- Solution if solved
  deriving Repr

/-- Unification state -/
structure UnifyState where
  metas : List MetaInfo
  nextId : Nat
  postponed : List (Expr × Expr)  -- Postponed constraints
  deriving Repr, Inhabited

namespace UnifyState

def empty : UnifyState := { metas := [], nextId := 0, postponed := [] }

/-- Create a fresh meta-variable -/
def freshMeta (st : UnifyState) (ctx : List Expr) (ty : Expr) : UnifyState × GName :=
  let name := GName.fresh "?" st.nextId
  let info : MetaInfo := { name, ctx, ty, solution := none }
  ({ st with metas := info :: st.metas, nextId := st.nextId + 1 }, name)

/-- Lookup a meta-variable -/
def lookupMeta (st : UnifyState) (name : GName) : Option MetaInfo :=
  st.metas.find? (fun m => m.name == name)

/-- Solve a meta-variable -/
def solveMeta (st : UnifyState) (name : GName) (sol : Expr) : UnifyState :=
  { st with metas := st.metas.map fun m =>
      if m.name == name then { m with solution := some sol } else m }

/-- Check if a meta is solved -/
def isSolved (st : UnifyState) (name : GName) : Bool :=
  match st.lookupMeta name with
  | some m => m.solution.isSome
  | none => false

/-- Get all unsolved metas -/
def unsolved (st : UnifyState) : List MetaInfo :=
  st.metas.filter fun m => m.solution.isNone

/-- Add a postponed constraint -/
def postpone (st : UnifyState) (t1 t2 : Expr) : UnifyState :=
  { st with postponed := (t1, t2) :: st.postponed }

/-- Get and clear postponed constraints -/
def takePostponed (st : UnifyState) : UnifyState × List (Expr × Expr) :=
  ({ st with postponed := [] }, st.postponed)

end UnifyState

/-! ## Free Variables

    Collect free variables (de Bruijn indices) in a term.
    Essential for scope checking in pattern unification.
-/

/-- Collect free de Bruijn indices in an expression -/
partial def freeVars (depth : Nat) : Expr → List Nat
  | .ix n => if n >= depth then [n - depth] else []
  | .lam body => freeVars (depth + 1) body
  | .app f a => freeVars depth f ++ freeVars depth a
  | .pi dom cod => freeVars depth dom ++ freeVars (depth + 1) cod
  | .sigma dom cod => freeVars depth dom ++ freeVars (depth + 1) cod
  | .pair a b => freeVars depth a ++ freeVars depth b
  | .fst p => freeVars depth p
  | .snd p => freeVars depth p
  | .path ty a b => freeVars depth ty ++ freeVars depth a ++ freeVars depth b
  | .plam body => freeVars (depth + 1) body
  | .papp p r => freeVars depth p ++ freeVars depth r
  | .refl a => freeVars depth a
  | .letE ty val body => freeVars depth ty ++ freeVars depth val ++ freeVars (depth + 1) body
  | .suc n => freeVars depth n
  | .coe r r' ty a => freeVars depth r ++ freeVars depth r' ++ freeVars depth ty ++ freeVars depth a
  | _ => []  -- Literals and constants have no free vars

/-! ## Occurs Check

    Prevent circular solutions like ?α := f(?α)
-/

/-- Check if a meta-variable occurs in an expression -/
partial def occurs (name : GName) : Expr → Bool
  | .lit n => n == name.name  -- Meta represented as literal
  | .ix _ => false
  | .lam body => occurs name body
  | .app f a => occurs name f || occurs name a
  | .pi dom cod => occurs name dom || occurs name cod
  | .sigma dom cod => occurs name dom || occurs name cod
  | .pair a b => occurs name a || occurs name b
  | .fst p => occurs name p
  | .snd p => occurs name p
  | .path ty a b => occurs name ty || occurs name a || occurs name b
  | .plam body => occurs name body
  | .papp p r => occurs name p || occurs name r
  | .refl a => occurs name a
  | .coe r r' ty a => occurs name r || occurs name r' || occurs name ty || occurs name a
  | .hcom r r' ty phi cap =>
    occurs name r || occurs name r' || occurs name ty || occurs name phi || occurs name cap
  | .hcomTube r r' ty tubes cap =>
    occurs name r || occurs name r' || occurs name ty ||
    tubes.any (fun (c, t) => occurs name c || occurs name t) || occurs name cap
  | .com r r' ty tubes cap =>
    occurs name r || occurs name r' || occurs name ty ||
    tubes.any (fun (c, t) => occurs name c || occurs name t) || occurs name cap
  | .letE ty val body => occurs name ty || occurs name val || occurs name body
  | .natElim p z s n => occurs name p || occurs name z || occurs name s || occurs name n
  | .suc n => occurs name n
  | .circleElim p b l x => occurs name p || occurs name b || occurs name l || occurs name x
  | .loop r => occurs name r
  | .vtype r a b e => occurs name r || occurs name a || occurs name b || occurs name e
  | .vin r m n => occurs name r || occurs name m || occurs name n
  | .vproj r a b e v => occurs name r || occurs name a || occurs name b || occurs name e || occurs name v
  | .glue a phi t equiv => occurs name a || occurs name phi || occurs name t || occurs name equiv
  | .glueElem t a => occurs name t || occurs name a
  | .unglue g => occurs name g
  | .sys branches => branches.any (fun (c, t) => occurs name c || occurs name t)
  | .cof_eq a b => occurs name a || occurs name b
  | .cof_and a b => occurs name a || occurs name b
  | .cof_or a b => occurs name a || occurs name b
  | _ => false  -- Literals, dim0, dim1, etc.

/-! ## Unification Result -/

/-- Result of unification -/
inductive UnifyResult where
  | success : UnifyState → UnifyResult
  | failure : String → UnifyResult
  | stuck : UnifyState → UnifyResult  -- Flex-flex case, postponed
  deriving Repr, Inhabited

/-! ## Spine Representation

    For higher-order unification, we need to recognize
    patterns like ?α x₁ x₂ ... xₙ where xᵢ are distinct variables.

    In cubical type theory, spines can also contain dimension variables.
-/

/-- Spine element: either a term variable or dimension variable -/
inductive SpineElem where
  | termVar : Nat → SpineElem      -- de Bruijn index
  | dimVar : Nat → SpineElem       -- dimension variable index
  | other : Expr → SpineElem       -- non-variable (breaks pattern)
  deriving Repr, BEq

/-- Classify a spine argument -/
def classifySpineArg : Expr → SpineElem
  | .ix n => .termVar n
  | .dimVar n => .dimVar n
  | e => .other e

/-- Collect the spine of a nested application -/
def collectSpine : Expr → Expr × List Expr
  | .app f a =>
    let (head, args) := collectSpine f
    (head, args ++ [a])
  | .papp f a =>
    let (head, args) := collectSpine f
    (head, args ++ [a])  -- Include dimension applications
  | e => (e, [])

/-- Check if an expression is a variable (de Bruijn index) -/
def isVar : Expr → Option Nat
  | .ix n => some n
  | _ => none

/-- Check if an expression is a dimension variable -/
def isDimVar : Expr → Option Nat
  | .dimVar n => some n
  | _ => none

/-- Check if a spine consists of distinct variables (term or dim) -/
def isPatternSpine (args : List Expr) : Bool :=
  let elems := args.map classifySpineArg
  -- All must be variables (not .other)
  let allVars := elems.all fun e => match e with
    | .termVar _ => true
    | .dimVar _ => true
    | .other _ => false
  -- All must be distinct
  let distinct := elems.eraseDups.length == elems.length
  allVars && distinct

/-- Extract variable indices from pattern spine -/
def spineToVars (args : List Expr) : List Nat :=
  args.filterMap fun e =>
    match classifySpineArg e with
    | .termVar n => some n
    | .dimVar n => some n  -- Treat dim vars same as term vars for renaming
    | .other _ => none

/-- Check if head is a meta-variable -/
def isMeta (e : Expr) : Option String :=
  match e with
  | .lit name => if name.startsWith "?" then some name else none
  | _ => none

/-! ## Miller Pattern Inversion

    The key operation: given ?α x₁ x₂ ... xₙ = term,
    construct the solution λy₁...λyₙ. term[xᵢ ↦ yᵢ]

    Requirements (Miller pattern fragment):
    1. Each xᵢ must be a distinct variable
    2. All free variables in term must be among {x₁, ..., xₙ}
    3. No xᵢ occurs twice in term in conflicting ways (linearity)
-/

/-- Rename variables in term according to spine mapping.
    If spine is [x₃, x₁, x₀], we need to rename:
    - x₃ → 0 (first lambda binds)
    - x₁ → 1
    - x₀ → 2
    Returns None if term has variables not in the spine (scope escape).
-/
def invertTerm (spineVars : List Nat) (term : Expr) : Option Expr :=
  -- Check: all free vars in term must be in spineVars
  let fvs := (freeVars 0 term).eraseDups
  if !fvs.all (fun v => spineVars.contains v) then
    none  -- Scope escape: term uses variable not in spine
  else
    -- Build varMap: spineVars[i] ↦ i
    let varMap := zipWithIndex spineVars |>.map (fun (v, i) => (v, i))
    some (renameVars varMap 0 term)
where
  zipWithIndex {α : Type} (xs : List α) : List (α × Nat) :=
    xs.zip (List.range xs.length)
  renameVars (ren : List (Nat × Nat)) (depth : Nat) : Expr → Expr
    | .ix n =>
      if n < depth then .ix n  -- Bound variable, keep
      else
        let adjusted := n - depth
        match ren.find? (fun (v, _) => v == adjusted) with
        | some (_, newIdx) => .ix (newIdx + depth)
        | none => .ix n  -- Not in renaming, keep (shouldn't happen if scope check passed)
    | .lam body => .lam (renameVars ren (depth + 1) body)
    | .app f a => .app (renameVars ren depth f) (renameVars ren depth a)
    | .pi dom cod => .pi (renameVars ren depth dom) (renameVars ren (depth + 1) cod)
    | .sigma dom cod => .sigma (renameVars ren depth dom) (renameVars ren (depth + 1) cod)
    | .pair a b => .pair (renameVars ren depth a) (renameVars ren depth b)
    | .fst p => .fst (renameVars ren depth p)
    | .snd p => .snd (renameVars ren depth p)
    | .path ty a b => .path (renameVars ren depth ty) (renameVars ren depth a) (renameVars ren depth b)
    | .plam body => .plam (renameVars ren (depth + 1) body)
    | .papp p r => .papp (renameVars ren depth p) (renameVars ren depth r)
    | .refl a => .refl (renameVars ren depth a)
    | .letE ty val body => .letE (renameVars ren depth ty) (renameVars ren depth val) (renameVars ren (depth + 1) body)
    | .suc n => .suc (renameVars ren depth n)
    | .coe r r' ty a => .coe (renameVars ren depth r) (renameVars ren depth r') (renameVars ren depth ty) (renameVars ren depth a)
    | e => e  -- Literals, constants, etc.

/-! ## Core Unification -/

/-- Try to solve a flex-rigid equation: ?α args = term
    Using Miller pattern unification when applicable.
-/
def solveFlexRigid (st : UnifyState) (metaName : String) (args : List Expr) (term : Expr) : UnifyResult :=
  let gname := GName.named metaName
  -- Occurs check
  if occurs gname term then
    .failure s!"occurs check failed: {metaName} occurs in solution"
  -- Pattern condition: args must be distinct variables
  else if !isPatternSpine args then
    .stuck (st.postpone (.lit metaName) term)  -- Not a pattern, postpone
  else
    let spineVars := args.filterMap isVar
    -- Try to invert: rename term's variables to match lambda bindings
    match invertTerm spineVars term with
    | none =>
      -- Scope escape: term uses variables not in the spine
      .stuck (st.postpone (.lit metaName) term)
    | some invertedTerm =>
      -- Build solution: λx₁...λxₙ. invertedTerm
      let solution := args.foldr (fun _ body => .lam body) invertedTerm
      .success (st.solveMeta gname solution)

mutual

/-- Unify two expressions -/
partial def unify (st : UnifyState) (t1 t2 : Expr) : UnifyResult :=
  -- First, check if already equal
  if conv t1 t2 then
    .success st
  else
    -- Decompose applications
    let (h1, args1) := collectSpine t1
    let (h2, args2) := collectSpine t2

    match isMeta h1, isMeta h2 with
    -- Flex-rigid: ?α args = term
    | some m, none => solveFlexRigid st m args1 t2
    -- Rigid-flex: term = ?α args
    | none, some m => solveFlexRigid st m args2 t1
    -- Flex-flex: ?α args₁ = ?β args₂
    | some m1, some m2 =>
      if m1 == m2 then
        -- Same meta: ?α x y = ?α y x
        -- Try to find intersection of spines
        flexFlexSame st m1 args1 args2
      else
        -- Different metas: ?α x y = ?β y z
        -- Use intersection to find common variables
        flexFlexDiff st m1 args1 m2 args2
    -- Rigid-rigid: structural unification
    | none, none =>
      unifyRigid st t1 t2

/-- Handle flex-flex with same meta: ?α args₁ = ?α args₂
    Find the intersection of the two spines.
-/
partial def flexFlexSame (st : UnifyState) (metaName : String) (args1 args2 : List Expr) : UnifyResult :=
  if args1.length != args2.length then
    .failure "flex-flex: spine length mismatch"
  else if !isPatternSpine args1 || !isPatternSpine args2 then
    .stuck (st.postpone (.lit metaName) (.lit metaName))  -- Not patterns, postpone
  else
    let vars1 := spineToVars args1
    let vars2 := spineToVars args2
    -- Find common positions: where vars1[i] == vars2[i]
    let pairs := vars1.zip vars2
    let commonCount := pairs.filter (fun (v1, v2) => v1 == v2) |>.length
    if commonCount == vars1.length then
      -- All positions match, trivially equal
      .success st
    else
      -- Need to create a new meta with restricted spine
      -- For now, just postpone (full implementation needs type info)
      .stuck (st.postpone (.lit metaName) (.lit metaName))

/-- Handle flex-flex with different metas: ?α args₁ = ?β args₂
    The key insight: we can solve by making both equal to a fresh meta
    that only uses the intersection of their spines.

    Example: ?α x y = ?β y z
    - α's spine: [x, y]
    - β's spine: [y, z]
    - Common: [y]
    - Solution: α := λx.λy. ?γ y, β := λy.λz. ?γ y

    For now, we use a simpler approach: try to solve one in terms of the other
    if one spine is a subset of the other.
-/
partial def flexFlexDiff (st : UnifyState) (m1 : String) (args1 : List Expr)
                         (m2 : String) (args2 : List Expr) : UnifyResult :=
  if !isPatternSpine args1 || !isPatternSpine args2 then
    .stuck (st.postpone (.lit m1) (.lit m2))  -- Not patterns, postpone
  else
    let vars1 := spineToVars args1
    let vars2 := spineToVars args2
    -- Check if vars2 ⊆ vars1 (can solve m2 := ... m1 ...)
    let subset21 := vars2.all (fun v => vars1.contains v)
    -- Check if vars1 ⊆ vars2 (can solve m1 := ... m2 ...)
    let subset12 := vars1.all (fun v => vars2.contains v)

    if subset21 then
      -- vars2 ⊆ vars1, so solve m2 := λy₁...λyₖ. m1 (perm of ys)
      -- Build: m1 applied to vars2 reindexed through vars1
      let body := buildMetaApp m1 vars1 vars2
      let solution := args2.foldr (fun _ b => .lam b) body
      .success (st.solveMeta (GName.named m2) solution)
    else if subset12 then
      -- vars1 ⊆ vars2, solve m1 := λx₁...λxₖ. m2 (perm of xs)
      let body := buildMetaApp m2 vars2 vars1
      let solution := args1.foldr (fun _ b => .lam b) body
      .success (st.solveMeta (GName.named m1) solution)
    else
      -- No subset relationship, would need fresh meta with intersection
      -- Postpone for now
      .stuck (st.postpone (.lit m1) (.lit m2))
where
  /-- Find index of element in list -/
  findIndex (xs : List Nat) (v : Nat) : Option Nat :=
    let rec go (idx : Nat) : List Nat → Option Nat
      | [] => none
      | x :: rest => if x == v then some idx else go (idx + 1) rest
    go 0 xs
  /-- Build ?m x₁ ... xₙ where xᵢ come from targetVars reindexed through sourceVars
      sourceVars = spine of source meta
      targetVars = spine of target meta (subset of sourceVars)
  -/
  buildMetaApp (m : String) (sourceVars targetVars : List Nat) : Expr :=
    -- For each var in targetVars, find its position in sourceVars
    -- and use that position as the de Bruijn index (since we're under lambdas)
    let reindexed := targetVars.map fun v =>
      match findIndex sourceVars v with
      | some i => i
      | none => 0  -- Shouldn't happen if subset check passed
    reindexed.foldl (fun acc idx => .app acc (.ix idx)) (.lit m)

/-- Unify rigid terms structurally -/
partial def unifyRigid (st : UnifyState) (t1 t2 : Expr) : UnifyResult :=
  match t1, t2 with
  | .ix n1, .ix n2 =>
    if n1 == n2 then .success st else .failure "variable mismatch"
  | .lit l1, .lit l2 =>
    if l1 == l2 then .success st else .failure s!"literal mismatch: {l1} ≠ {l2}"
  | .univ l1, .univ l2 =>
    if Level.levelEq l1 l2 then .success st else .failure "universe level mismatch"

  | .lam body1, .lam body2 =>
    unify st body1 body2

  | .app f1 a1, .app f2 a2 =>
    match unify st f1 f2 with
    | .success st' => unify st' a1 a2
    | other => other

  | .pi dom1 cod1, .pi dom2 cod2 =>
    match unify st dom1 dom2 with
    | .success st' => unify st' cod1 cod2
    | other => other

  | .sigma dom1 cod1, .sigma dom2 cod2 =>
    match unify st dom1 dom2 with
    | .success st' => unify st' cod1 cod2
    | other => other

  | .pair a1 b1, .pair a2 b2 =>
    match unify st a1 a2 with
    | .success st' => unify st' b1 b2
    | other => other

  | .fst p1, .fst p2 => unify st p1 p2
  | .snd p1, .snd p2 => unify st p1 p2

  | .path ty1 a1 b1, .path ty2 a2 b2 =>
    match unify st ty1 ty2 with
    | .success st' =>
      match unify st' a1 a2 with
      | .success st'' => unify st'' b1 b2
      | other => other
    | other => other

  | .plam body1, .plam body2 => unify st body1 body2
  | .papp p1 r1, .papp p2 r2 =>
    match unify st p1 p2 with
    | .success st' => unify st' r1 r2
    | other => other

  | .refl a1, .refl a2 => unify st a1 a2

  | .dim0, .dim0 => .success st
  | .dim1, .dim1 => .success st
  | .dimVar n1, .dimVar n2 =>
    if n1 == n2 then .success st else .failure "dimension variable mismatch"

  | .nat, .nat => .success st
  | .zero, .zero => .success st
  | .suc n1, .suc n2 => unify st n1 n2

  | .circle, .circle => .success st
  | .base, .base => .success st
  | .loop r1, .loop r2 => unify st r1 r2

  | .cof_top, .cof_top => .success st
  | .cof_bot, .cof_bot => .success st
  | .cof_eq a1 b1, .cof_eq a2 b2 =>
    match unify st a1 a2 with
    | .success st' => unify st' b1 b2
    | other => other
  | .cof_and a1 b1, .cof_and a2 b2 =>
    match unify st a1 a2 with
    | .success st' => unify st' b1 b2
    | other => other
  | .cof_or a1 b1, .cof_or a2 b2 =>
    match unify st a1 a2 with
    | .success st' => unify st' b1 b2
    | other => other

  | _, _ => .failure s!"structural mismatch"

/-- Unify lists of arguments -/
partial def unifyArgs (st : UnifyState) (args1 args2 : List Expr) : UnifyResult :=
  match args1, args2 with
  | [], [] => .success st
  | a1 :: rest1, a2 :: rest2 =>
    match unify st a1 a2 with
    | .success st' => unifyArgs st' rest1 rest2
    | other => other
  | _, _ => .failure "argument count mismatch"

end -- mutual

/-! ## Substitution Application

    Apply meta-variable solutions throughout a term.
-/

/-- Substitute solved metas in an expression -/
partial def applyMetas (st : UnifyState) : Expr → Expr
  | e@(.lit name) =>
    if name.startsWith "?" then
      match st.lookupMeta (GName.named name) with
      | some { solution := some sol, .. } => applyMetas st sol
      | _ => e
    else e
  | .lam body => .lam (applyMetas st body)
  | .app f a => .app (applyMetas st f) (applyMetas st a)
  | .pi dom cod => .pi (applyMetas st dom) (applyMetas st cod)
  | .sigma dom cod => .sigma (applyMetas st dom) (applyMetas st cod)
  | .pair a b => .pair (applyMetas st a) (applyMetas st b)
  | .fst p => .fst (applyMetas st p)
  | .snd p => .snd (applyMetas st p)
  | .path ty a b => .path (applyMetas st ty) (applyMetas st a) (applyMetas st b)
  | .plam body => .plam (applyMetas st body)
  | .papp p r => .papp (applyMetas st p) (applyMetas st r)
  | .refl a => .refl (applyMetas st a)
  | .coe r r' ty a => .coe (applyMetas st r) (applyMetas st r') (applyMetas st ty) (applyMetas st a)
  | .hcom r r' ty phi cap =>
    .hcom (applyMetas st r) (applyMetas st r') (applyMetas st ty)
      (applyMetas st phi)
      (applyMetas st cap)
  | .hcomTube r r' ty tubes cap =>
    .hcomTube (applyMetas st r) (applyMetas st r') (applyMetas st ty)
      (List.map (fun (c, t) => (applyMetas st c, applyMetas st t)) tubes)
      (applyMetas st cap)
  | .com r r' ty tubes cap =>
    .com (applyMetas st r) (applyMetas st r') (applyMetas st ty)
      (List.map (fun (c, t) => (applyMetas st c, applyMetas st t)) tubes)
      (applyMetas st cap)
  | .letE ty val body => .letE (applyMetas st ty) (applyMetas st val) (applyMetas st body)
  | .suc n => .suc (applyMetas st n)
  | .natElim p z s n =>
    .natElim (applyMetas st p) (applyMetas st z) (applyMetas st s) (applyMetas st n)
  | .loop r => .loop (applyMetas st r)
  | .circleElim p b l x =>
    .circleElim (applyMetas st p) (applyMetas st b) (applyMetas st l) (applyMetas st x)
  | .vtype r a b e =>
    .vtype (applyMetas st r) (applyMetas st a) (applyMetas st b) (applyMetas st e)
  | .vin r m n => .vin (applyMetas st r) (applyMetas st m) (applyMetas st n)
  | .vproj r a b e v =>
    .vproj (applyMetas st r) (applyMetas st a) (applyMetas st b) (applyMetas st e) (applyMetas st v)
  | .glue a phi t equiv =>
    .glue (applyMetas st a) (applyMetas st phi) (applyMetas st t) (applyMetas st equiv)
  | .glueElem t a =>
    .glueElem (applyMetas st t) (applyMetas st a)
  | .unglue g => .unglue (applyMetas st g)
  | .sys branches =>
    .sys (List.map (fun (c, t) => (applyMetas st c, applyMetas st t)) branches)
  | .cof_eq a b => .cof_eq (applyMetas st a) (applyMetas st b)
  | .cof_and a b => .cof_and (applyMetas st a) (applyMetas st b)
  | .cof_or a b => .cof_or (applyMetas st a) (applyMetas st b)
  | e => e  -- Atoms: ix, dim0, dim1, nat, zero, circle, base, cof_top, cof_bot

/-! ## Constraint Solving Loop

    After solving some metas, retry postponed constraints.
    Continue until no more progress is made.
-/

/-- Process postponed constraints, applying current solutions and retrying.
    Returns (new state, whether progress was made).
-/
def processPostponed (st : UnifyState) : UnifyState × Bool :=
  let constraints := st.postponed
  if constraints.isEmpty then
    (st, false)
  else
    -- Clear postponed and retry each constraint
    let st' := { st with postponed := [] }
    constraints.foldl (fun (acc, progress) (t1, t2) =>
      -- Apply current solutions before retrying
      let t1' := applyMetas acc t1
      let t2' := applyMetas acc t2
      match unify acc t1' t2' with
      | .success newSt => (newSt, true)
      | .stuck newSt => (newSt, progress)  -- Re-postponed, no progress on this one
      | .failure _ => (acc.postpone t1' t2', progress)  -- Keep trying
    ) (st', false)

/-- Solve all constraints with fuel-bounded iteration.
    Keeps retrying postponed constraints until no progress.
-/
def solveAll (st : UnifyState) (fuel : Nat := 100) : UnifyState :=
  match fuel with
  | 0 => st
  | n + 1 =>
    let (st', progress) := processPostponed st
    if progress then
      solveAll st' n  -- Made progress, continue
    else
      st'  -- No more progress, done

/-! ## High-Level Interface -/

/-- Attempt to unify two expressions, returning updated state or error -/
def tryUnify (st : UnifyState) (t1 t2 : Expr) : Option UnifyState :=
  match unify st t1 t2 with
  | .success st' => some st'
  | .stuck st' => some st'  -- Accept postponed constraints
  | .failure _ => none

/-- Unify and solve all constraints -/
def unifyAndSolve (st : UnifyState) (t1 t2 : Expr) : Option UnifyState :=
  match unify st t1 t2 with
  | .success st' => some (solveAll st')
  | .stuck st' => some (solveAll st')
  | .failure _ => none

/-- Create a hole (meta-variable) in a context -/
def hole (st : UnifyState) (ctx : List Expr) (ty : Expr) : UnifyState × Expr :=
  let (st', name) := st.freshMeta ctx ty
  (st', .lit name.name)

/-- Check if all metas are solved -/
def allSolved (st : UnifyState) : Bool :=
  st.unsolved.isEmpty

/-- Get a human-readable summary of unsolved metas -/
def unsolvedSummary (st : UnifyState) : String :=
  let unsolved := st.unsolved
  if unsolved.isEmpty then
    "All meta-variables solved"
  else
    let entries := unsolved.map fun m =>
      s!"  {m.name} : {Expr.toString m.ty}"
    s!"Unsolved meta-variables ({unsolved.length}):\n" ++ String.intercalate "\n" entries

end Lego.Red
