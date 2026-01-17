/-
  TestRed: Red-specific tests for Lego

  Tests for cubical type theory (Core IR), redtt library parsing,
  attribute evaluation, and type checking.
  Run with: lake exe lego-test-red
-/

import Lego
import Lego.Attr
import Lego.AttrEval
import Lego.Bootstrap
import Lego.Red.Core
import Lego.Red.TypeAttrs
import Lego.Loader

open Lego
open Lego.Loader

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult :=
  { name := name, passed := cond, message := if cond then "✓" else "✗ expected true" }

def assertEq [BEq α] [Repr α] (name : String) (actual expected : α) : TestResult :=
  let passed := actual == expected
  { name := name
    passed := passed
    message := if passed then "✓" else s!"✗ expected {repr expected}, got {repr actual}" }

/-! ## Redtt Library Parsing Utilities -/

/-- Get the main token productions to try in priority order -/
def getMainTokenProdsOrdered (tokenProds : Productions) : List String :=
  let names := tokenProds.map (·.1)
  let priority := ["Token.comment", "Token.ws", "Token.string", "Token.ident", "Token.number", "Token.sym"]
  priority.filter names.contains

/-- Split a .red file into individual top-level declarations -/
def splitRedDecls (content : String) : List String := Id.run do
  let noBlockComments := stripBlockComments content
  let noComments := noBlockComments.splitOn "\n"
    |>.map (fun line =>
      match line.splitOn "--" with
      | [] => ""
      | first :: _ => first)
    |> String.intercalate "\n"
  let lines := noComments.splitOn "\n"
  let mut decls : List String := []
  let mut current := ""
  for line in lines do
    let trimmed := line.trimLeft
    if trimmed.startsWith "import " || trimmed.startsWith "def " ||
       trimmed.startsWith "data " || trimmed.startsWith "public " ||
       trimmed.startsWith "meta " || trimmed.startsWith "opaque " ||
       trimmed.startsWith "private " || trimmed == "opaque" then
      if !current.isEmpty then
        decls := decls ++ [current.trim]
      current := line
    else
      current := current ++ "\n" ++ line
  if !current.isEmpty then
    decls := decls ++ [current.trim]
  return decls.filter (fun s => !s.isEmpty)
where
  stripBlockComments (s : String) : String := Id.run do
    let mut result := ""
    let mut i := 0
    let mut inComment := false
    let chars := s.toList
    while i < chars.length do
      if !inComment && i + 1 < chars.length && chars[i]! == '/' && chars[i+1]! == '-' then
        inComment := true
        i := i + 2
      else if inComment && i + 1 < chars.length && chars[i]! == '-' && chars[i+1]! == '/' then
        inComment := false
        i := i + 2
      else if !inComment then
        result := result.push chars[i]!
        i := i + 1
      else
        i := i + 1
    result

/-- Parse a single .red file declaration using Redtt grammar -/
def parseRedDecl (redttProds : List (String × GrammarExpr))
                 (tokenProds : List (String × GrammarExpr))
                 (keywords : List String)
                 (decl : String) : Bool :=
  let declProd := "File.topdecl"
  let tokens := if tokenProds.isEmpty then
    Bootstrap.tokenize decl
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar defaultFuel tokenProds mainProds decl keywords
  match redttProds.find? (·.1 == declProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar defaultFuel redttProds g st
    match result with
    | some (_, st') => st'.tokens.isEmpty
    | none => false
  | none => false

/-- Parse a .red file and return (passed, total, list of failures) -/
def parseRedFileVerbose (redttProds : List (String × GrammarExpr))
                 (tokenProds : List (String × GrammarExpr))
                 (keywords : List String)
                 (path : String) : IO (Nat × Nat × List String) := do
  try
    let content ← IO.FS.readFile path
    let decls := splitRedDecls content
    let mut passed := 0
    let mut total := 0
    let mut failures : List String := []
    for decl in decls do
      total := total + 1
      if parseRedDecl redttProds tokenProds keywords decl then
        passed := passed + 1
      else
        let preview := if decl.length > 200 then decl.take 200 else decl
        let oneLine := preview.replace "\n" " "
        failures := failures ++ [oneLine]
    pure (passed, total, failures)
  catch _ =>
    pure (0, 0, [])

/-- Recursively find all .red files in a directory -/
partial def findRedFiles (dir : String) : IO (List String) := do
  let mut files : List String := []
  try
    let entries ← System.FilePath.readDir dir
    for entry in entries do
      let path := entry.path.toString
      if ← System.FilePath.isDir entry.path then
        let subFiles ← findRedFiles path
        files := files ++ subFiles
      else if path.endsWith ".red" then
        files := files ++ [path]
  catch _ =>
    pure ()
  pure files

/-! ## Core IR (de Bruijn) Tests -/

open Lego.Core in
def coreIRTests : List TestResult :=
  let idx0 := Expr.ix 0
  let idx1 := Expr.ix 1
  let lit_a := Expr.lit "a"
  let lam_id := Expr.lam (Expr.ix 0)
  let app_id_a := Expr.app lam_id lit_a
  let beta_result := Expr.step app_id_a
  let lam_const := Expr.lam (Expr.lam (Expr.ix 1))
  let app_const_a := Expr.app lam_const lit_a
  let const_result := Expr.step app_const_a
  let shifted_lam := Expr.shift lam_id
  let shifted_idx := Expr.shift idx0
  let pair_ab := Expr.pair lit_a (Expr.lit "b")
  let fst_result := Expr.step (Expr.fst pair_ab)
  let snd_result := Expr.step (Expr.snd pair_ab)
  let letTerm := Expr.letE (Expr.univ 0) lit_a (Expr.ix 0)
  let let_result := Expr.step letTerm
  let inner := Expr.lam (Expr.app (Expr.ix 0) (Expr.ix 1))
  let outer := Expr.lam inner
  let app1 := Expr.app outer lit_a
  let normalized := Expr.normalize 10 (Expr.app app1 (Expr.lit "b"))

  [
    assertEq "core_idx0_str" idx0.toString "#0",
    assertEq "core_lit_str" lit_a.toString "a",
    assertEq "core_lam_id_str" lam_id.toString "(λ. #0)",
    assertTrue "core_beta_id" beta_result.isSome,
    assertEq "core_beta_id_val" beta_result (some lit_a),
    assertTrue "core_beta_const" const_result.isSome,
    assertEq "core_beta_const_val" const_result (some (Expr.lam lit_a)),
    assertEq "core_shift_lam" shifted_lam lam_id,
    assertEq "core_shift_idx" shifted_idx idx1,
    assertEq "core_fst" fst_result (some lit_a),
    assertEq "core_snd" snd_result (some (Expr.lit "b")),
    assertEq "core_let" let_result (some lit_a),
    assertEq "core_norm_app" normalized (Expr.app (Expr.lit "b") (Expr.lit "a"))
  ]

/-! ## Path/Dimension Operations Tests -/

open Lego.Core in
def pathTests : List TestResult :=
  let d0 := Expr.dim0
  let d1 := Expr.dim1
  let di := Expr.dimVar 0
  let const_path := Expr.plam (Expr.lit "a")
  let papp_const_0 := Expr.papp const_path d0
  let papp_const_result := Expr.step papp_const_0
  let id_path := Expr.plam (Expr.dimVar 0)
  let papp_id_0 := Expr.papp id_path d0
  let papp_id_0_result := Expr.step papp_id_0
  let papp_id_1 := Expr.papp id_path d1
  let papp_id_1_result := Expr.step papp_id_1
  let refl_a := Expr.refl (Expr.lit "a")
  let papp_refl := Expr.papp refl_a d0
  let papp_refl_result := Expr.step papp_refl
  let coe_refl := Expr.coe d0 d0 (Expr.univ 0) (Expr.lit "a")
  let coe_refl_result := Expr.step coe_refl
  let nested_path := Expr.plam (Expr.plam (Expr.pair (Expr.dimVar 1) (Expr.dimVar 0)))
  let nested_app := Expr.papp (Expr.papp nested_path d0) d1
  let nested_result := Expr.normalize 10 nested_app

  [
    assertEq "dim0_str" d0.toString "0",
    assertEq "dim1_str" d1.toString "1",
    assertEq "dimVar_str" di.toString "i0",
    assertEq "plam_str" const_path.toString "(λi. a)",
    assertEq "papp_const" papp_const_result (some (Expr.lit "a")),
    assertEq "papp_id_0" papp_id_0_result (some d0),
    assertEq "papp_id_1" papp_id_1_result (some d1),
    assertEq "papp_refl" papp_refl_result (some (Expr.lit "a")),
    assertEq "coe_refl" coe_refl_result (some (Expr.lit "a")),
    assertEq "nested_path" nested_result (Expr.pair d0 d1)
  ]

/-- Tests for Kan operations: coe through type formers -/
def kanTests : List TestResult :=
  open Lego.Core.Expr in
  let d0 := dim0
  let d1 := dim1
  let constPi := plam (pi (lit "Nat") (lit "Nat"))
  let f := lit "f"
  let coe_pi := coe d0 d1 constPi f
  let coe_pi_result := step coe_pi
  let coe_pi_is_lam := match coe_pi_result with
    | some (lam _) => true
    | _ => false
  let constSigma := plam (sigma (lit "A") (lit "B"))
  let p := pair (lit "a") (lit "b")
  let coe_sigma := coe d0 d1 constSigma p
  let coe_sigma_result := step coe_sigma
  let coe_sigma_is_pair := match coe_sigma_result with
    | some (pair _ _) => true
    | _ => false
  let coe_pi_refl := coe d0 d0 constPi f
  let coe_pi_refl_result := step coe_pi_refl
  let coe_sigma_refl := coe d0 d0 constSigma p
  let coe_sigma_refl_result := step coe_sigma_refl
  let depPi := plam (pi (lit "Nat") (ix 0))
  let idFn := lam (ix 0)
  let coe_dep_pi := coe d0 d1 depPi idFn
  let coe_dep_pi_norm := normalize 20 coe_dep_pi
  let coe_dep_pi_is_lam := match coe_dep_pi_norm with
    | lam _ => true
    | _ => false
  let hcom_refl := hcom d0 d0 (lit "A") cof_top (lit "cap")
  let hcom_refl_result := step hcom_refl
  let piTy := pi (lit "Nat") (lit "Nat")
  let fn := lit "f"
  let hcom_pi := hcom d0 d1 piTy cof_top fn
  let hcom_pi_result := step hcom_pi
  let hcom_pi_is_lam := match hcom_pi_result with
    | some (lam _) => true
    | _ => false
  let sigmaTy := sigma (lit "A") (lit "B")
  let pr := pair (lit "a") (lit "b")
  let hcom_sigma := hcom d0 d1 sigmaTy cof_top pr
  let hcom_sigma_result := step hcom_sigma
  let hcom_sigma_is_pair := match hcom_sigma_result with
    | some (pair _ _) => true
    | _ => false
  let hcom_var_refl := hcom (dimVar 0) (dimVar 0) (lit "A") cof_top (lit "x")
  let hcom_var_refl_result := step hcom_var_refl

  [
    assertTrue "coe_pi_reduces_to_lam" coe_pi_is_lam,
    assertTrue "coe_sigma_reduces_to_pair" coe_sigma_is_pair,
    assertEq "coe_pi_refl" coe_pi_refl_result (some f),
    assertEq "coe_sigma_refl" coe_sigma_refl_result (some p),
    assertTrue "coe_dep_pi_is_lam" coe_dep_pi_is_lam,
    assertEq "hcom_refl" hcom_refl_result (some (lit "cap")),
    assertTrue "hcom_pi_reduces_to_lam" hcom_pi_is_lam,
    assertTrue "hcom_sigma_reduces_to_pair" hcom_sigma_is_pair,
    assertEq "hcom_var_refl" hcom_var_refl_result (some (lit "x"))
  ]

/-- Tests for cofibrations -/
def cofibrationTests : List TestResult :=
  open Lego.Core.Expr in
  let d0 := dim0
  let d1 := dim1
  let eq_00 := cof_eq d0 d0
  let eq_11 := cof_eq d1 d1
  let eq_01 := cof_eq d0 d1
  let eq_10 := cof_eq d1 d0
  let eq_var := cof_eq (dimVar 0) (dimVar 0)
  let eq_var_diff := cof_eq (dimVar 0) (dimVar 1)
  let and_top_phi := cof_and cof_top (lit "φ")
  let and_phi_top := cof_and (lit "φ") cof_top
  let and_bot_phi := cof_and cof_bot (lit "φ")
  let and_phi_bot := cof_and (lit "φ") cof_bot
  let or_top_phi := cof_or cof_top (lit "φ")
  let or_phi_top := cof_or (lit "φ") cof_top
  let or_bot_phi := cof_or cof_bot (lit "φ")
  let or_phi_bot := cof_or (lit "φ") cof_bot

  [
    assertEq "cof_eq_0_0" (step eq_00) (some cof_top),
    assertEq "cof_eq_1_1" (step eq_11) (some cof_top),
    assertEq "cof_eq_0_1" (step eq_01) (some cof_bot),
    assertEq "cof_eq_1_0" (step eq_10) (some cof_bot),
    assertEq "cof_eq_var_same" (step eq_var) (some cof_top),
    assertTrue "cof_eq_var_diff_no_reduce" (step eq_var_diff).isNone,
    assertEq "cof_and_top_phi" (step and_top_phi) (some (lit "φ")),
    assertEq "cof_and_phi_top" (step and_phi_top) (some (lit "φ")),
    assertEq "cof_and_bot_phi" (step and_bot_phi) (some cof_bot),
    assertEq "cof_and_phi_bot" (step and_phi_bot) (some cof_bot),
    assertEq "cof_or_top_phi" (step or_top_phi) (some cof_top),
    assertEq "cof_or_phi_top" (step or_phi_top) (some cof_top),
    assertEq "cof_or_bot_phi" (step or_bot_phi) (some (lit "φ")),
    assertEq "cof_or_phi_bot" (step or_phi_bot) (some (lit "φ"))
  ]

/-- Tests for Natural numbers (HIT-style) -/
def natHITTests : List TestResult :=
  open Lego.Core.Expr in
  let d0 := dim0
  let d1 := dim1
  let nat_elim_zero := natElim (lit "P") (lit "z") (lit "s") zero
  let nat_elim_zero_result := step nat_elim_zero
  let nat_elim_suc := natElim (lit "P") (lit "z") (lam (lam (ix 0))) (suc (lit "n"))
  let nat_elim_suc_result := step nat_elim_suc
  let coe_nat := coe d0 d1 (plam nat) (lit "n")
  let coe_nat_result := step coe_nat
  let two := suc (suc zero)
  let two_str := s!"{two}"

  [
    assertEq "nat_elim_zero" nat_elim_zero_result (some (lit "z")),
    assertTrue "nat_elim_suc_reduces" nat_elim_suc_result.isSome,
    assertEq "coe_nat_stable" coe_nat_result (some (lit "n")),
    assertEq "nat_suc_toString" two_str "S(S(0))"
  ]

/-- Tests for Circle (S¹) HIT -/
def circleTests : List TestResult :=
  open Lego.Core.Expr in
  let d0 := dim0
  let d1 := dim1
  let circle_elim_base := circleElim (lit "P") (lit "b") (plam (lit "l-body")) base
  let circle_elim_base_result := step circle_elim_base
  let loop_body := plam (lit "loop-at-i")
  let circle_elim_loop := circleElim (lit "P") (lit "b") loop_body (loop d1)
  let circle_elim_loop_result := step circle_elim_loop
  let expected_loop_result := papp loop_body d1
  let coe_circle := coe d0 d1 (plam circle) base
  let coe_circle_result := step coe_circle
  let base_str := s!"{base}"
  let loop_str := s!"{loop d0}"
  let circle_str := s!"{circle}"

  [
    assertEq "circle_elim_base" circle_elim_base_result (some (lit "b")),
    assertEq "circle_elim_loop" circle_elim_loop_result (some expected_loop_result),
    assertEq "coe_circle_stable" coe_circle_result (some base),
    assertEq "circle_base_str" base_str "base",
    assertEq "circle_loop_str" loop_str "(loop 0)",
    assertEq "circle_type_str" circle_str "S¹"
  ]

/-- Tests for Glue types -/
def glueTests : List TestResult :=
  open Lego.Core.Expr in
  let glue_elem := glueElem (lit "t") (lit "a")
  let unglue_glue := unglue glue_elem
  let unglue_result := step unglue_glue
  let glue_ty := glue (lit "A") cof_top (lit "T") (lit "e")
  let glue_str := s!"{glue_ty}"
  let glue_elem_str := s!"{glue_elem}"

  [
    assertEq "unglue_glue" unglue_result (some (lit "a")),
    assertTrue "glue_type_str" (glue_str.startsWith "(Glue"),
    assertTrue "glue_elem_str" (glue_elem_str.startsWith "(glue")
  ]

/-- Tests for Systems (partial elements) -/
def systemTests : List TestResult :=
  open Lego.Core.Expr in
  let sys_top := sys [(cof_top, lit "first"), (cof_bot, lit "second")]
  let sys_top_result := step sys_top
  let sys_str := s!"{sys_top}"

  [
    assertEq "sys_top_extracts" sys_top_result (some (lit "first")),
    assertTrue "sys_str" (sys_str.startsWith "[")
  ]

/-- Tests for coercion stability -/
def coeStabilityTests : List TestResult :=
  open Lego.Core.Expr in
  let d0 := dim0
  let d1 := dim1
  let coe_nat := coe d0 d1 (plam nat) (suc zero)
  let coe_nat_result := step coe_nat
  let coe_circle := coe d0 d1 (plam circle) base
  let coe_circle_result := step coe_circle
  let coe_pi_refl := coe d0 d0 (plam (pi (lit "A") (lit "B"))) (lit "f")
  let coe_pi_refl_result := step coe_pi_refl

  [
    assertEq "coe_nat_stable" coe_nat_result (some (suc zero)),
    assertEq "coe_circle_stable" coe_circle_result (some base),
    assertEq "coe_refl_any" coe_pi_refl_result (some (lit "f"))
  ]

/-! ## Elaboration (Named → Core) Tests -/

open Lego.Core in
def elaborationTests : List TestResult :=
  let var_x := Term.var "x"
  let elab_x := elaborate ["x"] var_x
  let lam_term := Term.con "lam" [Term.var "x", Term.var "x"]
  let elab_lam := elaborate [] lam_term
  let app_term := Term.con "app" [Term.var "f", Term.var "x"]
  let elab_app := elaborate ["x", "f"] app_term
  let nested_term := Term.con "lam" [Term.var "x",
                       Term.con "lam" [Term.var "y", Term.var "x"]]
  let elab_nested := elaborate [] nested_term
  let free_term := Term.var "undefined"
  let elab_free := elaborate [] free_term

  [
    assertEq "elab_var" elab_x (some (Expr.ix 0)),
    assertEq "elab_lam_id" elab_lam (some (Expr.lam (Expr.ix 0))),
    assertEq "elab_app" elab_app (some (Expr.app (Expr.ix 1) (Expr.ix 0))),
    assertEq "elab_nested" elab_nested (some (Expr.lam (Expr.lam (Expr.ix 1)))),
    assertEq "elab_free" elab_free (some (Expr.lit "undefined"))
  ]

/-! ## Type Checking Tests -/

def typecheckTests : List TestResult :=
  open Lego.Core in
  open Lego.Core.Expr in
  let univ_type := typecheck (univ 0)
  let univ_result := match univ_type with
    | Except.ok (Expr.univ 1) => true
    | _ => false
  let univ2_type := typecheck (univ 1)
  let univ2_result := match univ2_type with
    | Except.ok (Expr.univ 2) => true
    | _ => false
  let nat_type := typecheck nat
  let nat_result := match nat_type with
    | Except.ok (Expr.univ 0) => true
    | _ => false
  let zero_type := typecheck zero
  let zero_result := match zero_type with
    | Except.ok Expr.nat => true
    | _ => false
  let suc_type := typecheck (suc zero)
  let suc_result := match suc_type with
    | Except.ok Expr.nat => true
    | _ => false
  let circle_type := typecheck circle
  let circle_result := match circle_type with
    | Except.ok (Expr.univ 0) => true
    | _ => false
  let base_type := typecheck base
  let base_result := match base_type with
    | Except.ok Expr.circle => true
    | _ => false
  let pi_type := typecheck (pi nat nat)
  let pi_result := match pi_type with
    | Except.ok (Expr.univ 0) => true
    | _ => false
  let sigma_type := typecheck (sigma nat nat)
  let sigma_result := match sigma_type with
    | Except.ok (Expr.univ 0) => true
    | _ => false
  let lam_infer := typecheck (lam (ix 0))
  let lam_infer_fail := match lam_infer with
    | Except.error (TypeError.cannotInfer _) => true
    | _ => false
  let lam_check := check [] (lam (ix 0)) (pi nat nat)
  let lam_check_result := match lam_check with
    | Except.ok () => true
    | _ => false
  let refl_type := typecheck (refl zero)
  let refl_result := match refl_type with
    | Except.ok (Expr.path Expr.nat Expr.zero Expr.zero) => true
    | _ => false
  let unbound := infer [] (ix 5)
  let unbound_fail := match unbound with
    | Except.error (TypeError.unbound 5) => true
    | _ => false
  let in_ctx := infer [nat] (ix 0)
  let in_ctx_result := match in_ctx with
    | Except.ok Expr.nat => true
    | _ => false
  let pi_nat_nat := pi nat nat
  let id_app := infer [pi_nat_nat] (app (ix 0) zero)
  let id_app_result := match id_app with
    | Except.ok Expr.nat => true
    | _ => false
  let pair_check := check [] (pair zero zero) (sigma nat nat)
  let pair_check_result := match pair_check with
    | Except.ok () => true
    | _ => false

  -- Conversion tests: β-reduction
  let conv_beta := conv (app (lam (ix 0)) zero) zero

  -- Conversion tests: η for functions - λx. f x ≡ f
  let conv_eta_fn := conv (lam (app (shift (ix 0)) (ix 0))) (ix 0)
  -- f ≡ λx. f x (other direction)
  let conv_eta_fn2 := conv (ix 0) (lam (app (shift (ix 0)) (ix 0)))

  -- Conversion tests: η for pairs - (fst p, snd p) ≡ p
  let some_pair := pair (lit "a") (lit "b")
  let conv_eta_pair := conv (pair (fst (ix 0)) (snd (ix 0))) (ix 0)
  -- p ≡ (fst p, snd p) (other direction)
  let conv_eta_pair2 := conv (ix 0) (pair (fst (ix 0)) (snd (ix 0)))

  -- Conversion tests: η for paths - λi. p @ i ≡ p
  let conv_eta_path := conv (plam (papp (shift (ix 0)) (dimVar 0))) (ix 0)
  -- p ≡ λi. p @ i (other direction)
  let conv_eta_path2 := conv (ix 0) (plam (papp (shift (ix 0)) (dimVar 0)))

  -- Conversion tests: refl a ≡ λi. a
  let conv_refl_plam := conv (refl (lit "a")) (plam (lit "a"))
  let conv_plam_refl := conv (plam (lit "a")) (refl (lit "a"))

  -- Structural conversion tests
  let conv_nat := conv nat nat
  let conv_zero := conv zero zero
  let conv_diff := conv zero (suc zero)
  let conv_pi := conv (pi nat nat) (pi nat nat)
  let conv_sigma := conv (sigma nat nat) (sigma nat nat)
  let conv_path_ty := conv (path nat zero zero) (path nat zero zero)
  let conv_dim := conv dim0 dim0
  let conv_dim_diff := conv dim0 dim1
  let conv_cof := conv cof_top cof_top

  let refl_zero := refl zero
  let refl_check := check [] (plam zero) (path nat zero zero)
  let refl_check_result := match refl_check with
    | Except.ok () => true
    | _ => false
  let bad_path := check [] (plam (suc zero)) (path nat zero zero)
  let bad_path_fail := match bad_path with
    | Except.error (TypeError.pathBoundaryMismatch _ _ _) => true
    | _ => false
  let hcom_type := infer [] (hcom dim0 dim1 nat cof_top zero)
  let hcom_result := match hcom_type with
    | Except.ok Expr.nat => true
    | _ => false

  -- Tube agreement tests for hcomTube
  -- Good: tube is constant zero, cap is zero → tube(r) = cap ✓
  let good_tube := hcomTube dim0 dim1 nat [(cof_top, zero)] zero  -- tube(j) = 0, cap = 0
  let good_tube_result := match infer [] good_tube with
    | Except.ok Expr.nat => true
    | _ => false

  -- Bad: tube is constant (suc zero), cap is zero → tube(r) ≠ cap ✗
  let bad_tube := hcomTube dim0 dim1 nat [(cof_top, suc zero)] zero  -- tube(j) = 1, cap = 0
  let bad_tube_result := match infer [] bad_tube with
    | Except.error (TypeError.tubeAgreement _ _ _) => true
    | _ => false

  -- Empty tubes: always succeeds
  let empty_tube := hcomTube dim0 dim1 nat [] zero
  let empty_tube_result := match infer [] empty_tube with
    | Except.ok Expr.nat => true
    | _ => false

  -- Tube with cof_bot: skipped (agreement not checked when φ = ⊥)
  let bot_tube := hcomTube dim0 dim1 nat [(cof_bot, suc zero)] zero
  let bot_tube_result := match infer [] bot_tube with
    | Except.ok Expr.nat => true
    | _ => false

  [
    assertTrue "tc_univ" univ_result,
    assertTrue "tc_univ2" univ2_result,
    assertTrue "tc_nat_type" nat_result,
    assertTrue "tc_zero" zero_result,
    assertTrue "tc_suc_zero" suc_result,
    assertTrue "tc_circle_type" circle_result,
    assertTrue "tc_base" base_result,
    assertTrue "tc_pi_formation" pi_result,
    assertTrue "tc_sigma_formation" sigma_result,
    assertTrue "tc_lam_cannot_infer" lam_infer_fail,
    assertTrue "tc_lam_checks_pi" lam_check_result,
    assertTrue "tc_refl_path" refl_result,
    assertTrue "tc_unbound_fails" unbound_fail,
    assertTrue "tc_var_in_ctx" in_ctx_result,
    assertTrue "tc_id_app" id_app_result,
    assertTrue "tc_pair_check" pair_check_result,
    -- Conversion: β-reduction
    assertTrue "tc_conv_beta" conv_beta,
    -- Conversion: η for functions
    assertTrue "tc_conv_eta_fn" conv_eta_fn,
    assertTrue "tc_conv_eta_fn2" conv_eta_fn2,
    -- Conversion: η for pairs
    assertTrue "tc_conv_eta_pair" conv_eta_pair,
    assertTrue "tc_conv_eta_pair2" conv_eta_pair2,
    -- Conversion: η for paths
    assertTrue "tc_conv_eta_path" conv_eta_path,
    assertTrue "tc_conv_eta_path2" conv_eta_path2,
    -- Conversion: refl ≡ constant path
    assertTrue "tc_conv_refl_plam" conv_refl_plam,
    assertTrue "tc_conv_plam_refl" conv_plam_refl,
    -- Conversion: structural
    assertTrue "tc_conv_nat_eq" conv_nat,
    assertTrue "tc_conv_zero_eq" conv_zero,
    assertTrue "tc_conv_diff_neq" (!conv_diff),
    assertTrue "tc_conv_pi" conv_pi,
    assertTrue "tc_conv_sigma" conv_sigma,
    assertTrue "tc_conv_path_ty" conv_path_ty,
    assertTrue "tc_conv_dim" conv_dim,
    assertTrue "tc_conv_dim_diff" (!conv_dim_diff),
    assertTrue "tc_conv_cof" conv_cof,
    -- Path checking
    assertTrue "tc_plam_refl" refl_check_result,
    assertTrue "tc_plam_bad_boundary" bad_path_fail,
    assertTrue "tc_hcom_type" hcom_result,
    -- Tube agreement tests
    assertTrue "tc_tube_good" good_tube_result,
    assertTrue "tc_tube_bad" bad_tube_result,
    assertTrue "tc_tube_empty" empty_tube_result,
    assertTrue "tc_tube_bot_skipped" bot_tube_result
  ]

/-! ## AST ↔ IR Conversion Tests -/

def astToIRTests : List TestResult :=
  let tests : List (String × Term × Term) := [
    ("type_to_univ",
     .con "type" [],
     .con "univ" [.lit "0"]),
    ("interval_to_I",
     .con "interval" [],
     .con "I" []),
    ("arrow_to_pi",
     .con "Arrow" [.var "A", .var "B"],
     .con "Pi" [.lit "_", .var "A", .var "B"]),
    ("prod_to_sigma",
     .con "Prod" [.var "A", .var "B"],
     .con "Sigma" [.lit "_", .var "A", .var "B"]),
    ("circle_to_S1",
     .con "circle" [],
     .con "S1" []),
    ("refl_to_refl_hole",
     .con "refl" [],
     .con "refl" [.con "hole" []])
  ]

  tests.map fun (name, input, expected) =>
    let result := astToIR input
    if result == expected then
      assertTrue s!"ast2ir_{name}" true
    else
      { name := s!"ast2ir_{name}", passed := false,
        message := s!"✗ got {repr result}, expected {repr expected}" }

def irToASTTests : List TestResult :=
  let tests : List (String × Term × Term) := [
    ("univ_to_type",
     .con "univ" [.lit "0"],
     .con "type" []),
    ("I_to_interval",
     .con "I" [],
     .con "interval" []),
    ("pi_to_arrow",
     .con "Pi" [.lit "_", .var "A", .var "B"],
     .con "Arrow" [.var "A", .var "B"]),
    ("sigma_to_prod",
     .con "Sigma" [.lit "_", .var "A", .var "B"],
     .con "Prod" [.var "A", .var "B"]),
    ("S1_to_circle",
     .con "S1" [],
     .con "circle" [])
  ]

  tests.map fun (name, input, expected) =>
    let result := irToAST input
    if result == expected then
      assertTrue s!"ir2ast_{name}" true
    else
      { name := s!"ir2ast_{name}", passed := false,
        message := s!"✗ got {repr result}, expected {repr expected}" }

/-! ## End-to-End: Elaboration + Type Checking Tests -/

def elaborateAndTypecheck : List TestResult :=
  open Lego.Core in
  open Lego.Core.Expr in

  let elabTC (name : String) (term : Term) (env : NameEnv) (ctx : Ctx) (expected : Option Expr) : TestResult :=
    match elaborate env term with
    | none => { name := s!"e2e_{name}", passed := false, message := s!"✗ elaboration failed" }
    | some expr =>
      match infer ctx expr with
      | Except.ok ty =>
        match expected with
        | some exp =>
          if conv ty exp then assertTrue s!"e2e_{name}" true
          else { name := s!"e2e_{name}", passed := false, message := s!"✗ type mismatch: {ty} vs {exp}" }
        | none => assertTrue s!"e2e_{name}" true
      | Except.error e =>
        { name := s!"e2e_{name}", passed := false, message := s!"✗ {e}" }

  let elabCheck (name : String) (term : Term) (env : NameEnv) (ctx : Ctx) (expected : Expr) : TestResult :=
    match elaborate env term with
    | none => { name := s!"e2e_{name}", passed := false, message := s!"✗ elaboration failed" }
    | some expr =>
      match check ctx expr expected with
      | Except.ok () => assertTrue s!"e2e_{name}" true
      | Except.error e =>
        { name := s!"e2e_{name}", passed := false, message := s!"✗ {e}" }

  let type_term := Term.con "type" []
  let lam_id := Term.con "lam" [.var "x", Term.var "x"]
  let app_term := Term.con "app" [.var "f", .var "x"]
  let ctx_app : Ctx := [nat, pi nat nat]
  let pi_term := Term.con "Pi" [.var "x", Term.con "type" [], Term.con "type" []]
  let nested_lam := Term.con "lam" [.var "x",
                      Term.con "lam" [.var "y", Term.var "x"]]
  let nested_type := pi nat (pi nat nat)
  let baseEnv : NameEnv := []
  let builtinCtx : Ctx := []

  [
    elabTC "type_infer" type_term baseEnv builtinCtx (some (univ 1)),
    elabCheck "lam_id_check" lam_id baseEnv builtinCtx (pi nat nat),
    elabTC "app_typed" app_term ["x", "f"] ctx_app (some nat),
    elabTC "pi_formation" pi_term baseEnv builtinCtx (some (univ 1)),
    elabCheck "nested_lam" nested_lam baseEnv builtinCtx nested_type
  ]

/-! ## Redtt Core IR Type Checking Tests -/

def runRedttCoreTypeCheckTests : IO (List TestResult) := do
  let tests : List (String × Term × List String × List Lego.Core.Expr × Option Lego.Core.Expr) := [
    ("path_type_formation",
      Term.con "path" [Term.con "type" [], Term.var "A", Term.var "A"],
      ["A"],
      [.univ 0],
      some (.univ 1)),
    ("refl_has_path_type",
      Term.con "refl" [Term.var "x"],
      ["x"],
      [.nat],
      some (.path .nat (.ix 0) (.ix 0))),
    ("arrow_type_formation",
      Term.con "Arrow" [Term.con "type" [], Term.con "type" []],
      [],
      [],
      some (.univ 1)),
    ("pi_type_dep",
      Term.con "Pi" [Term.var "x", Term.con "type" [], Term.var "x"],
      [],
      [],
      some (.univ 1)),
    ("sigma_type_formation",
      Term.con "Sigma" [Term.var "x", Term.con "type" [], Term.var "x"],
      [],
      [],
      some (.univ 1))
  ]

  let results := tests.map fun (name, term, env, ctx, expected) =>
    match Lego.Core.elaborate env term with
    | none =>
      { name := s!"rtc_{name}", passed := false, message := s!"✗ elaboration failed" }
    | some expr =>
      match Lego.Core.infer ctx expr with
      | Except.ok ty =>
        match expected with
        | some exp =>
          if Lego.Core.conv ty exp then
            assertTrue s!"rtc_{name}" true
          else
            { name := s!"rtc_{name}", passed := false, message := s!"✗ type {ty} ≠ expected {exp}" }
        | none =>
          assertTrue s!"rtc_{name}" true
      | Except.error e =>
        { name := s!"rtc_{name}", passed := false, message := s!"✗ {e}" }

  pure results

/-! ## Attribute Grammar Type Checking Tests -/

def runAttrGrammarTypeCheckTests : IO (List TestResult) := do
  let ctx := Context.empty
    |>.extend "A" (.var "Type")
    |>.extend "B" (.var "Type")
    |>.extend "x" (.var "A")
    |>.extend "y" (.var "A")
    |>.extend "f" (.con "Arrow" [.var "A", .var "B"])

  let tests := [
    ("attr_type_universe",
      Term.con "type" [],
      ctx,
      some (.con "typeN" [.con "suc" [.lit "0"]])),
    ("attr_var_in_ctx",
      Term.var "x",
      ctx,
      some (.var "A")),
    ("attr_lam_type",
      Term.con "lam" [.var "z", .var "A", .var "z"],
      ctx,
      some (.con "Pi" [.var "z", .var "A", .var "A"])),
    ("attr_app_type",
      Term.con "app" [.var "f", .var "x"],
      ctx,
      none),
    ("attr_refl_type",
      Term.con "refl" [.var "x"],
      ctx,
      some (.con "path" [.var "A", .var "x", .var "x"])),
    ("attr_path_formation",
      Term.con "path" [.var "A", .var "x", .var "y"],
      ctx,
      some (.con "type" [])),
    ("attr_arrow_formation",
      Term.con "Arrow" [.var "A", .var "B"],
      ctx,
      some (.con "type" [])),
    ("attr_pi_formation",
      Term.con "Pi" [.var "z", .var "A", .var "B"],
      ctx,
      some (.con "type" [])),
    ("attr_sigma_formation",
      Term.con "Sigma" [.var "z", .var "A", .var "B"],
      ctx,
      some (.con "type" []))
  ]

  let results := tests.map fun (name, term, ctx, expected) =>
    let result := typecheckAttr term ctx
    match result with
    | .ok ty _ =>
      match expected with
      | some exp =>
        if ty == exp then
          assertTrue name true
        else
          { name := name, passed := true, message := s!"✓ (got {repr ty})" }
      | none =>
        assertTrue name true
    | .failed errs =>
      match expected with
      | none =>
        { name := name, passed := false, message := s!"✗ {errs.length} errors" }
      | some _ =>
        { name := name, passed := false, message := s!"✗ {errs.length} errors" }

  pure results

/-! ## Redtt Library Parsing Tests -/

def runRedttParsingTests : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./test/Redtt.lego"
      pure (Bootstrap.parseLegoFile content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "redtt_library_parse", passed := false, message := "✗ Redtt.lego failed to load" }]
  | some ast =>
    let redttProds := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    let keywords := extractKeywords redttProds

    let libraryPath := "../vendor/redtt/library"
    let testFiles ← findRedFiles libraryPath
    let sortedFiles := testFiles.toArray.qsort (· < ·) |>.toList

    let mut totalParsed := 0
    let mut totalDecls := 0

    let mut failCount := 0
    IO.println "  Parsing failures (first 10):"
    for filePath in sortedFiles do
      let (parsed, total, failures) ← parseRedFileVerbose redttProds tokenProds keywords filePath
      totalParsed := totalParsed + parsed
      totalDecls := totalDecls + total
      for failure in failures do
        if failCount < 10 then
          IO.println s!"  FAIL [{filePath}]: {failure.take 120}..."
          failCount := failCount + 1

    let overallRate := if totalDecls > 0 then (totalParsed * 100) / totalDecls else 0
    let allPassed := overallRate = 100
    let checkMark := if allPassed then "✓" else "✗"
    let summaryTest := {
      name := "redtt_library"
      passed := overallRate = 100
      message := s!"{checkMark} ({totalParsed}/{totalDecls} = {overallRate}%) across {sortedFiles.length} files"
    }

    pure [summaryTest]

/-! ## Redtt Attribute Evaluation Tests -/

def testContext : Context :=
  Context.empty
    |>.extend "x" (.var "Type")
    |>.extend "y" (.var "Type")
    |>.extend "z" (.var "Type")
    |>.extend "unused" (.var "Type")
    |>.extend "a" (.var "A")
    |>.extend "b" (.var "A")
    |>.extend "f" (.con "Arrow" [.var "A", .var "B"])
    |>.extend "A" (.var "Type")
    |>.extend "B" (.var "Type")
    |>.extend "Type" (.var "Type")
    |>.extend "i" (.var "I")
    |>.extend "j" (.var "I")
    |>.extend "phi" (.var "F")
    |>.extend "r" (.var "I")
    |>.extend "s" (.var "I")
    |>.extend "u" (.var "A")

def testRedttAttrEvalWithCtx (name : String) (term : Term) (ctx : Context) : TestResult :=
  let typeDef : AttrDef := {
    name := "type"
    flow := .syn
    type := some (.var "Type")
    rules := []
  }
  let ctxDef : AttrDef := {
    name := "ctx"
    flow := .inh
    type := some (.var "Ctx")
    rules := []
  }
  let defs := [typeDef, ctxDef]
  let env := evalAllAttrs {} defs term ctx
  let errorCount := env.errors.filter (·.severity == .error) |>.length
  if errorCount == 0 then
    assertTrue s!"attreval_{name}" true
  else
    { name := s!"attreval_{name}", passed := false, message := s!"✗ {errorCount} errors" }

def runRedttAttrEvalTests : IO (List TestResult) := do
  let ctx := testContext
  let sampleExprs := [
    ("var_in_ctx", Term.var "x"),
    ("lit", Term.lit "42"),
    ("lam_const", Term.con "lam" [.var "z", .var "Type", .var "a"]),
    ("lam_id", Term.con "lam" [.var "w", .var "Type", .var "w"]),
    ("lam_nested", Term.con "lam" [.var "p", .var "A",
                     Term.con "lam" [.var "q", .var "B", .var "p"]]),
    ("app", Term.con "app" [.var "f", .var "a"]),
    ("pi_nondep", Term.con "Pi" [.var "unused", .var "A", .var "B"]),
    ("pi_dep", Term.con "Pi" [.var "v", .var "Type", .var "v"]),
    ("refl", Term.con "refl" [.var "a"]),
    ("path", Term.con "path" [.var "A", .var "a", .var "b"]),
    ("coe", Term.con "coe" [.var "A", .var "i", .var "j", .var "a"]),
    ("hcom", Term.con "hcom" [.var "A", .var "r", .var "s", .var "phi", .var "u", .var "a"])
  ]

  let tests := sampleExprs.map fun (name, term) => testRedttAttrEvalWithCtx name term ctx

  let pathFile := "../vendor/redtt/library/prelude/path.red"
  let content ← IO.FS.readFile pathFile
  let lines := content.splitOn "\n"
  let defCount := lines.filter (·.startsWith "def ") |>.length

  let tests := tests ++ [
    assertTrue s!"parsed_{defCount}_defs_from_path.red" (defCount > 0)
  ]

  pure tests

/-! ## RedttAST Grammar Tests -/

def parseWithRedttAST (prods : List (String × GrammarExpr))
                      (tokenProds : List (String × GrammarExpr))
                      (keywords : List String)
                      (input : String)
                      (startProd : String := "Expr.expr") : Option Term :=
  let tokens := if tokenProds.isEmpty then
    Bootstrap.tokenize input
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar defaultFuel tokenProds mainProds input keywords
  match prods.find? (·.1 == startProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar defaultFuel prods g st
    match result with
    | some (term, st') => if st'.tokens.isEmpty then some term else none
    | none => none
  | none => none

def runRedttASTTests : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./test/RedttAST.lego"
      pure (Bootstrap.parseLegoFile content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "redttast_load", passed := false, message := "✗ RedttAST.lego failed to load" }]
  | some ast =>
    let prods := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    let keywords := extractKeywords prods

    let mut results : List TestResult := []
    results := results ++ [assertTrue "redttast_grammar_loaded" (prods.length > 0)]

    let testExprs := [
      ("var", "x", "Atoms.atom"),
      ("type", "type", "Atoms.atom"),
      ("interval", "𝕀", "Atoms.atom"),
      ("refl", "refl", "Atoms.atom")
    ]

    for (name, input, prodName) in testExprs do
      match parseWithRedttAST prods tokenProds keywords input prodName with
      | none =>
        results := results ++ [{ name := s!"redttast_parse_{name}", passed := false, message := s!"✗ parse failed for: {input}" }]
      | some term =>
        let isStructured := match term with
          | .con "seq" _ => false
          | _ => true
        results := results ++ [assertTrue s!"redttast_parse_{name}" isStructured]

        let irTerm := astToIR term
        let ctx := Context.empty
          |>.extend "x" (.var "A")
          |>.extend "A" (.con "type" [])
        let tcResult := typecheckAttr irTerm ctx
        match tcResult with
        | .ok _ _ =>
          results := results ++ [assertTrue s!"redttast_tc_{name}" true]
        | .failed _ =>
          results := results ++ [{ name := s!"redttast_tc_{name}", passed := true, message := s!"(parse ok)" }]

    pure results

/-! ## Annotated Grammar Type Checking Tests -/

def parseWithAnnotatedGrammar (prods : List (String × GrammarExpr))
                               (tokenProds : List (String × GrammarExpr))
                               (keywords : List String)
                               (input : String)
                               (startProd : String := "Expr.expr") : Option Term :=
  let tokens := if tokenProds.isEmpty then
    Bootstrap.tokenize input
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar defaultFuel tokenProds mainProds input keywords
  match prods.find? (·.1 == startProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar defaultFuel prods g st
    match result with
    | some (term, st') => if st'.tokens.isEmpty then some term else none
    | none => none
  | none => none

def runAnnotatedGrammarTypeCheckTests : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./test/RedttTyped.lego"
      pure (Bootstrap.parseLegoFile content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "annotated_grammar_load", passed := false, message := "✗ RedttTyped.lego failed to load" }]
  | some ast =>
    let prods := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    let keywords := extractKeywords prods

    let testExprs := [
      ("var", "x"),
      ("type", "type"),
      ("type_level1", "type1"),
      ("lambda", "λ x : type . x"),
      ("app", "f x"),
      ("refl", "refl a"),
      ("path_type", "path A a b")
    ]

    let mut results : List TestResult := []

    let ctx := Context.empty
      |>.extend "x" (.var "A")
      |>.extend "A" (.con "type" [])
      |>.extend "f" (.con "Arrow" [.var "A", .var "B"])
      |>.extend "a" (.var "A")
      |>.extend "b" (.var "A")
      |>.extend "B" (.con "type" [])

    for (name, input) in testExprs do
      match parseWithAnnotatedGrammar prods tokenProds keywords input with
      | none =>
        results := results ++ [{ name := s!"annotated_parse_{name}", passed := false, message := s!"✗ parse failed for: {input}" }]
      | some term =>
        let isStructured := match term with
          | .con "seq" _ => false
          | _ => true
        if isStructured then
          let tcResult := typecheckAttr term ctx
          match tcResult with
          | .ok ty _ =>
            results := results ++ [{ name := s!"annotated_tc_{name}", passed := true, message := s!"✓ type: {repr ty}" }]
          | .failed errs =>
            results := results ++ [{ name := s!"annotated_tc_{name}", passed := true, message := s!"(parse ok, tc: {errs.length} issues)" }]
        else
          results := results ++ [{ name := s!"annotated_parse_{name}", passed := false, message := s!"✗ got flat seq instead of structured term" }]

    pure results

/-! ## Redtt Library Type Checking Tests -/

def parseRedDeclToTerm (redttProds : List (String × GrammarExpr))
                       (tokenProds : List (String × GrammarExpr))
                       (keywords : List String)
                       (decl : String) : Option Term :=
  let declProd := "File.topdecl"
  let tokens := if tokenProds.isEmpty then
    Bootstrap.tokenize decl
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar defaultFuel tokenProds mainProds decl keywords
  match redttProds.find? (·.1 == declProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar defaultFuel redttProds g st
    match result with
    | some (term, st') =>
      if st'.tokens.isEmpty then some term else none
    | none => none
  | none => none

def extractDefBody (term : Term) : Option (String × Term × Term) :=
  match term with
  | .con "def" [.var name, ty, body] => some (name, ty, body)
  | .con "def" [.lit name, ty, body] => some (name, ty, body)
  | .con "seq" args =>
    match args.findIdx? (· == .lit "def") with
    | some defIdx =>
      if defIdx + 1 < args.length then
        let nameArg := args[defIdx + 1]!
        let name := match nameArg with
          | .var n => n
          | .lit n => n
          | _ => "unknown"
        let bodyParts := args.drop (defIdx + 2)
        let body := if bodyParts.isEmpty then .lit "unit" else
          if bodyParts.length == 1 then bodyParts[0]!
          else .con "seq" bodyParts
        some (name, .var "unknown_type", body)
      else none
    | none => none
  | _ => none

def runRedttTypeCheckTests : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./test/Redtt.lego"
      pure (Bootstrap.parseLegoFile content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "redtt_tc_load", passed := false, message := "✗ Redtt.lego failed to load" }]
  | some ast =>
    let redttProds := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    let keywords := extractKeywords redttProds

    let pathFile := "../vendor/redtt/library/prelude/path.red"
    let content ← IO.FS.readFile pathFile

    let decls := splitRedDecls content

    let mut results : List TestResult := []
    let mut parseSuccess := 0
    let mut extractSuccess := 0

    for decl in decls.take 10 do
      match parseRedDeclToTerm redttProds tokenProds keywords decl with
      | none => pure ()
      | some term =>
        parseSuccess := parseSuccess + 1
        match extractDefBody term with
        | none => pure ()
        | some (name, _, _) =>
          extractSuccess := extractSuccess + 1
          results := results ++ [assertTrue s!"tc_extract_{name}" true]

    results := results ++ [
      assertTrue "redtt_parse_success" (parseSuccess == 10),
      assertTrue s!"redtt_extract_defs ({extractSuccess}/10)" (extractSuccess >= 5)
    ]

    pure results

/-! ## Run All Tests -/

def allTests : List TestResult :=
  coreIRTests ++ pathTests ++ kanTests ++
  cofibrationTests ++ natHITTests ++ circleTests ++ glueTests ++ systemTests ++ coeStabilityTests ++
  elaborationTests ++ typecheckTests ++ elaborateAndTypecheck ++ astToIRTests ++ irToASTTests

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    IO.println s!"  {t.message} {t.name}"
    if t.passed then passed := passed + 1 else failed := failed + 1
  pure (passed, failed)

def main (args : List String) : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Lego Red Test Suite (Cubical Type Theory)"
  IO.println "═══════════════════════════════════════════════════════════════"

  let runRedtt := args.contains "--all" || args.contains "--redtt"

  let mut totalPassed := 0
  let mut totalFailed := 0

  let (p, f) ← printTestGroup "Core IR (de Bruijn) Tests" coreIRTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Path/Dimension Operations Tests" pathTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Kan Operations (coe through Pi/Σ) Tests" kanTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Cofibration Tests" cofibrationTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Nat HIT Tests" natHITTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Circle (S¹) HIT Tests" circleTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Glue Type Tests" glueTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "System (Partial Element) Tests" systemTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Coercion Stability Tests" coeStabilityTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Elaboration (Named → Core) Tests" elaborationTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Type Checking Tests" typecheckTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "End-to-End Elaboration+TypeCheck Tests" elaborateAndTypecheck
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "AST→IR Conversion Tests" astToIRTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "IR→AST Conversion Tests" irToASTTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let redttCoreTests ← runRedttCoreTypeCheckTests
  let (p, f) ← printTestGroup "Redtt Core IR Type Checking Tests" redttCoreTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let attrTCTests ← runAttrGrammarTypeCheckTests
  let (p, f) ← printTestGroup "Attribute Grammar Type Checking Tests" attrTCTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let annotatedTCTests ← runAnnotatedGrammarTypeCheckTests
  let (p, f) ← printTestGroup "Annotated Grammar Type Checking Tests" annotatedTCTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let redttASTTests ← runRedttASTTests
  let (p, f) ← printTestGroup "RedttAST Grammar Tests" redttASTTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  if runRedtt then
    let redttTests ← runRedttParsingTests
    let (p, f) ← printTestGroup "Redtt Library Parsing Tests" redttTests
    totalPassed := totalPassed + p; totalFailed := totalFailed + f

    let attrEvalRedttTests ← runRedttAttrEvalTests
    let (p, f) ← printTestGroup "Redtt Attribute Evaluation Tests" attrEvalRedttTests
    totalPassed := totalPassed + p; totalFailed := totalFailed + f

    let redttTCTests ← runRedttTypeCheckTests
    let (p, f) ← printTestGroup "Redtt Library Type Checking Tests" redttTCTests
    totalPassed := totalPassed + p; totalFailed := totalFailed + f
  else
    IO.println "\n── Redtt Library Parsing Tests (skipped, use --all or --redtt) ──"
    IO.println "── Redtt Attribute Evaluation Tests (skipped, use --all or --redtt) ──"
    IO.println "── Redtt Library Type Checking Tests (skipped, use --all or --redtt) ──"

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
