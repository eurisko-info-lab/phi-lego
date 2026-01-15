/-
  Test: Runnable tests for Lego

  Tests core functionality and parses .lego files.
  Run with: lake exe lego-test
-/

import Lego
import Lego.Bootstrap

open Lego

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

/-! ## Term Construction Tests -/

def termTests : List TestResult := [
  -- Basic terms
  assertEq "term_var" (Term.var "x") (Term.var "x"),
  assertEq "term_lit" (Term.lit "42") (Term.lit "42"),
  assertEq "term_con" (Term.con "app" [Term.var "f", Term.var "x"])
                      (Term.con "app" [Term.var "f", Term.var "x"]),

  -- Nested terms
  let lam_id := Term.con "lam" [Term.var "x", Term.var "x"]
  assertEq "term_lam_id" lam_id (Term.con "lam" [Term.var "x", Term.var "x"]),

  -- Church zero as term
  let zero := Term.con "lam" [Term.var "f", Term.con "lam" [Term.var "x", Term.var "x"]]
  assertTrue "term_church_zero" (zero.toString.length > 0)
]

/-! ## Iso Tests -/

def isoTests : List TestResult :=
  -- Identity
  let idR : Iso Nat Nat := Iso.id
  let idFwd := idR.forward 42
  let idBwd := idR.backward 42

  -- Composition
  let addOne : Iso Nat Nat := {
    forward := fun n => some (n + 1)
    backward := fun n => if n > 0 then some (n - 1) else none
  }
  let doubled := addOne >>> addOne
  let dblFwd := doubled.forward 5
  let dblBwd := doubled.backward 7

  -- Symmetric
  let sym_addOne := ~addOne
  let symFwd := sym_addOne.forward 5
  let symBwd := sym_addOne.backward 5

  [
    assertEq "iso_id_forward" idFwd (some 42),
    assertEq "iso_id_backward" idBwd (some 42),
    assertEq "iso_comp_forward" dblFwd (some 7),
    assertEq "iso_comp_backward" dblBwd (some 5),
    assertEq "iso_sym_forward" symFwd (some 4),
    assertEq "iso_sym_backward" symBwd (some 6)
  ]

/-! ## Pattern Matching Tests -/

def matchTests : List TestResult :=
  -- Simple variable pattern
  let pat1 := Term.var "$x"
  let term1 := Term.lit "hello"
  let result1 := Term.matchPattern pat1 term1

  -- Constructor pattern
  let pat2 := Term.con "app" [Term.var "$f", Term.var "$x"]
  let term2 := Term.con "app" [Term.var "add", Term.lit "1"]
  let result2 := Term.matchPattern pat2 term2

  -- Nested pattern
  let pat3 := Term.con "lam" [Term.var "$x", Term.con "app" [Term.var "$f", Term.var "$x"]]
  let term3 := Term.con "lam" [Term.var "y", Term.con "app" [Term.var "inc", Term.var "y"]]
  let result3 := Term.matchPattern pat3 term3

  -- Failed match
  let pat4 := Term.con "lam" [Term.var "$x", Term.var "$body"]
  let term4 := Term.con "app" [Term.var "f", Term.var "x"]
  let result4 := Term.matchPattern pat4 term4

  [
    assertTrue "match_var" result1.isSome,
    assertTrue "match_con" result2.isSome,
    assertTrue "match_nested" result3.isSome,
    assertTrue "match_fail" result4.isNone
  ]

/-! ## Substitution Tests -/

def substTests : List TestResult :=
  -- Simple substitution
  let env1 : List (String × Term) := [("$x", Term.lit "42")]
  let template1 := Term.var "$x"
  let result1 := Term.substitute template1 env1

  -- Substitution in constructor
  let env2 := [("$f", Term.var "add"), ("$x", Term.lit "1")]
  let template2 := Term.con "app" [Term.var "$f", Term.var "$x"]
  let result2 := Term.substitute template2 env2

  -- Nested substitution
  let env3 := [("$x", Term.var "y"), ("$body", Term.var "y")]
  let template3 := Term.con "lam" [Term.var "$x", Term.var "$body"]
  let result3 := Term.substitute template3 env3

  [
    assertEq "subst_simple" result1 (Term.lit "42"),
    assertEq "subst_con" result2 (Term.con "app" [Term.var "add", Term.lit "1"]),
    assertEq "subst_nested" result3 (Term.con "lam" [Term.var "y", Term.var "y"])
  ]

/-! ## Rule Application Tests -/

def ruleTests : List TestResult :=
  -- Beta reduction rule
  let betaRule : Rule := {
    name := "beta"
    pattern := Term.con "app" [Term.con "lam" [Term.var "$x", Term.var "$body"], Term.var "$arg"]
    template := Term.con "subst" [Term.var "$x", Term.var "$arg", Term.var "$body"]
  }

  -- Apply beta to (λx.x) y
  let term := Term.con "app" [Term.con "lam" [Term.var "x", Term.var "x"], Term.var "y"]
  let result := betaRule.apply term

  -- Expected: (subst x y x)
  let expected := Term.con "subst" [Term.var "x", Term.var "y", Term.var "x"]

  -- Eta rule: λx.(f x) → f
  let etaRule : Rule := {
    name := "eta"
    pattern := Term.con "lam" [Term.var "$x", Term.con "app" [Term.var "$f", Term.var "$x"]]
    template := Term.var "$f"
  }
  let term2 := Term.con "lam" [Term.var "x", Term.con "app" [Term.var "inc", Term.var "x"]]
  let result2 := etaRule.apply term2

  [
    assertTrue "rule_beta" result.isSome,
    assertEq "rule_beta_result" result (some expected),
    assertEq "rule_eta" result2 (some (Term.var "inc"))
  ]

/-! ## Lambda Calculus Language Tests -/

/-! ## Interpreter Tests (Reduction) -/

def interpreterTests : List TestResult :=
  -- Lambda: identity function
  let id_term := Term.con "lam" [Term.var "x", Term.var "x"]

  -- Lambda: application of identity
  let app_id := Term.con "app" [
    Term.con "lam" [Term.var "x", Term.var "x"],
    Term.var "y"
  ]
  let betaRule : Rule := {
    name := "beta"
    pattern := Term.con "app" [Term.con "lam" [Term.var "$x", Term.var "$body"], Term.var "$arg"]
    template := Term.con "subst" [Term.var "$x", Term.var "$arg", Term.var "$body"]
  }
  let step1 := betaRule.apply app_id

  -- INet: Wire symmetry
  let wire := Term.con "wire" [Term.con "Port" [Term.var "a"], Term.con "Port" [Term.var "b"]]

  -- Meta: KSeq identity
  let kseq := Term.con "KSeq" [Term.con "KEmpty" [], Term.var "g"]
  let seqIdRule : Rule := {
    name := "seq_id_left"
    pattern := Term.con "KSeq" [Term.con "KEmpty" [], Term.var "$g"]
    template := Term.var "$g"
  }
  let kseqResult := seqIdRule.apply kseq

  [
    assertTrue "interp_id_term" (id_term.toString.length > 0),
    assertTrue "interp_beta_step" step1.isSome,
    assertTrue "interp_wire" (wire.toString.length > 0),
    assertEq "interp_kseq_id" kseqResult (some (Term.var "g"))
  ]

/-! ## Nat (Church Numerals) Tests -/

def natTests : List TestResult :=
  -- Church zero: λf.λx.x
  let zero := Term.con "lam" [Term.var "f",
                Term.con "lam" [Term.var "x", Term.var "x"]]

  -- Church one: λf.λx.(f x)
  let one := Term.con "lam" [Term.var "f",
               Term.con "lam" [Term.var "x",
                 Term.con "app" [Term.var "f", Term.var "x"]]]

  -- Church two: λf.λx.(f (f x))
  let two := Term.con "lam" [Term.var "f",
               Term.con "lam" [Term.var "x",
                 Term.con "app" [Term.var "f",
                   Term.con "app" [Term.var "f", Term.var "x"]]]]

  -- Successor function: λn.λf.λx.(f (n f x))
  let succ := Term.con "lam" [Term.var "n",
                Term.con "lam" [Term.var "f",
                  Term.con "lam" [Term.var "x",
                    Term.con "app" [Term.var "f",
                      Term.con "app" [Term.con "app" [Term.var "n", Term.var "f"], Term.var "x"]]]]]

  -- Addition: λm.λn.λf.λx.(m f (n f x))
  let add := Term.con "lam" [Term.var "m",
               Term.con "lam" [Term.var "n",
                 Term.con "lam" [Term.var "f",
                   Term.con "lam" [Term.var "x",
                     Term.con "app" [Term.con "app" [Term.var "m", Term.var "f"],
                       Term.con "app" [Term.con "app" [Term.var "n", Term.var "f"], Term.var "x"]]]]]]

  [
    assertTrue "nat_zero" (zero.toString.length > 0),
    assertTrue "nat_one" (one.toString.length > 0),
    assertTrue "nat_two" (two.toString.length > 0),
    assertTrue "nat_succ" (succ.toString.length > 0),
    assertTrue "nat_add" (add.toString.length > 0)
  ]

/-! ## Let/Letrec Tests -/

def letTests : List TestResult :=
  -- Let expression: (let x e body)
  let letExpr := Term.con "let" [Term.var "x", Term.lit "42", Term.var "x"]

  -- Letrec for factorial (structure only)
  let factDef := Term.con "letrec" [
    Term.var "fact",
    Term.con "lam" [Term.var "n",
      Term.con "if" [
        Term.con "isZero" [Term.var "n"],
        Term.lit "1",
        Term.con "mul" [Term.var "n",
          Term.con "app" [Term.var "fact",
            Term.con "pred" [Term.var "n"]]]]],
    Term.con "app" [Term.var "fact", Term.lit "5"]
  ]

  -- Fibonacci definition (structure only)
  let fibDef := Term.con "letrec" [
    Term.var "fib",
    Term.con "lam" [Term.var "n",
      Term.con "if" [
        Term.con "leq" [Term.var "n", Term.lit "1"],
        Term.var "n",
        Term.con "add" [
          Term.con "app" [Term.var "fib", Term.con "sub" [Term.var "n", Term.lit "1"]],
          Term.con "app" [Term.var "fib", Term.con "sub" [Term.var "n", Term.lit "2"]]]]],
    Term.con "app" [Term.var "fib", Term.lit "10"]
  ]

  [
    assertTrue "let_expr" (letExpr.toString.length > 0),
    assertTrue "letrec_fact" (factDef.toString.length > 0),
    assertTrue "letrec_fib" (fibDef.toString.length > 0)
  ]

/-! ## .lego File Parsing Tests (IO) -/

/-! ## AST to Rule/Test Conversion -/

/-- Get identifier name from (ident name) node -/
def getIdentName (t : Term) : Option String :=
  match t with
  | .con "ident" [.lit n] => some n
  | .con "ident" [.var n] => some n
  | _ => none

/-- Filter out paren literals from args -/
def filterParens (args : List Term) : List Term :=
  args.filter fun t => match t with
    | .lit "(" => false
    | .lit ")" => false
    | _ => true

/-- Convert parsed pattern AST to Term for pattern matching.
    Patterns use $x for metavariables -/
partial def patternToTerm (t : Term) : Term :=
  match t with
  -- (metavar "$" (ident x)) -> .var "$x"
  | .con "metavar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var s!"${n}"
    | none => t
  -- (pvar (ident x)) -> .var "x"
  | .con "pvar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var n
    | none => t
  | .con "plit" [.con "string" [.lit s]] => .lit s
  | .con "plit" [.lit s] => .lit s
  -- (pcon "(" (ident name) args... ")") -> .con name [args...]
  | .con "pcon" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map patternToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map patternToTerm)
  | _ => t

/-- Convert parsed template AST to Term for substitution -/
partial def templateToTerm (t : Term) : Term :=
  match t with
  -- (metavar "$" (ident x)) -> .var "$x"
  | .con "metavar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var s!"${n}"
    | none => t
  -- (tvar (ident x)) -> .var "x"
  | .con "tvar" args =>
    let idents := args.filterMap getIdentName
    match idents.head? with
    | some n => .var n
    | none => t
  | .con "tlit" [.con "string" [.lit s]] => .lit s
  | .con "tlit" [.lit s] => .lit s
  -- (tcon "(" (ident name) args... ")") -> .con name [args...]
  | .con "tcon" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map templateToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map templateToTerm)
  | _ => t

/-- Convert parsed term AST (s-expression) to simplified Term -/
partial def termAstToTerm (t : Term) : Term :=
  match t with
  -- (var (ident x)) -> .var "x"
  | .con "var" [ident] =>
    match getIdentName ident with
    | some n => .var n
    | none => t
  -- (lit (string "...")) -> .lit "..."
  | .con "lit" [.con "string" [.lit s]] => .lit s
  | .con "lit" [.lit s] => .lit s
  -- (num (number n)) -> .lit n
  | .con "num" [.con "number" [.lit n]] => .lit n
  | .con "num" [.lit n] => .lit n
  -- (con "(" (ident name) args... ")") -> .con name [args...]
  | .con "con" args =>
    let filtered := filterParens args
    match filtered with
    | ident :: rest =>
      match getIdentName ident with
      | some name => .con name (rest.map termAstToTerm)
      | none => t
    | _ => t
  | .con name args => .con name (args.map termAstToTerm)
  | _ => t

/-- Extract rules from parsed AST -/
partial def extractRules (t : Term) : List Rule :=
  match t with
  | .con "DRule" args =>
    -- DRule structure: ["rule", (ident name), ":", optional-newline, pattern, "~>", template]
    let rec findArrowIdx (xs : List Term) (idx : Nat) : Option Nat :=
      match xs with
      | [] => none
      | .lit "~>" :: _ => some idx
      | _ :: rest => findArrowIdx rest (idx + 1)
    let arrowIdx := findArrowIdx args 0
    match arrowIdx with
    | some idx =>
      if idx > 0 ∧ idx + 1 < args.length then
        let pattern := args[idx - 1]!
        let template := args[idx + 1]!
        let nameOpt := args.findSome? fun
          | .con "ident" [.lit n] => some n
          | .con "ident" [.var n] => some n
          | _ => none
        match nameOpt with
        | some name => [{ name := name, pattern := patternToTerm pattern, template := templateToTerm template }]
        | none => []
      else []
    | none => []
  | .con "seq" ts => ts.flatMap extractRules
  | .con _ ts => ts.flatMap extractRules
  | _ => []

/-- Test with expected result -/
structure EvalTest where
  name : String
  input : Term
  expected : Term
  deriving Repr

/-- Extract eval tests (tests with ~~> expected result) from parsed AST -/
partial def extractEvalTests (t : Term) : List EvalTest :=
  match t with
  | .con "DTest" args =>
    -- DTest structure: ["test", (string "name"), ":", input, optional: "~~>", expected]
    -- Find the "~~>" arrow
    let arrowIdx := args.findIdx? (· == .lit "~~>")
    match arrowIdx with
    | some idx =>
      -- input is at idx-1, expected is at idx+1
      if idx > 0 ∧ idx + 1 < args.length then
        let input := args[idx - 1]!
        let expected := args[idx + 1]!
        -- Get name from (string "name")
        let nameOpt := args.findSome? fun
          | .con "string" [.lit n] => some (n.replace "\"" "")  -- Remove quotes
          | _ => none
        match nameOpt with
        | some name => [{ name := name, input := termAstToTerm input, expected := termAstToTerm expected }]
        | none => []
      else []
    | none => []  -- No "~~>", not an eval test
  | .con "seq" ts => ts.flatMap extractEvalTests
  | .con _ ts => ts.flatMap extractEvalTests
  | _ => []

/-- Apply built-in substitution: (subst x val body)
    Works with both simple Terms (.var x) and parsed structure (Term.con "var" [Term.var "x"]) -/
partial def applySubst (x : String) (val : Term) (body : Term) : Term :=
  match body with
  -- Simple var: (var "x")
  | .var name => if name == x then val else body
  -- Parsed var structure: (var (var "x")) or similar
  | .con "var" [.var name] => if name == x then val else body
  -- Lit stays unchanged
  | .lit _ => body
  -- Recursively substitute in constructor args
  | .con name args => .con name (args.map (applySubst x val))

/-- Apply built-in reductions (like subst) -/
def stepBuiltin (t : Term) : Option Term :=
  match t with
  -- (subst x val body) where x is a var name -> apply substitution
  | .con "subst" [.var x, val, body] =>
    some (applySubst x val body)
  | _ => none

/-- Apply a single step with any matching rule -/
def stepOnce (rules : List Rule) (t : Term) : Option Term :=
  -- Try rules first
  match rules.findSome? (fun r => r.apply t) with
  | some t' => some t'
  | none => stepBuiltin t

/-- Apply rules to subterms recursively (single step) -/
partial def stepDeep (rules : List Rule) (t : Term) : Option Term :=
  -- Try at root first
  match stepOnce rules t with
  | some t' => some t'
  | none =>
    -- Try recursively in subterms
    match t with
    | .con name args =>
      -- Try each arg, return first success
      let rec tryArgs (before : List Term) (after : List Term) : Option Term :=
        match after with
        | [] => none
        | arg :: rest =>
          match stepDeep rules arg with
          | some arg' => some (.con name (before.reverse ++ [arg'] ++ rest))
          | none => tryArgs (arg :: before) rest
      tryArgs [] args
    | _ => none

/-- Normalize term by applying rules until fixpoint (with fuel) -/
partial def normalize (fuel : Nat) (rules : List Rule) (t : Term) : Term :=
  match fuel with
  | 0 => t  -- Out of fuel
  | n + 1 =>
    match stepDeep rules t with
    | some t' => normalize n rules t'
    | none => t  -- Normal form

/-- Canonicalize a term (convert parsed (var x) to simple .var "x") -/
partial def canonicalize (t : Term) : Term :=
  match t with
  | .con "var" [.var name] => .var name
  | .con name args => .con name (args.map canonicalize)
  | _ => t

/-- Compare terms for equality after canonicalization -/
def termEq (t1 t2 : Term) : Bool := canonicalize t1 == canonicalize t2

/-- Run a single eval test -/
def runEvalTest (rules : List Rule) (test : EvalTest) : TestResult :=
  let result := normalize 100 rules test.input
  let passed := termEq result test.expected
  { name := s!"eval_{test.name}"
    passed := passed
    message := if passed then "✓"
               else s!"✗ got {result}, expected {test.expected}" }

/-- Parse a .lego file and return test results -/
def parseLegoFileTest (path : String) : IO TestResult := do
  let name := path.splitOn "/" |>.getLast!
  try
    let content ← IO.FS.readFile path
    let result := Bootstrap.parseLegoFile content
    match result with
    | some _ => pure { name := s!"parse_{name}", passed := true, message := "✓" }
    | none => pure { name := s!"parse_{name}", passed := false, message := "✗ parse failed" }
  catch _ =>
    pure { name := s!"parse_{name}", passed := false, message := "✗ file not found" }

/-- Count test declarations in parsed AST -/
partial def countTests (t : Term) : Nat :=
  match t with
  | .con "DTest" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countTests t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countTests t') 0
  | _ => 0

/-- Count rule declarations in parsed AST -/
partial def countRules (t : Term) : Nat :=
  match t with
  | .con "DRule" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countRules t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countRules t') 0
  | _ => 0

/-- Count piece declarations in parsed AST -/
partial def countPieces (t : Term) : Nat :=
  match t with
  | .con "DPiece" _ => 1
  | .con "seq" ts => ts.foldl (fun acc t' => acc + countPieces t') 0
  | .con _ ts => ts.foldl (fun acc t' => acc + countPieces t') 0
  | _ => 0

/-- Parse and analyze a .lego file -/
def analyzeLegoFile (path : String) : IO (List TestResult) := do
  let name := path.splitOn "/" |>.getLast!
  try
    let content ← IO.FS.readFile path
    let result := Bootstrap.parseLegoFile content
    match result with
    | some ast =>
      let testCount := countTests ast
      let ruleCount := countRules ast
      let pieceCount := countPieces ast
      let rules := extractRules ast
      let evalTests := extractEvalTests ast
      let evalResults := evalTests.map (runEvalTest rules)
      let baseResults := [
        { name := s!"parse_{name}", passed := true, message := "✓" },
        { name := s!"{name}_has_pieces", passed := pieceCount > 0, message := if pieceCount > 0 then s!"✓ ({pieceCount})" else "✗" },
        -- Rules and tests are optional - count them but don't fail if 0
        { name := s!"{name}_has_rules", passed := true, message := s!"✓ ({ruleCount})" },
        { name := s!"{name}_has_tests", passed := true, message := s!"✓ ({testCount})" }
      ]
      pure (baseResults ++ evalResults)
    | none => pure [{ name := s!"parse_{name}", passed := false, message := "✗ parse failed" }]
  catch _ =>
    pure [{ name := s!"parse_{name}", passed := false, message := "✗ file not found" }]

/-- Run .lego file parsing tests -/
def runLegoFileTests : IO (List TestResult) := do
  -- Test files in toy/test/
  let testPath := "./test"
  let files := [
    s!"{testPath}/Lambda.lego",
    s!"{testPath}/Arith.lego",
    s!"{testPath}/INet.lego",
    s!"{testPath}/Meta.lego",
    s!"{testPath}/K.lego",
    s!"{testPath}/Bootstrap.lego"
  ]
  let mut results : List TestResult := []
  for file in files do
    let fileResults ← analyzeLegoFile file
    results := results ++ fileResults
  pure results

/-! ## Run All Tests -/

def allTests : List TestResult :=
  termTests ++ isoTests ++ matchTests ++ substTests ++
  ruleTests ++ interpreterTests ++ natTests ++ letTests

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    IO.println s!"  {t.message} {t.name}"
    if t.passed then passed := passed + 1 else failed := failed + 1
  pure (passed, failed)

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "Lego Test Suite"
  IO.println "═══════════════════════════════════════════════════════════════"

  let mut totalPassed := 0
  let mut totalFailed := 0

  let (p, f) ← printTestGroup "Term Tests" termTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Iso Tests" isoTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Pattern Matching Tests" matchTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Substitution Tests" substTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Rule Application Tests" ruleTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Interpreter Tests" interpreterTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Nat (Church Numerals) Tests" natTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  let (p, f) ← printTestGroup "Let/Letrec Tests" letTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  -- Run .lego file parsing tests (IO-based)
  let legoFileTests ← runLegoFileTests
  let (p, f) ← printTestGroup ".lego File Parsing Tests" legoFileTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
