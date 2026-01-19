/-
  Rosetta: Generic Lego → Lean code generator

  This module transforms parsed .lego AST into Lean code.
  It is GENERIC - no domain-specific types hard-coded.
  All domain knowledge comes from the .lego grammar.

  Pipeline:
  1. Parse .lego file using Bootstrap grammar → Term AST
  2. Walk AST to extract pieces, rules, types, tests
  3. Generate Lean code from extracted data
-/

import Lego.Loader
import Lego.Bootstrap
import Lego.Algebra

namespace Rosetta

open Lego

/-! ## Rosetta IR Types

Simple intermediate representation for code generation.
No domain-specific knowledge - just generic constructs.
-/

/-- Constructor info extracted from grammar -/
structure ConstrInfo where
  name : String
  arity : Nat  -- number of arguments
  deriving Repr

/-- Rule info extracted from rules section -/
structure RuleInfo where
  name : String
  pattern : Term
  template : Term
  deriving Repr

/-- Test info extracted from tests section -/
structure TestInfo where
  name : String
  input : Term
  expected : Term
  deriving Repr

/-- Piece info extracted from AST -/
structure PieceInfo where
  name : String
  constrs : List ConstrInfo
  rules : List RuleInfo
  tests : List TestInfo
  deriving Repr

/-- Language info -/
structure LangInfo where
  name : String
  pieces : List PieceInfo
  deriving Repr

/-! ## AST Walking

Extract structured info from raw Term AST.
-/

/-- Extract string from Term -/
def getString : Term → Option String
  | .lit s => some s
  | .var s => some s
  | _ => none

/-- Extract constructor name and arity from production -/
def extractConstr (prod : Term) : Option ConstrInfo := do
  -- Production shape: (proddecl name (seq ... → conName))
  match prod with
  | .con "proddecl" [.var name, _grammar] =>
    -- Just count as arity 0 for now - would need grammar analysis
    some { name := name, arity := 0 }
  | _ => none

/-- Extract rule info -/
def extractRule (rule : Term) : Option RuleInfo := do
  match rule with
  | .con "rule" [.var name, pattern, template] =>
    some { name := name, pattern := pattern, template := template }
  | .con "rule" [.var name, pattern, template, _cond] =>
    some { name := name, pattern := pattern, template := template }
  | _ => none

/-- Extract test info -/
def extractTest (test : Term) : Option TestInfo := do
  match test with
  | .con "test" [.lit name, input, expected] =>
    some { name := name, input := input, expected := expected }
  | _ => none

/-- Extract piece from AST -/
partial def extractPiece (piece : Term) : Option PieceInfo := do
  match piece with
  | .con "piece" args =>
    let name ← args.head?.bind getString
    let constrs := args.filterMap extractConstr
    let rules := args.filterMap extractRule
    let tests := args.filterMap extractTest
    some { name := name, constrs := constrs, rules := rules, tests := tests }
  | _ => none

/-- Extract all pieces from language AST -/
partial def extractLang (ast : Term) : Option LangInfo := do
  match ast with
  | .con "lang" args =>
    let name ← args.head?.bind getString
    let pieces := args.filterMap extractPiece
    some { name := name, pieces := pieces }
  | .con "file" args =>
    -- Try to find lang inside file
    for arg in args do
      if let some info := extractLang arg then
        return info
    none
  | _ => none

/-! ## Lean Code Generation -/

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  match s.toList with
  | [] => s
  | c :: cs => String.mk (c.toUpper :: cs)

/-- Generate Lean term from Lego Term -/
partial def termToLean : Term → String
  | .var s => s
  | .lit s => s!"\"{s}\""
  | .con name [] => capitalize name
  | .con name args =>
    let argsStr := args.map termToLean |>.intersperse " " |> String.join
    s!"({capitalize name} {argsStr})"

/-- Generate rule as Lean match case -/
def ruleToLean (rule : RuleInfo) : String :=
  s!"  -- {rule.name}\n  | {termToLean rule.pattern} => some {termToLean rule.template}"

/-- Generate test as Lean example -/
def testToLean (test : TestInfo) : String :=
  s!"/-- {test.name} -/\nexample : step {termToLean test.input} = some {termToLean test.expected} := rfl"

/-- Generate piece as Lean namespace -/
def pieceToLean (langName : String) (piece : PieceInfo) : String :=
  let header := s!"/-
  {langName}.{piece.name}
  Generated from {langName}.lego via Rosetta pipeline
-/

namespace {langName}.{piece.name}

"
  let rules := if piece.rules.isEmpty then "" else
    let cases := piece.rules.map ruleToLean |>.intersperse "\n" |> String.join
    s!"/-! ## Reduction Rules -/

def step : Term → Option Term
{cases}
  | _ => none

"
  let tests := if piece.tests.isEmpty then "" else
    let testStrs := piece.tests.map testToLean |>.intersperse "\n\n" |> String.join
    s!"/-! ## Tests -/

{testStrs}

"
  header ++ rules ++ tests ++ s!"end {langName}.{piece.name}\n"

/-- Generate language index file -/
def langIndexToLean (info : LangInfo) : String :=
  let imports := info.pieces.map (fun p => s!"import {info.name}.{p.name}")
                   |>.intersperse "\n" |> String.join
  s!"/-
  {info.name} - Generated from {info.name}.lego via Rosetta pipeline
-/

{imports}

namespace {info.name}

-- Re-exports

end {info.name}
"

/-! ## Main Entry Point -/

/-- Parse and generate Lean from a .lego file -/
def generateFromFile (path : String) : IO (Option String) := do
  let content ← IO.FS.readFile path
  match Bootstrap.parseLegoFile content with
  | some ast =>
    match extractLang ast with
    | some info =>
      -- Generate index file
      return some (langIndexToLean info)
    | none =>
      IO.eprintln s!"Could not extract language structure from {path}"
      return none
  | none =>
    IO.eprintln s!"Failed to parse {path}"
    return none

/-- Generate all piece files -/
def generatePieceFiles (path : String) (outDir : String) : IO Bool := do
  let content ← IO.FS.readFile path
  match Bootstrap.parseLegoFile content with
  | some ast =>
    match extractLang ast with
    | some info =>
      for piece in info.pieces do
        let pieceCode := pieceToLean info.name piece
        let outPath := s!"{outDir}/{piece.name}.lean"
        IO.FS.writeFile outPath pieceCode
        IO.println s!"Generated {outPath}"
      -- Generate index
      let indexPath := s!"{outDir}/{info.name}.lean"
      IO.FS.writeFile indexPath (langIndexToLean info)
      IO.println s!"Generated {indexPath}"
      return true
    | none =>
      IO.eprintln s!"Could not extract language structure"
      return false
  | none =>
    IO.eprintln s!"Failed to parse {path}"
    return false

end Rosetta
