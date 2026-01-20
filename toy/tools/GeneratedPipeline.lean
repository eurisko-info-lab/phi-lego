/-
  GeneratedPipeline: Convert generated/*.lego to .lean files

  Uses the proper Lego approach:
  1. Parse with Bootstrap grammar (via Runtime)
  2. Transform AST (rules → Lean functions)
  3. Print using Lean grammar
-/

import Lego.Runtime
import Lego.Loader

namespace GeneratedPipeline

open Lego

/-! ## Rule Extraction -/

/-- Extract rules from parsed AST -/
partial def extractRules (t : Term) : List Rule :=
  Loader.extractRules t

/-! ## Lean Code Generation -/

/-- Convert a Term pattern to Lean pattern syntax -/
partial def termToLeanPattern (t : Term) : String :=
  match t with
  | .var x => x
  | .lit s => s
  | .con name args =>
    if args.isEmpty then s!".{name}"
    else s!".{name} {" ".intercalate (args.map termToLeanPattern)}"

/-- Convert a Term template to Lean expression syntax -/
partial def termToLeanExpr (t : Term) : String :=
  match t with
  | .var x => x
  | .lit s => s
  | .con name args =>
    if args.isEmpty then name
    else s!"({name} {" ".intercalate (args.map termToLeanExpr)})"

/-- Group rules by their function name (first constructor in pattern) -/
def groupRulesByFunction (rules : List Rule) : List (String × List Rule) :=
  let funcs := rules.filterMap fun r =>
    match r.pattern with
    | .con name _ => some name
    | _ => none
  let uniqueFuncs := funcs.eraseDups
  uniqueFuncs.map fun fn =>
    (fn, rules.filter fun r =>
      match r.pattern with
      | .con name _ => name == fn
      | _ => false)

/-- Generate a Lean function from grouped rules -/
def generateFunction (funcName : String) (rules : List Rule) : String :=
  let cases := rules.map fun r =>
    match r.pattern with
    | .con _ args =>
      let pats := args.map termToLeanPattern
      let body := termToLeanExpr r.template
      s!"  | {", ".intercalate pats} => {body}"
    | _ => s!"  | _ => sorry -- {r.name}"
  let header := s!"/-- {funcName} -/\ndef {funcName} : Expr → Expr"
  let defaultCase := "  | e => e"
  s!"{header}\n{"\n".intercalate cases}\n{defaultCase}"

/-- Generate Lean module from rules -/
def generateLean (langName : String) (rules : List Rule) : String :=
  let header := s!"/-
  Lego.Cubical.{langName}: Generated from {langName}.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline {langName}.lego
-/

import Lego.Cubical.Core

namespace Lego.Cubical.{langName}

open Lego.Core
open Lego.Core.Expr
"

  let grouped := groupRulesByFunction rules
  let functions := grouped.map fun (fn, rs) => generateFunction fn rs

  let footer := s!"
end Lego.Cubical.{langName}
"

  header ++ "\n".intercalate functions ++ footer

/-! ## Pipeline -/

/-- Process a .lego file -/
def processFile (rt : Runtime.Runtime) (path : String) : IO String := do
  let content ← IO.FS.readFile path
  match Runtime.parseLegoFileE rt content with
  | .error e => throw (IO.userError s!"Failed to parse {path}: {e}")
  | .ok ast =>
    let rules := extractRules ast
    let langName := path.splitOn "/" |>.getLast! |>.dropRight 5  -- remove .lego
    return generateLean langName rules

end GeneratedPipeline

/-! ## Main -/

def main (args : List String) : IO UInt32 := do
  -- Load Bootstrap grammar
  let rt ← Lego.Runtime.loadBootstrapOrError "./test/Bootstrap.lego"

  match args with
  | [] =>
    IO.println "Usage: generated-pipeline <file.lego> [output.lean]"
    IO.println "       generated-pipeline --all"
    return 1
  | ["--all"] =>
    let dir := "./src/Lego/Cubical/generated"
    let entries ← System.FilePath.readDir dir
    let legoFiles := entries.filter (·.fileName.endsWith ".lego")
    IO.FS.createDirAll "./src/Lego/Cubical/gen"
    for entry in legoFiles do
      let inPath := s!"{dir}/{entry.fileName}"
      let outName := entry.fileName.dropRight 5 ++ ".lean"
      let outPath := s!"./src/Lego/Cubical/gen/{outName}"
      IO.println s!"Processing {entry.fileName}..."
      try
        let result ← GeneratedPipeline.processFile rt inPath
        IO.FS.writeFile outPath result
        IO.println s!"  → {outPath}"
      catch e =>
        IO.println s!"  ERROR: {e}"
    return 0
  | [inPath] =>
    let result ← GeneratedPipeline.processFile rt inPath
    IO.println result
    return 0
  | [inPath, outPath] =>
    let result ← GeneratedPipeline.processFile rt inPath
    IO.FS.writeFile outPath result
    IO.println s!"Generated: {outPath}"
    return 0
  | _ =>
    IO.println "Too many arguments"
    return 1
