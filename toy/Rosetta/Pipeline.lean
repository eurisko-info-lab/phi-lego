/-
  Pipeline.lean
  cubical := parse CubicalTT.lego
  lifted := run rules cubical2rosetta.lego on cubical
  lean := run rules rosetta2lean.lego on lifted
  print lean → generated/
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

/-- Check if a Term is a var -/
def Term.isVar : Term → Bool
  | .var _ => true
  | _ => false

/-- Get var name from a Term -/
def Term.getVarName : Term → Option String
  | .var name => some name
  | _ => none

/-- Pretty-print a transformed Term to Lean 4 code -/
partial def termToLean (t : Term) (indent : Nat := 0) : String :=
  let pad := String.mk (List.replicate (indent * 2) ' ')
  match t with
  | .var name => name
  | .lit s => s
  | .con "seq" children =>
    children.map (termToLean · indent) |> String.intercalate "\n\n"
  | .con "DLang" args =>
    -- Extract lang name and body
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Unknown"
    let body := args.filterMap fun t =>
      match t with
      | .con "DToken" _ => some t
      | .con "DPiece" _ => some t
      | _ => none
    s!"{pad}namespace {name}\n\n{body.map (termToLean · (indent + 1)) |> String.intercalate "\n\n"}\n\n{pad}end {name}"
  | .con "DToken" args =>
    -- Token definitions become a lexer module
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Token"
    let rules := args.filter fun t =>
      match t with | .con "inductive" _ => true | _ => false
    s!"{pad}-- Token lexer: {name}\n{rules.map (termToLean · indent) |> String.intercalate "\n"}"
  | .con "DPiece" args =>
    -- Piece definitions become sections
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "Piece"
    let contents := args.filter fun t =>
      match t with
      | .con "inductive" _ => true
      | .con "def" _ => true
      | .con "example" _ => true
      | .con "DRule" _ => true  -- Include rules
      | .con "DTest" _ => true  -- Include tests
      | _ => false
    s!"{pad}section {name}\n\n{contents.map (termToLean · (indent + 1)) |> String.intercalate "\n\n"}\n\n{pad}end {name}"
  | .con "DRule" args =>
    -- Transform DRule directly in printer
    -- Structure: [lit "rule", ident name, lit ":", pat, lit "~~>", tmpl, unit, lit ";"]
    let name := args.find? Term.isVar |>.bind Term.getVarName |>.getD "rule"
    let pat := args.find? (fun t => match t with | .con "con" _ => true | _ => false) |>.getD (.con "unit" [])
    let tmpl := args.reverse.find? (fun t => match t with | .con "con" _ => true | _ => false) |>.getD (.con "unit" [])
    s!"{pad}def {name} (t : Term) : Term :=\n{pad}  match t with\n{pad}  | {termToLean pat 0} => {termToLean tmpl 0}\n{pad}  | _ => t"
  | .con "DTest" args =>
    -- Transform DTest directly in printer
    let name := args.find? (fun t => match t with | .lit s => s.startsWith "\"" | _ => false) |>.map (fun t => match t with | .lit s => s | _ => "") |>.getD "test"
    let body := args.find? (fun t => match t with | .con "con" _ => true | _ => false) |>.getD (.con "unit" [])
    s!"{pad}-- Test: {name}\n{pad}-- {termToLean body 0}"
  | .con "inductive" [.var name, body] =>
    s!"{pad}def {name} : Parser :=\n{pad}  {termToLean body 0}"
  | .con "inductive" args =>
    let name := args.head?.map (termToLean · 0) |>.getD "unknown"
    let body := args[1]? |>.map (termToLean · 0) |>.getD "()"
    s!"{pad}def {name} : Parser :=\n{pad}  {body}"
  | .con "choice" [left, right] =>
    s!"({termToLean left 0} <|> {termToLean right 0})"
  | .con "char" [.lit c] =>
    s!"char {c}"
  | .con "many" [inner] =>
    s!"many ({termToLean inner 0})"
  | .con "optional" [inner] =>
    s!"optional ({termToLean inner 0})"
  | .con "ref" [.var name] =>
    name
  | .con "terminal" [.lit s] =>
    s!"str {s}"
  | .con "def" [.var name, pat, tmpl] =>
    s!"{pad}def {name} : Rule :=\n{pad}  match · with\n{pad}  | {termToLean pat 0} => {termToLean tmpl 0}\n{pad}  | t => t"
  | .con "def" args =>
    let name := args.head?.map (termToLean · 0) |>.getD "unknown"
    s!"{pad}-- def {name} ..."
  | .con "example" [.lit name, body] =>
    s!"{pad}-- test {name}: {termToLean body 0}"
  | .con "app" (head :: args) =>
    s!"({termToLean head 0} {args.map (termToLean · 0) |> String.intercalate " "})"
  | .con "metavar" [.var name] =>
    s!"${name}"
  | .con "unit" [] =>
    "()"
  | .con tag args =>
    if args.isEmpty then tag
    else s!"({tag} {args.map (termToLean · 0) |> String.intercalate " "})"

def main : IO Unit := do
  -- Step 0: Initialize runtime by loading Bootstrap.lego
  let rt ← Lego.Runtime.init

  -- Load transformation rules
  let c2rContent ← IO.FS.readFile "./src/Rosetta/cubical2rosetta.lego"
  let c2rAst ← match parseLegoFileE rt c2rContent with
    | .error e => IO.eprintln s!"parse cubical2rosetta failed: {e}"; return
    | .ok ast => pure ast
  let rules1 := extractRules c2rAst

  let r2lContent ← IO.FS.readFile "./src/Rosetta/rosetta2lean.lego"
  let r2lAst ← match parseLegoFileE rt r2lContent with
    | .error e => IO.eprintln s!"parse rosetta2lean failed: {e}"; return
    | .ok ast => pure ast
  let rules2 := extractRules r2lAst

  -- Process multiple .lego files
  let files := [
    ("./test/Redtt.lego", "./generated/Cubical/Redtt.lean"),
    ("./src/Lego/Cubical/CubicalTT.lego", "./generated/Cubical/CubicalTT.lean"),
    ("./src/Lego/Cubical/Red.lego", "./generated/Cubical/Red.lean")
    -- Cool.lego has unsupported 'for' syntax in type constraints, skipped for now
  ]

  IO.FS.createDirAll "./generated/Cubical"

  for (input, output) in files do
    let content ← IO.FS.readFile input
    match parseLegoFileE rt content with
    | .error e => IO.eprintln s!"parse {input} failed: {e}"
    | .ok ast =>
      let lifted := transform rules1 ast
      let lean := transform rules2 lifted
      let leanCode := termToLean lean
      IO.FS.writeFile output leanCode
      IO.println s!"Wrote {output}"
