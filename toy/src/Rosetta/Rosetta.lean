/-
  Rosetta: Lego → Lean code generator

  This module implements the Rosetta pipeline that transforms
  .lego specifications into executable Lean code.

  Pipeline:
  1. Parse .lego file using Bootstrap grammar
  2. Transform to Rosetta IR (abstract primitives)
  3. Generate Lean code from Rosetta IR
-/

import Lego.Loader
import Lego.Grammar

namespace Rosetta

open Lego

/-! ## Rosetta IR Types -/

/-- Abstract term in Rosetta IR -/
inductive RosettaTerm where
  | Var (name : String) : RosettaTerm
  | App (f : RosettaTerm) (args : List RosettaTerm) : RosettaTerm
  | Lam (x : String) (body : RosettaTerm) : RosettaTerm
  | Const (lit : String) : RosettaTerm
  | Pair (a b : RosettaTerm) : RosettaTerm
  | Fst (t : RosettaTerm) : RosettaTerm
  | Snd (t : RosettaTerm) : RosettaTerm
  | Subst (x : String) (v body : RosettaTerm) : RosettaTerm
  deriving Repr

/-- ADT definition -/
structure AdtDef where
  name : String
  constrs : List (String × String)  -- (constructor name, type)
  deriving Repr

/-- Rewrite rule -/
structure RewriteRule where
  name : String
  lhs : RosettaTerm
  rhs : RosettaTerm
  deriving Repr

/-- Judgment declaration -/
structure JudgeDecl where
  name : String
  term : RosettaTerm
  tp : RosettaTerm
  conditions : List (RosettaTerm × RosettaTerm)
  deriving Repr

/-- Test declaration -/
structure TestDecl where
  name : String
  lhs : RosettaTerm
  rhs : RosettaTerm
  deriving Repr

/-- Module (from piece) -/
structure ModuleDecl where
  name : String
  adts : List AdtDef
  rules : List RewriteRule
  judges : List JudgeDecl
  tests : List TestDecl
  deriving Repr

/-- Complete language spec -/
structure LangSpec where
  name : String
  modules : List ModuleDecl
  deriving Repr

/-! ## Lego → Rosetta Transformation -/

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  match s.data with
  | [] => s
  | c :: cs => ⟨c.toUpper :: cs⟩

/-- Transform Lego term to Rosetta -/
partial def termToRosetta (ctx : String) : Term → RosettaTerm
  | Term.Sym s => RosettaTerm.Var s
  | Term.Lit s => RosettaTerm.Const s
  | Term.App (Term.Sym "lam") [Term.Sym x, body] =>
    RosettaTerm.Lam x (termToRosetta ctx body)
  | Term.App (Term.Sym "fst") [t] =>
    RosettaTerm.Fst (termToRosetta ctx t)
  | Term.App (Term.Sym "snd") [t] =>
    RosettaTerm.Snd (termToRosetta ctx t)
  | Term.App (Term.Sym "pair") [a, b] =>
    RosettaTerm.Pair (termToRosetta ctx a) (termToRosetta ctx b)
  | Term.App (Term.Sym "subst") [Term.Sym x, v, body] =>
    RosettaTerm.Subst x (termToRosetta ctx v) (termToRosetta ctx body)
  | Term.App f args =>
    RosettaTerm.App (termToRosetta ctx f) (args.map (termToRosetta ctx))
  | Term.List ts =>
    -- Represent as nested pairs
    ts.foldr (fun t acc => RosettaTerm.Pair (termToRosetta ctx t) acc)
             (RosettaTerm.Const "nil")

/-- Transform production to ADT constructor -/
def prodToConstr (prod : ProdRule) : String × String :=
  (capitalize prod.name, "Term")  -- Simplified: all constructors return Term

/-- Transform grammar to ADT -/
def grammarToAdt (pieceName : String) (prods : List ProdRule) : AdtDef :=
  { name := pieceName ++ "Term"
    constrs := prods.map prodToConstr }

/-- Transform rule to RewriteRule -/
def ruleToRewrite (pieceName : String) (rule : RuleDecl) : RewriteRule :=
  { name := pieceName ++ "_" ++ rule.name
    lhs := termToRosetta pieceName rule.lhs
    rhs := termToRosetta pieceName rule.rhs }

/-- Transform type to JudgeDecl -/
def typeToJudge (pieceName : String) (td : TypeDecl) : JudgeDecl :=
  { name := pieceName ++ "_" ++ td.name
    term := termToRosetta pieceName td.term
    tp := termToRosetta pieceName td.tp
    conditions := td.conditions.map fun (l, r) =>
      (termToRosetta pieceName l, termToRosetta pieceName r) }

/-- Transform test to TestDecl -/
def testToTest (pieceName : String) (test : TestDecl) : Rosetta.TestDecl :=
  { name := pieceName ++ "_" ++ test.name
    lhs := termToRosetta pieceName test.lhs
    rhs := termToRosetta pieceName test.rhs }

/-- Transform piece to module -/
def pieceToModule (piece : Piece) : ModuleDecl :=
  { name := piece.name
    adts := [grammarToAdt piece.name piece.prods]
    rules := piece.rules.map (ruleToRewrite piece.name)
    judges := piece.types.map (typeToJudge piece.name)
    tests := piece.tests.map (testToTest piece.name) }

/-- Transform language to spec -/
def langToSpec (lang : Language) : LangSpec :=
  { name := lang.name
    modules := lang.pieces.map pieceToModule }

/-! ## Rosetta → Lean Code Generation -/

/-- Generate Lean term from Rosetta -/
partial def rosettaToLean : RosettaTerm → String
  | RosettaTerm.Var name => name
  | RosettaTerm.Const lit => s!"\"{lit}\""
  | RosettaTerm.App f args =>
    let fStr := rosettaToLean f
    let argsStr := args.map rosettaToLean |>.intersperse " " |> String.join
    if args.isEmpty then fStr else s!"({fStr} {argsStr})"
  | RosettaTerm.Lam x body =>
    s!"fun {x} => {rosettaToLean body}"
  | RosettaTerm.Pair a b =>
    s!"({rosettaToLean a}, {rosettaToLean b})"
  | RosettaTerm.Fst t => s!"(Prod.fst {rosettaToLean t})"
  | RosettaTerm.Snd t => s!"(Prod.snd {rosettaToLean t})"
  | RosettaTerm.Subst x v body =>
    s!"(subst \"{x}\" {rosettaToLean v} {rosettaToLean body})"

/-- Generate Lean inductive from ADT -/
def adtToLean (adt : AdtDef) : String :=
  let constrs := adt.constrs.map fun (name, tp) =>
    s!"  | {name} : {tp}"
  s!"inductive {adt.name} where\n" ++ (constrs.intersperse "\n" |> String.join)

/-- Generate Lean def from rewrite rule -/
def ruleToLean (rule : RewriteRule) : String :=
  s!"/-- {rule.name}: {rosettaToLean rule.lhs} ~> {rosettaToLean rule.rhs} -/
def {rule.name} : Term → Option Term
  | {rosettaToLean rule.lhs} => some ({rosettaToLean rule.rhs})
  | _ => none"

/-- Generate Lean theorem from judge -/
def judgeToLean (judge : JudgeDecl) : String :=
  let conds := judge.conditions.map fun (l, r) =>
    s!"{rosettaToLean l} : {rosettaToLean r}"
  let condStr := if conds.isEmpty then "" else
    s!" when {conds.intersperse ", " |> String.join}"
  s!"/-- {judge.name}: {rosettaToLean judge.term} : {rosettaToLean judge.tp}{condStr} -/
axiom {judge.name} : True  -- placeholder"

/-- Generate Lean example from test -/
def testToLean (test : Rosetta.TestDecl) : String :=
  s!"/-- {test.name} -/
example : reduce {rosettaToLean test.lhs} = {rosettaToLean test.rhs} := sorry"

/-- Generate Lean module from ModuleDecl -/
def moduleToLean (mod : ModuleDecl) : String :=
  let header := s!"/-
  {mod.name} - Generated from .lego via Rosetta pipeline
-/

namespace {mod.name}

"
  let adts := mod.adts.map adtToLean |>.intersperse "\n\n" |> String.join
  let rules := mod.rules.map ruleToLean |>.intersperse "\n\n" |> String.join
  let judges := mod.judges.map judgeToLean |>.intersperse "\n\n" |> String.join
  let tests := mod.tests.map testToLean |>.intersperse "\n\n" |> String.join

  header ++
  (if adts.isEmpty then "" else "/-! ## Syntax -/\n\n" ++ adts ++ "\n\n") ++
  (if rules.isEmpty then "" else "/-! ## Reduction Rules -/\n\n" ++ rules ++ "\n\n") ++
  (if judges.isEmpty then "" else "/-! ## Typing Rules -/\n\n" ++ judges ++ "\n\n") ++
  (if tests.isEmpty then "" else "/-! ## Tests -/\n\n" ++ tests ++ "\n\n") ++
  s!"end {mod.name}\n"

/-- Generate Lean file from LangSpec -/
def langToLean (spec : LangSpec) : String :=
  let header := s!"/-
  {spec.name} - Generated from {spec.name}.lego via Rosetta pipeline
-/

"
  let imports := spec.modules.map (fun m => s!"import {spec.name}.{m.name}")
                   |>.intersperse "\n" |> String.join
  let modules := spec.modules.map moduleToLean
                   |>.intersperse "\n" |> String.join

  header ++ imports ++ "\n\n" ++ modules

/-! ## Main Entry Point -/

/-- Generate Lean code from a .lego file -/
def generateLean (legoFile : String) : IO String := do
  let contents ← IO.FS.readFile legoFile
  match parseLego contents with
  | Except.ok lang =>
    let spec := langToSpec lang
    return langToLean spec
  | Except.error err =>
    throw (IO.userError s!"Parse error: {err}")

end Rosetta
