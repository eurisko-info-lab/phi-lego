/-
  Rosetta: Lego → Lean code generator

  This module implements the Rosetta pipeline that transforms
  .lego specifications into executable Lean code.

  Pipeline:
  1. Parse .lego file using Bootstrap grammar
  2. Transform to Rosetta IR (generic primitives)
  3. Generate Lean code from Rosetta IR

  IMPORTANT: This generator is GENERIC - no cubical-specific types.
  Domain-specific types (Dim, Cof, etc.) come from the .lego grammar,
  not hard-coded here. See Rosetta.lego for the prelude definition.
-/

import Lego.Loader
import Lego.Bootstrap

namespace Rosetta

open Lego

/-! ## Rosetta IR Types

These represent generic programming constructs that can be
translated to any target language. No domain-specific types here.
-/

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
  | Error (msg : String) : RosettaTerm
  | Loc (line col : Nat) (t : RosettaTerm) : RosettaTerm
  deriving Repr

/-- ADT constructor (from grammar production) -/
structure ConstrDef where
  name : String
  fields : List (String × String)  -- (field name, type)
  deriving Repr

/-- ADT definition (from grammar piece) -/
structure AdtDef where
  name : String
  constrs : List ConstrDef
  deriving Repr

/-- Rewrite rule -/
structure RewriteRule where
  name : String
  lhs : RosettaTerm
  rhs : RosettaTerm
  condition : Option RosettaTerm := none
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
  imports : List String := []
  deriving Repr

/-! ## Lego AST → Rosetta Transformation -/

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
  | Term.App (Term.Sym "error") [Term.Lit msg] =>
    RosettaTerm.Error msg
  | Term.App f args =>
    RosettaTerm.App (termToRosetta ctx f) (args.map (termToRosetta ctx))
  | Term.List ts =>
    -- Represent as nested pairs
    ts.foldr (fun t acc => RosettaTerm.Pair (termToRosetta ctx t) acc)
             (RosettaTerm.Const "nil")

/-- Extract constructor fields from grammar expression -/
partial def extractFields (g : GrammarExpr) : List (String × String) :=
  match g.val with
  | .seq l r => extractFields ⟨l⟩ ++ extractFields ⟨r⟩
  | .bind name inner => [(name, inferType inner)]
  | _ => []
where
  /-- Infer type from grammar reference - NO domain-specific knowledge here.
      Types come from the grammar itself, not hard-coded. -/
  inferType (g : GrammarExprF GrammarExpr) : String :=
    match g with
    | .ref name =>
      -- Use reference name as type, capitalizing if needed
      if name == "ident" || name == "TOKEN.ident" then "String"
      else if name == "string" || name == "TOKEN.string" then "String"
      else if name == "number" || name == "TOKEN.number" then "Nat"
      else if name.contains '.' then
        -- Qualified name like "Term.term" → use the production name
        capitalize (name.splitOn "." |>.getLast!)
      else
        capitalize name  -- "dim" → "Dim", "cof" → "Cof", "term" → "Term"
    | .star _ => "List Term"
    | .plus _ => "List Term"
    | _ => "Term"

/-- Transform production to ADT constructor -/
def prodToConstr (prod : ProdRule) : ConstrDef :=
  { name := capitalize prod.name
    fields := extractFields prod.expr }

/-- Transform grammar productions to ADT -/
def grammarToAdt (pieceName : String) (prods : List ProdRule) : AdtDef :=
  { name := pieceName ++ "Term"
    constrs := prods.map prodToConstr }

/-- Transform rule to RewriteRule -/
def ruleToRewrite (pieceName : String) (rule : RuleDecl) : RewriteRule :=
  { name := pieceName ++ "_" ++ rule.name
    lhs := termToRosetta pieceName rule.lhs
    rhs := termToRosetta pieceName rule.rhs
    condition := rule.condition.map (termToRosetta pieceName) }

/-- Transform type to JudgeDecl -/
def typeToJudge (pieceName : String) (td : TypeDecl) : JudgeDecl :=
  { name := pieceName ++ "_" ++ td.name
    term := termToRosetta pieceName td.term
    tp := termToRosetta pieceName td.tp
    conditions := td.conditions.map fun (l, r) =>
      (termToRosetta pieceName l, termToRosetta pieceName r) }

/-- Transform test to TestDecl -/
def testToTest (pieceName : String) (test : Lego.TestDecl) : Rosetta.TestDecl :=
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
    modules := lang.pieces.map pieceToModule
    imports := lang.imports }

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
  | RosettaTerm.Error msg => s!"(panic! \"{msg}\")"
  | RosettaTerm.Loc _ _ t => rosettaToLean t  -- Drop source locations

/-- Generate Lean type for a field - pass through as-is, no special cases -/
def fieldTypeToLean (tp : String) : String := tp

/-- Generate Lean inductive from ADT -/
def adtToLean (adt : AdtDef) : String :=
  let constrs := adt.constrs.map fun c =>
    let fieldTypes := c.fields.map (fun (_, tp) => fieldTypeToLean tp)
    if fieldTypes.isEmpty then
      s!"  | {c.name} : {adt.name}"
    else
      let typeStr := fieldTypes.intersperse " → " |> String.join
      s!"  | {c.name} : {typeStr} → {adt.name}"
  s!"inductive {adt.name} where\n" ++ (constrs.intersperse "\n" |> String.join) ++
  s!"\n  deriving Repr"

/-- Generate Lean def from rewrite rule -/
def ruleToLean (rule : RewriteRule) : String :=
  let condStr := match rule.condition with
    | some c => s!" (when {rosettaToLean c})"
    | none => ""
  s!"/-- {rule.name}: {rosettaToLean rule.lhs} ~> {rosettaToLean rule.rhs}{condStr} -/
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
def moduleToLean (langName : String) (mod : ModuleDecl) : String :=
  let header := s!"/-
  {langName}.{mod.name} - Generated from .lego via Rosetta pipeline

  This file was auto-generated. Do not edit manually.
-/

namespace {langName}.{mod.name}

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
  s!"end {langName}.{mod.name}\n"

/-- Generate Lean file from LangSpec -/
def langToLean (spec : LangSpec) : String :=
  let header := s!"/-
  {spec.name} - Generated from {spec.name}.lego via Rosetta pipeline

  This file was auto-generated. Do not edit manually.
-/

"
  let imports := spec.imports.map (fun i => s!"import {i}")
                   |>.intersperse "\n" |> String.join
  let moduleImports := spec.modules.map (fun m => s!"import {spec.name}.{m.name}")
                   |>.intersperse "\n" |> String.join
  let allImports := if imports.isEmpty then moduleImports
                    else imports ++ "\n" ++ moduleImports

  header ++ allImports ++ "\n\n" ++
  s!"namespace {spec.name}\n\n" ++
  s!"-- Re-exports from modules\n\n" ++
  s!"end {spec.name}\n"

/-- Generate individual module file -/
def generateModuleFile (langName : String) (mod : ModuleDecl) : String :=
  moduleToLean langName mod

/-! ## Main Entry Point -/

/-- Generate Lean code from a parsed .lego AST -/
def generateFromAST (ast : Term) (langName : String) : Option LangSpec := do
  -- Extract language structure from AST
  -- This would need proper AST walking - placeholder for now
  some { name := langName, modules := [], imports := [] }

/-- Generate Lean code from a .lego file -/
def generateLean (legoFile : String) : IO String := do
  let contents ← IO.FS.readFile legoFile
  match Bootstrap.parseLegoFile contents with
  | some ast =>
    -- For now, just show structure was parsed
    return s!"-- Parsed: {repr ast |>.take 200}..."
  | none =>
    throw (IO.userError "Parse error")

end Rosetta
