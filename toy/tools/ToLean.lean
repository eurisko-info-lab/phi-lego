/-
  ToLean: Generate Lean code from Lego grammar

  Usage:
    lake exe tolean test/Bootstrap.lego > generated/Bootstrap.lean

  This achieves meta-circularity: Bootstrap.lego can generate code
  equivalent to src/Lego/Bootstrap.lean, allowing the system to
  bootstrap itself.

  Translation:
    .lego                         Lean
    ──────────────────────────    ──────────────────────────────────
    piece Atom                    def atomPiece : Piece := { ... }
    ident ::= <ident> ;           ("Atom.ident", ref "TOKEN.ident")
    foo → con                     node "con" (...)
    foo | bar                     (...).alt (...)
    foo bar                       (...).seq (...)
    foo*                          (...).star
    foo+                          (...).plus
    foo?                          (...).alt empty
    token Token                   Character predicates + tokenize fn
-/

import Lego.Algebra
import Lego.Bootstrap
import Lego.Loader

namespace Lego.ToLean

open Lego

/-- Escape a string for Lean string literal -/
def escapeLeanString (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | c => acc.push c
  ) ""

/-- Well-known cross-piece production mappings -/
def crossPieceRefs : List (String × String) := [
  -- Atom pieces
  ("ident", "Atom.ident"),
  ("string", "Atom.string"),
  ("number", "Atom.number"),
  ("char", "Atom.char"),
  -- Term pieces
  ("term", "Term.term"),
  ("conname", "Term.conname"),
  -- Pattern/Template pieces
  ("pattern", "Pattern.pattern"),
  ("template", "Template.template"),
  -- GrammarExpr pieces
  ("expr", "GrammarExpr.expr"),
  ("alt", "GrammarExpr.alt"),
  ("seq", "GrammarExpr.seq"),
  ("seqBase", "GrammarExpr.seqBase"),
  ("suffix", "GrammarExpr.suffix"),
  ("atom", "GrammarExpr.atom")
]

/-- Qualify a reference name if it matches a known piece production -/
def qualifyRef (currentPiece : String) (name : String) : String :=
  if name.startsWith "TOKEN." then name
  else if name.contains '.' then
    -- Already qualified - but check if it's a mis-qualified cross-piece ref
    -- e.g., "File.expr" should be "GrammarExpr.expr"
    let shortName := name.splitOn "." |>.getLast!
    match crossPieceRefs.find? (·.1 == shortName) with
    | some (_, qualified) =>
      -- Only fix if current qualification is wrong
      if qualified != name then qualified else name
    | none => name
  -- Check for well-known cross-piece references
  else match crossPieceRefs.find? (·.1 == name) with
    | some (_, qualified) => qualified
    | none => s!"{currentPiece}.{name}"

/-- Convert GrammarExpr to Lean source code -/
partial def exprToLean (pieceName : String) (g : GrammarExpr) : String :=
  match g with
  | .mk .empty => "empty"
  | .mk (.lit s) => s!"(lit \"{escapeLeanString s}\")"
  | .mk (.ref name) =>
    let qualName := if name.startsWith "TOKEN." then name
                    else qualifyRef pieceName name
    s!"(ref \"{qualName}\")"
  | .mk (.seq g1 g2) =>
    let s1 := exprToLean pieceName g1
    let s2 := exprToLean pieceName g2
    s!"({s1}.seq {s2})"
  | .mk (.alt g1 g2) =>
    let s1 := exprToLean pieceName g1
    let s2 := exprToLean pieceName g2
    s!"({s1}.alt {s2})"
  | .mk (.star g') =>
    s!"({exprToLean pieceName g'}.star)"
  | .mk (.bind x g') =>
    s!"(bind \"{x}\" {exprToLean pieceName g'})"
  | .mk (.node name g') =>
    s!"(node \"{name}\" {exprToLean pieceName g'})"

/-- Convert a single production to Lean tuple -/
def prodToLean (pieceName : String) (name : String) (expr : GrammarExpr) : String :=
  s!"    (\"{name}\", {exprToLean pieceName expr})"

/-- Group productions by piece name -/
def groupByPiece (prods : Productions) : List (String × Productions) :=
  let pieceNames := prods.map (fun (n, _) =>
    match n.splitOn "." with
    | [p, _] => p
    | _ => "Unknown"
  ) |>.eraseDups
  pieceNames.map fun pname =>
    (pname, prods.filter fun (n, _) =>
      match n.splitOn "." with
      | [p, _] => p == pname
      | _ => false)

/-- Convert piece name to Lean identifier (camelCase) -/
def pieceToLeanIdent (name : String) : String :=
  let first := name.toList.head? |>.map Char.toLower |>.getD 'x'
  s!"{first}{name.drop 1}Piece"

/-- Generate a Piece definition -/
def generatePiece (pieceName : String) (prods : Productions) : String :=
  let leanIdent := pieceToLeanIdent pieceName
  let prodStrs := prods.map (fun (n, e) => prodToLean pieceName n e)
  let grammar := ",\n".intercalate prodStrs
  s!"/-- {pieceName} piece -/
def {leanIdent} : Piece := \{
  name := \"{pieceName}\"
  grammar := [
{grammar}
  ]
  rules := []
}"

/-- Extract character set from token grammar (for tokenizer generation) -/
partial def extractCharSet (g : GrammarExpr) : List Char :=
  match g with
  | .mk (.lit s) =>
    -- Character literals like 'x' → extract x
    if s.startsWith "'" && s.endsWith "'" && s.length == 3 then
      match s.toList with
      | [_, c, _] => [c]
      | _ => []
    else if s.length == 1 then
      [s.toList.head!]
    else []
  | .mk (.alt g1 g2) => extractCharSet g1 ++ extractCharSet g2
  | .mk (.seq g1 g2) => extractCharSet g1 ++ extractCharSet g2
  | .mk (.star g') => extractCharSet g'
  | .mk (.node _ g') => extractCharSet g'
  | .mk (.ref _) => []
  | .mk .empty => []
  | .mk (.bind _ g') => extractCharSet g'

/-- Generate character set predicate -/
def generateCharPredicate (name : String) (chars : List Char) : String :=
  let charLits := chars.map (fun c => s!"'{c}'")
  let charList := ", ".intercalate charLits
  s!"/-- Check if character is in {name} set -/
def is{name} (c : Char) : Bool :=
  c ∈ [{charList}]"

/-- Extract all character sets from token productions -/
def extractTokenCharSets (tokenProds : Productions) : List (String × List Char) :=
  tokenProds.filterMap fun (name, expr) =>
    let chars := extractCharSet expr
    if chars.isEmpty then none
    else
      let shortName := match name.splitOn "." with
        | [_, n] => n.capitalize
        | _ => name.capitalize
      some (shortName, chars.eraseDups)

/-- Default tokenizer when no token piece is defined -/
def defaultTokenizer : String :=
"
/-- Default tokenizer (uses Bootstrap tokenizer) -/
def tokenize : String → TokenStream := Lego.Bootstrap.tokenize"

/-- Generate the tokenizer function skeleton -/
def generateTokenizer (charSets : List (String × List Char)) : String :=
  let predicates := charSets.map (fun (n, cs) => generateCharPredicate n cs)
  let predCode := "\n\n".intercalate predicates
  s!"{predCode}

/-- Tokenize a string into tokens -/
partial def tokenize (s : String) : TokenStream :=
  let lines := s.splitOn \"\\n\" |>.map String.trim |>.filter (· ≠ \"\")
  lines.foldl (fun acc line => acc ++ tokenizeLine line.toList []) []
where
  tokenizeLine (chars : List Char) (acc : List Token) : TokenStream :=
    match chars with
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then
        tokenizeLine rest acc
      else if c == '\"' then
        let (str, rest') := takeString rest \"\"
        tokenizeLine rest' (Token.lit s!\"\\\"\{str}\\\"\" :: acc)
      else if c == '\\'' then
        let (chr, rest') := takeChar rest
        tokenizeLine rest' (Token.lit s!\"'\{chr}'\" :: acc)
      else if c.isAlpha || c == '_' then
        let (ident, rest') := takeIdent chars \"\"
        tokenizeLine rest' (Token.ident ident :: acc)
      else if c.isDigit then
        let (num, rest') := takeNumber chars \"\"
        tokenizeLine rest' (Token.number num :: acc)
      else
        tokenizeLine rest (Token.sym (String.singleton c) :: acc)

  takeString (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | '\"' :: rest => (acc, rest)
    | '\\\\' :: c :: rest => takeString rest (acc.push '\\\\' |>.push c)
    | c :: rest => takeString rest (acc.push c)

  takeChar (chars : List Char) : String × List Char :=
    match chars with
    | [] => (\"\", [])
    | c :: '\\'' :: rest => (String.singleton c, rest)
    | _ => (\"\", chars)

  takeIdent (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      if c.isAlpha || c.isDigit || c == '_' then
        takeIdent rest (acc.push c)
      else (acc, chars)

  takeNumber (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      if c.isDigit then takeNumber rest (acc.push c)
      else (acc, chars)"

/-! ## Rule Generation -/

/-- Convert a Term to Lean source code -/
partial def termToLean (t : Term) : String :=
  match t with
  | .var name => s!".var \"{escapeLeanString name}\""
  | .lit s => s!".lit \"{escapeLeanString s}\""
  | .con c [] => s!".con \"{escapeLeanString c}\" []"
  | .con c args =>
    let argStrs := args.map termToLean
    s!".con \"{escapeLeanString c}\" [{", ".intercalate argStrs}]"

/-- Generate a Rule definition -/
def ruleToLean (r : Rule) : String :=
  let patLean := termToLean r.pattern
  let tmplLean := termToLean r.template
  s!"/-- Rule: {r.name} -/
def rule_{r.name.replace "-" "_"} : Rule := \{
  name := \"{r.name}\"
  pattern := {patLean}
  template := {tmplLean}
}"

/-- Generate all rule definitions -/
def generateRules (rules : List Rule) : String :=
  if rules.isEmpty then ""
  else
    let ruleDefs := rules.map ruleToLean
    let ruleNames := rules.map (fun r => s!"rule_{r.name.replace "-" "_"}")
    let ruleList := ", ".intercalate ruleNames
    s!"/-! ## Rewrite Rules -/

{"\n\n".intercalate ruleDefs}

/-- All rules for this language -/
def allRules : List Rule := [{ruleList}]

/-- Combined interpreter from all rules -/
def ruleInterp : Iso Term Term := Language.combineRules allRules

/-- Apply rules to normalize a term -/
partial def normalize (t : Term) : Term :=
  match ruleInterp.forward t with
  | some t' => normalize t'
  | none =>
    match t with
    | .con c args => .con c (args.map normalize)
    | _ => t"

/-- Find the best start production -/
def findStartProd (prods : Productions) : String :=
  -- Prefer File.legoFile, then first File.* production, then first overall
  match prods.find? (fun (n, _) => n == "File.legoFile") with
  | some (n, _) => n
  | none =>
    match prods.find? (fun (n, _) => n.startsWith "File.") with
    | some (n, _) => n
    | none =>
      match prods with
      | (n, _) :: _ => n
      | _ => "File.legoFile"

/-- Generate the complete Lean module -/
def generateLeanModule (langName : String) (prods : Productions) (tokenProds : Productions) (rules : List Rule) : String :=
  let grouped := groupByPiece prods
  let pieces := grouped.map (fun (n, ps) => generatePiece n ps)
  let pieceCode := "\n\n".intercalate pieces

  let pieceNames := grouped.map (·.1)
  let pieceIdents := pieceNames.map pieceToLeanIdent
  let pieceList := ", ".intercalate pieceIdents

  let startProd := findStartProd prods

  -- Generate tokenizer from token productions (or use default)
  let charSets := extractTokenCharSets tokenProds
  let tokenizerCode := if tokenProds.isEmpty then defaultTokenizer else generateTokenizer charSets

  -- Generate rules
  let rulesCode := generateRules rules

  -- Add Bootstrap import if using default tokenizer
  let bootstrapImport := if tokenProds.isEmpty then "\nimport Lego.Bootstrap" else ""

  s!"/-
  Generated from {langName}.lego

  This module was automatically generated by ToLean.
  It should be structurally equivalent to hand-written Bootstrap.lean.
-/

import Lego.Algebra
import Lego.Interp{bootstrapImport}

namespace Lego.{langName}

open GrammarExpr

/-! ## Grammar Pieces -/

{pieceCode}

/-! ## Language Definition -/

/-- The complete {langName} language -/
def grammar : Language := \{
  name := \"{langName}\"
  pieces := [{pieceList}]
}

/-- Build the interpreter -/
def interp : LangInterp := grammar.toInterp \"{startProd}\"

/-! ## Tokenizer -/
{tokenizerCode}

/-- Parse input -/
def parse (content : String) : Option Term :=
  interp.parse (tokenize content)

{rulesCode}

end Lego.{langName}
"

/-- Extract grammar name from file path -/
def extractGrammarName (path : String) : String :=
  let basename := path.splitOn "/" |>.getLast!
  match basename.splitOn "." with
  | name :: _ => name
  | _ => "Grammar"

/-- Load a .lego file and convert to Lean -/
def legoFileToLean (path : String) : IO String := do
  let content ← IO.FS.readFile path
  let langName := extractGrammarName path
  match Bootstrap.parseLegoFile content with
  | some ast =>
    let prods := Loader.extractProductionsOnly ast
    let tokenProds := Loader.extractTokenProductions ast
    let rules := Loader.extractRules ast
    pure (generateLeanModule langName prods tokenProds rules)
  | none =>
    throw (IO.userError s!"Failed to parse {path}")

end Lego.ToLean

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let lean ← Lego.ToLean.legoFileToLean path
    IO.println lean
  | _ =>
    IO.eprintln "Usage: tolean <file.lego>"
    IO.eprintln ""
    IO.eprintln "Converts a Lego grammar to Lean source code."
    IO.eprintln "The output matches the structure of Bootstrap.lean,"
    IO.eprintln "enabling meta-circular bootstrapping."
    IO.eprintln ""
    IO.eprintln "Example:"
    IO.eprintln "  lake exe tolean test/Bootstrap.lego > generated/Bootstrap.lean"
    IO.Process.exit 1
