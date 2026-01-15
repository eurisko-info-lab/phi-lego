/-
  Lego.Loader: Load grammars from parsed .lego files

  This module converts parsed AST (DGrammar, DPiece nodes) back into
  executable Productions that can parse arbitrary input files.

  Key insight: The grammar is just data - we can interpret it at runtime.
-/

import Lego.Algebra
import Lego.Interp
import Lego.Bootstrap

namespace Lego.Loader

open Lego

/-! ## Helper Functions -/

/-- Split a list of Terms by .lit "|" tokens (the alternation separator).
    Returns groups of terms that form each alternative.
    Each group is combined into a seq if multiple elements. -/
def splitByPipe (ts : List Term) : List Term :=
  let rec go (acc : List Term) (current : List Term) : List Term :=
    match current with
    | [] =>
      if acc.isEmpty then [] else [mkSeq acc.reverse]
    | .lit "|" :: rest =>
      mkSeq acc.reverse :: go [] rest
    | t :: rest =>
      go (t :: acc) rest
  go [] ts
where
  mkSeq : List Term → Term
  | [] => .con "empty" []
  | [t] => t
  | ts => .con "seq" ts

/-! ## AST → GrammarExpr -/

/-- Flatten nested seq terms into a list -/
partial def flattenSeq (t : Term) : List Term :=
  match t with
  | .con "seq" [left, right] => flattenSeq left ++ flattenSeq right
  | other => [other]

/-- Extract annotation (conName, rest) from flattened args ending in → ident -/
def extractAnnotationFromFlat (args : List Term) : Option (String × List Term) :=
  match args.reverse with
  | .con "ident" [.var conName] :: .lit "→" :: rest => some (conName, rest.reverse)
  | _ => none

/-- Convert a parsed grammar expression AST back to GrammarExpr.
    pieceName is used to prefix unqualified references. -/
partial def astToGrammarExpr (pieceName : String := "") (t : Term) : Option GrammarExpr :=
  match t with
  -- Empty
  | .con "empty" _ => some GrammarExpr.empty

  -- Literal: (lit (string "..."))
  | .con "lit" [.con "string" [.lit s]] =>
    -- Strip quotes from string literal
    let s' := if s.startsWith "\"" && s.endsWith "\"" then
                s.drop 1 |>.dropRight 1
              else s
    some (GrammarExpr.lit s')

  -- Character literal: (char (char "'x'"))
  | .con "char" [.con "char" [.lit s]] =>
    -- Strip quotes from char literal 'x' → x
    let s' := if s.startsWith "'" && s.endsWith "'" then
                s.drop 1 |>.dropRight 1
              else s
    some (GrammarExpr.lit s')

  -- Reference: (ref (ident name))
  | .con "ref" [.con "ident" [.var name]] =>
    -- Built-in production names that should not be prefixed
    let builtins := ["name", "ident", "string", "number"]
    -- Prefix with piece name for unqualified references (except built-ins)
    let qualName := if pieceName.isEmpty || name.contains '.' || builtins.contains name then name
                    else s!"{pieceName}.{name}"
    some (GrammarExpr.ref qualName)

  -- Special: <ident>, <string>, etc.
  | .con "special" [.var special] =>
    -- Convert <ident> to TOKEN.ident
    if special.startsWith "<" && special.endsWith ">" then
      let inner := special.drop 1 |>.dropRight 1
      some (GrammarExpr.ref s!"TOKEN.{inner}")
    else
      some (GrammarExpr.ref special)

  -- Sequence: (seq g1 g2 ...)
  | .con "seq" gs =>
    gs.foldlM (fun acc g => do
      let g' ← astToGrammarExpr pieceName g
      pure (GrammarExpr.seq acc g')) GrammarExpr.empty

  -- Alternative: (alt g1 "|" g2 "|" g3 ...)
  -- Split by .lit "|" tokens, then fold into nested alts
  | .con "alt" args =>
    let parts := splitByPipe args
    match parts with
    | [] => none
    | [single] => astToGrammarExpr pieceName single
    | first :: rest => do
      let first' ← astToGrammarExpr pieceName first
      rest.foldlM (fun acc part => do
        let g' ← astToGrammarExpr pieceName part
        pure (GrammarExpr.alt acc g')) first'

  -- Star: (star g "*")
  | .con "star" [g, _] => do
    let g' ← astToGrammarExpr pieceName g
    pure (GrammarExpr.star g')

  -- Plus: (plus g "+")
  | .con "plus" [g, _] => do
    let g' ← astToGrammarExpr pieceName g
    pure (GrammarExpr.plus g')

  -- Optional: (opt g "?")
  | .con "opt" [g, _] => do
    let g' ← astToGrammarExpr pieceName g
    pure (GrammarExpr.alt g' GrammarExpr.empty)

  -- Group: (group "(" expr ")")
  | .con "group" [_, g, _] =>
    astToGrammarExpr pieceName g

  -- Annotated: (annotated ... "→" (ident conName))
  -- This wraps a grammar expression with a constructor name
  | .con "annotated" args =>
    -- Flatten and find the → ident part
    let flatArgs := args.flatMap flattenSeq
    -- Look for → ident at end
    match extractAnnotationFromFlat flatArgs with
    | some (conName, rest) =>
      -- Recursively convert the rest as a sequence
      let gexprs := rest.filterMap (astToGrammarExpr pieceName)
      match gexprs with
      | [] => none
      | [g] => some (GrammarExpr.node conName g)
      | g :: gs => some (GrammarExpr.node conName (gs.foldl GrammarExpr.seq g))
    | none => none  -- malformed annotated

  -- Fallback for unrecognized patterns
  | _ => none

/-- Extract production name from a grammar declaration -/
def extractProdName (pieceName : String) (gramDecl : Term) : Option String :=
  match gramDecl with
  | .con "DGrammar" args =>
    -- Flatten nested seq and look for ident at start
    let flatArgs := args.flatMap flattenSeq
    match flatArgs with
    | .con "ident" [.var prodName] :: _ => some s!"{pieceName}.{prodName}"
    | _ => none
  | _ => none

/-- Extract constructor annotation from flattened args (→ conName) if present -/
def extractConstructorAnnotation (args : List Term) : Option String :=
  -- Look for pattern: ... → ident ; at end of flattened seq
  match args.reverse with
  | .lit ";" :: .con "ident" [.var conName] :: .lit "→" :: _ => some conName
  | _ => none

/-- Strip constructor annotation from flattened args if present -/
def stripConstructorAnnotation (args : List Term) : List Term :=
  match args.reverse with
  | semi :: .con "ident" [_] :: .lit "→" :: rest => (semi :: rest).reverse
  | _ => args

/-- Extract grammar expression from a grammar declaration -/
def extractGrammarExpr (pieceName : String) (gramDecl : Term) : Option GrammarExpr :=
  match gramDecl with
  | .con "DGrammar" args =>
    -- DGrammar now has a single nested seq child - flatten it first
    let flatArgs := args.flatMap flattenSeq
    -- Structure after flattening: [ident, "::=", expr1, expr2, ..., ("→" ident)?, ";"]
    if flatArgs.length < 4 then none  -- need at least: name, ::=, one expr, ;
    else
      -- Check for constructor annotation
      let conName := extractConstructorAnnotation flatArgs
      let cleanArgs := stripConstructorAnnotation flatArgs
      let exprArgs := cleanArgs.drop 2 |>.dropLast  -- skip name, ::=, ;
      let gexprs := exprArgs.filterMap (astToGrammarExpr pieceName)
      let baseExpr := match gexprs with
        | [] => none
        | [g] => some g  -- single expression
        | g :: gs => some <| gs.foldl GrammarExpr.seq g  -- fold to sequence
      -- Wrap with node if constructor annotation present
      match conName, baseExpr with
      | some name, some g => some (GrammarExpr.node name g)
      | none, some g => some g
      | _, none => none
  | _ => none

/-- Extract all productions from a piece declaration -/
def extractPieceProductions (pieceDecl : Term) : List (String × GrammarExpr) :=
  match pieceDecl with
  | .con "DPiece" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g, extractGrammarExpr pieceName g with
      | some name, some expr => some (name, expr)
      | _, _ => none
  | .con "DToken" (.lit _ :: .con "ident" [.var pieceName] :: gramDecls) =>
    gramDecls.filterMap fun g =>
      match extractProdName pieceName g, extractGrammarExpr pieceName g with
      | some name, some expr => some (name, expr)
      | _, _ => none
  | _ => []

/-- Built-in productions available to all grammars -/
def builtinProductions : Productions := [
  -- name matches any identifier token
  ("Term.name", GrammarExpr.ref "TOKEN.ident"),
  -- Common aliases
  ("name", GrammarExpr.ref "TOKEN.ident"),
  ("ident", GrammarExpr.ref "TOKEN.ident"),
  ("string", GrammarExpr.ref "TOKEN.string"),
  ("number", GrammarExpr.ref "TOKEN.number")
]

/-- Extract productions from a parsed .lego file AST (without builtins) -/
partial def extractProductionsOnly (ast : Term) : Productions :=
  go ast
where
  go (t : Term) : Productions :=
    match t with
    | .con "DLang" ts =>
      ts.flatMap go
    | .con "DPiece" _ =>
      extractPieceProductions t
    | .con "DToken" _ =>
      extractPieceProductions t
    | .con "seq" ts =>
      ts.flatMap go
    | .con _ ts =>
      ts.flatMap go
    | _ => []

/-- Extract all productions from a parsed .lego file AST (includes builtins) -/
def extractAllProductions (ast : Term) : Productions :=
  builtinProductions ++ extractProductionsOnly ast

/-! ## Symbol Extraction for Tokenization -/

/-- Extract all literal symbols from a grammar expression -/
partial def extractSymbols (g : GrammarExpr) : List String :=
  match g with
  | .mk .empty => []
  | .mk (.lit s) => [s]
  | .mk (.ref _) => []
  | .mk (.seq g1 g2) => extractSymbols g1 ++ extractSymbols g2
  | .mk (.alt g1 g2) => extractSymbols g1 ++ extractSymbols g2
  | .mk (.star g') => extractSymbols g'
  | .mk (.bind _ g') => extractSymbols g'
  | .mk (.node _ g') => extractSymbols g'

/-- Extract all symbols from productions -/
def extractAllSymbols (prods : Productions) : List String :=
  prods.flatMap (fun (_, g) => extractSymbols g) |>.eraseDups

/-! ## Grammar Loading -/

/-- A loaded grammar ready for parsing -/
structure LoadedGrammar where
  productions : Productions
  symbols : List String
  startProd : String
  deriving Repr

/-- Load a grammar from a .lego file -/
def loadGrammarFromFile (path : String) (startProd : String) : IO (Option LoadedGrammar) := do
  try
    let content ← IO.FS.readFile path
    match Bootstrap.parseLegoFile content with
    | some ast =>
      let prods := extractAllProductions ast
      let symbols := extractAllSymbols prods
      pure (some { productions := prods, symbols := symbols, startProd := startProd })
    | none =>
      pure none
  catch _ =>
    pure none

/-- Load a grammar from parsed AST -/
def loadGrammarFromAST (ast : Term) (startProd : String) : LoadedGrammar :=
  let prods := extractAllProductions ast
  let symbols := extractAllSymbols prods
  { productions := prods, symbols := symbols, startProd := startProd }

/-! ## Parsing with Loaded Grammar -/

/-- Parse input using a loaded grammar -/
def parseWithGrammar (grammar : LoadedGrammar) (input : String) : Option Term :=
  let tokens := Bootstrap.tokenize input
  let st : ParseState := { tokens := tokens, binds := [] }
  match grammar.productions.find? (·.1 == grammar.startProd) with
  | some (_, g) =>
    match parseGrammar grammar.productions g st with
    | some (t, st') => if st'.tokens.isEmpty then some t else none
    | none => none
  | none => none

/-- Parse a file using a loaded grammar -/
def parseFileWithGrammar (grammar : LoadedGrammar) (path : String) : IO (Option Term) := do
  try
    let content ← IO.FS.readFile path
    pure (parseWithGrammar grammar content)
  catch _ =>
    pure none

/-! ## Parameterized Parsing (AST typeclass) -/

/-- Parse input using a loaded grammar, building into any AST type -/
def parseWithGrammarAs (α : Type) [AST α] (grammar : LoadedGrammar) (input : String) : Option α :=
  let tokens := Bootstrap.tokenize input
  let st : ParseStateT α := { tokens := tokens, binds := [] }
  match grammar.productions.find? (·.1 == grammar.startProd) with
  | some (_, g) =>
    match parseGrammarT grammar.productions g st with
    | some (t, st') => if st'.tokens.isEmpty then some t else none
    | none => none
  | none => none

/-- Parse and build GrammarExpr directly from grammar source -/
def parseAsGrammarExpr (grammar : LoadedGrammar) (input : String) : Option GrammarExpr :=
  parseWithGrammarAs GrammarExpr grammar input

/-! ## Bootstrap Loading -/

/-- Load Bootstrap.lego and extract productions (without builtins).
    This allows comparing with the hard-coded Bootstrap. -/
def loadBootstrapProductions (path : String := "./test/Bootstrap.lego") : IO (Option Productions) := do
  try
    let content ← IO.FS.readFile path
    match Bootstrap.parseLegoFile content with
    | some ast => pure (some (extractProductionsOnly ast))
    | none => pure none
  catch _ =>
    pure none

/-- Compare two productions lists for equivalence (by name) -/
def compareProductionNames (p1 p2 : Productions) : Bool × List String × List String :=
  let names1 := p1.map (·.1) |>.eraseDups
  let names2 := p2.map (·.1) |>.eraseDups
  let onlyIn1 := names1.filter (fun n => !names2.contains n)
  let onlyIn2 := names2.filter (fun n => !names1.contains n)
  (onlyIn1.isEmpty && onlyIn2.isEmpty, onlyIn1, onlyIn2)

/-- Check if p1 is a subset of p2 (by production name) -/
def isSubsetOfProductions (p1 p2 : Productions) : Bool × List String :=
  let names1 := p1.map (·.1) |>.eraseDups
  let names2 := p2.map (·.1) |>.eraseDups
  let missing := names1.filter (fun n => !names2.contains n)
  (missing.isEmpty, missing)

/-! ## Convenience: Load and Parse -/

/-- Load grammar and parse a file in one step -/
def loadAndParse (grammarPath : String) (startProd : String) (inputPath : String) : IO (Option Term) := do
  match ← loadGrammarFromFile grammarPath startProd with
  | some grammar => parseFileWithGrammar grammar inputPath
  | none => pure none

end Lego.Loader
