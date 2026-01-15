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

/-! ## AST → GrammarExpr -/

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

  -- Alternative: (alt g1 "|" g2)
  | .con "alt" (g1 :: _ :: g2 :: _) => do
    let g1' ← astToGrammarExpr pieceName g1
    let g2' ← astToGrammarExpr pieceName g2
    pure (GrammarExpr.alt g1' g2')

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

  -- Fallback for unrecognized patterns
  | _ => none

/-- Extract production name from a grammar declaration -/
def extractProdName (pieceName : String) (gramDecl : Term) : Option String :=
  match gramDecl with
  | .con "DGrammar" (.con "ident" [.var prodName] :: _) =>
    some s!"{pieceName}.{prodName}"
  | _ => none

/-- Extract grammar expression from a grammar declaration -/
def extractGrammarExpr (pieceName : String) (gramDecl : Term) : Option GrammarExpr :=
  match gramDecl with
  | .con "DGrammar" args =>
    -- Structure: [ident, "::=", expr1, expr2, ..., ";"]
    -- Skip first 2 (name, ::=) and last 1 (;), combine rest as sequence
    if args.length < 4 then none  -- need at least: name, ::=, one expr, ;
    else
      let exprArgs := args.drop 2 |>.dropLast  -- skip name, ::=, ;
      let gexprs := exprArgs.filterMap (astToGrammarExpr pieceName)
      match gexprs with
      | [] => none
      | [g] => some g  -- single expression
      | g :: gs => some <| gs.foldl GrammarExpr.seq g  -- fold to sequence
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

/-- Extract all productions from a parsed .lego file AST -/
partial def extractAllProductions (ast : Term) : Productions :=
  let extracted := go ast
  builtinProductions ++ extracted
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

/-! ## Convenience: Load and Parse -/

/-- Load grammar and parse a file in one step -/
def loadAndParse (grammarPath : String) (startProd : String) (inputPath : String) : IO (Option Term) := do
  match ← loadGrammarFromFile grammarPath startProd with
  | some grammar => parseFileWithGrammar grammar inputPath
  | none => pure none

end Lego.Loader
