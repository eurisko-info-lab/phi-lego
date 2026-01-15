/-
  Lego.Bootstrap: The Meta-Grammar (pre-compiled)

  This is exactly like Grammar.sexpr - a pre-compiled grammar that can parse
  other grammars. But structurally it's just another Language, not special.

  The only difference: it's defined in Lean directly (bootstrapped) rather
  than parsed from a .lego file.
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Bootstrap

open GrammarExpr

/-! ## Meta: The grammar for grammars -/

/-- Atom piece: basic tokens -/
def atomPiece : Piece := {
  name := "Atom"
  grammar := [
    ("Atom.ident",  node "ident" (ref "TOKEN.ident")),
    ("Atom.string", node "string" (ref "TOKEN.string")),
    ("Atom.char",   node "char" (ref "TOKEN.char")),    -- 'x' character literals
    ("Atom.number", node "number" (ref "TOKEN.number"))
  ]
  rules := []
}

/-- Term piece: S-expression terms -/
def termPiece : Piece := {
  name := "Term"
  grammar := [
    ("Term.term",
      (node "var" (ref "Atom.ident")).alt
      ((node "lit" (ref "Atom.string")).alt
      ((node "num" (ref "Atom.number")).alt
       (node "con" ((lit "(").seq ((ref "Atom.ident").seq ((ref "Term.term").star.seq (lit ")"))))))))
  ]
  rules := []
}

/-- Pattern piece: match patterns -/
def patternPiece : Piece := {
  name := "Pattern"
  grammar := [
    ("Pattern.pattern",
      (node "metavar" ((lit "$").seq (ref "Atom.ident"))).alt
      ((node "pcon" ((lit "(").seq ((ref "Atom.ident").seq ((ref "Pattern.pattern").star.seq (lit ")"))))).alt
      ((node "plit" (ref "Atom.string")).alt
       (node "pvar" (ref "Atom.ident")))))
  ]
  rules := []
}

/-- Template piece: substitution templates -/
def templatePiece : Piece := {
  name := "Template"
  grammar := [
    ("Template.template",
      (node "metavar" ((lit "$").seq (ref "Atom.ident"))).alt
      ((node "tcon" ((lit "(").seq ((ref "Atom.ident").seq ((ref "Template.template").star.seq (lit ")"))))).alt
      ((node "tlit" (ref "Atom.string")).alt
       (node "tvar" (ref "Atom.ident")))))
  ]
  rules := []
}

/-- GrammarExpr piece: grammar expressions -/
def grammarExprPiece : Piece := {
  name := "GrammarExpr"
  grammar := [
    ("GrammarExpr.expr", ref "GrammarExpr.alt"),
    ("GrammarExpr.alt",
      (node "alt" ((ref "GrammarExpr.seq").seq ((lit "|").seq (ref "GrammarExpr.alt")))).alt
       (ref "GrammarExpr.seq")),
    -- seq can optionally have → ident for constructor annotation
    ("GrammarExpr.seq",
      (node "annotated" ((ref "GrammarExpr.seqBase").seq ((lit "→").seq (ref "Atom.ident")))).alt
       (ref "GrammarExpr.seqBase")),
    ("GrammarExpr.seqBase",
      (node "seq" ((ref "GrammarExpr.suffix").seq (ref "GrammarExpr.suffix").star)).alt
       (ref "GrammarExpr.suffix")),
    ("GrammarExpr.suffix",
      (node "star" ((ref "GrammarExpr.atom").seq (lit "*"))).alt
      ((node "plus" ((ref "GrammarExpr.atom").seq (lit "+"))).alt
      ((node "opt"  ((ref "GrammarExpr.atom").seq (lit "?"))).alt
       (ref "GrammarExpr.atom")))),
    ("GrammarExpr.atom",
      (node "lit" (ref "Atom.string")).alt      -- "keyword" string literal
      ((node "char" (ref "Atom.char")).alt      -- 'x' character literal (for token grammars)
      ((node "ref" (ref "Atom.ident")).alt
      ((node "group" ((lit "(").seq ((ref "GrammarExpr.expr").seq (lit ")")))).alt
      ((node "special" (ref "TOKEN.special")).alt
       (node "empty" (lit "ε")))))))
  ]
  rules := []
}

/-- File piece: file structure (uses ; as separator, no end keyword needed) -/
def filePiece : Piece := {
  name := "File"
  grammar := [
    ("File.legoFile", (ref "File.decl").star),
    ("File.decl",
      (ref "File.importDecl").alt
      ((ref "File.langDecl").alt
      ((ref "File.tokenDecl").alt
      ((ref "File.pieceDecl").alt
      ((ref "File.ruleDecl").alt
       (ref "File.testDecl")))))),
    -- import Atoms ;
    ("File.importDecl",
      node "DImport" ((lit "import").seq ((ref "Atom.ident").seq (lit ";")))),
    -- lang Lambda (Atoms) := ... (ends at next top-level decl or EOF)
    ("File.langDecl",
      node "DLang" ((lit "lang").seq ((ref "Atom.ident").seq
                    (((ref "File.imports").alt empty).seq
                    ((lit ":=").seq (ref "File.langBody")))))),
    ("File.langBody", (ref "File.innerDecl").star),
    ("File.innerDecl",
      (ref "File.tokenDecl").alt
      ((ref "File.pieceDecl").alt
      ((ref "File.ruleDecl").alt
       (ref "File.testDecl")))),
    -- (Ident, Ident, ...)
    ("File.imports",
      node "DImports" ((lit "(").seq ((ref "Atom.ident").seq (((lit ",").seq (ref "Atom.ident")).star.seq (lit ")"))))),
    -- token Name prodDecl+ (CharStream → Token level)
    ("File.tokenDecl",
      node "DToken" ((lit "token").seq ((ref "Atom.ident").seq (ref "File.prodDecl").plus))),
    -- piece Name prodDecl+ (TokenStream → Term level)
    ("File.pieceDecl",
      node "DPiece" ((lit "piece").seq ((ref "Atom.ident").seq (ref "File.prodDecl").plus))),
    -- name ::= expr ;
    ("File.prodDecl",
      node "DGrammar" ((ref "Atom.ident").seq ((lit "::=").seq ((ref "GrammarExpr.expr").seq (lit ";"))))),
    -- rule name: pattern ~> template ;
    ("File.ruleDecl",
      node "DRule" ((lit "rule").seq ((ref "Atom.ident").seq ((lit ":").seq
                    ((ref "Pattern.pattern").seq ((lit "~>").seq ((ref "Template.template").seq (lit ";")))))))),
    -- test "name": term (~~> term)? ;
    ("File.testDecl",
      node "DTest" ((lit "test").seq ((ref "Atom.string").seq ((lit ":").seq
                    ((ref "Term.term").seq ((((lit "~~>").seq (ref "Term.term")).alt empty).seq (lit ";")))))))
  ]
  rules := []
}

/-- The complete Meta language -/
def metaGrammar : Language := {
  name := "Meta"
  pieces := [atomPiece, termPiece, patternPiece, templatePiece, grammarExprPiece, filePiece]
}

/-- Build the interpreter for parsing .lego files -/
def metaInterp : LangInterp := metaGrammar.toInterp "File.legoFile"

/-! ## Loading Languages -/

/-- Check if a character is a symbol character (ASCII) -/
def isSymChar (c : Char) : Bool :=
  c ∈ ['(', ')', '[', ']', '{', '}', ':', '=', '|', '*', '+', '?', '~', '>', '<', '$', '.', ',', ';', '^']

/-- Check if a character is a Unicode symbol -/
def isUnicodeSymChar (c : Char) : Bool :=
  c ∈ ['→', '←', '×', '∂', '𝕀', '∨', '∧', '∀', '∃', 'ε', 'μ', '▸', '▹', 'ω', 'π']

/-- Check if a character is a Unicode letter (Greek, etc.) that can start identifiers -/
def isUnicodeLetter (c : Char) : Bool :=
  c ∈ ['λ', 'Σ', 'Π', 'α', 'β', 'γ', 'δ', 'φ', 'ψ', 'τ', 'σ', 'ρ']

/-- Check if a character is an operator character that can be multi-char -/
def isOpChar (c : Char) : Bool :=
  c ∈ [':', '=', '~', '>', '<', '-']

/-- Remove comments from a line -/
def removeLineComment (s : String) : String :=
  match s.splitOn "--" with
  | [] => ""
  | h :: _ => h

/-- Tokenize a string into tokens (proper lexer).
    Skips comments and newlines by default. -/
partial def tokenize (s : String) : TokenStream :=
  -- Remove comments and tokenize each line, then concatenate
  let lines := s.splitOn "\n" |>.map removeLineComment |>.map String.trim |>.filter (· ≠ "")
  lines.foldl (fun acc line => acc ++ tokenizeLine line.toList []) []
where
  tokenizeLine (chars : List Char) (acc : List Token) : TokenStream :=
    match chars with
    | [] => acc.reverse
    | c :: rest =>
      if c.isWhitespace then
        tokenizeLine rest acc
      -- String literal (double quotes)
      else if c == '"' then
        let (str, rest') := takeString rest ""
        tokenizeLine rest' (Token.lit s!"\"{str}\"" :: acc)
      -- Character literal (single quotes) - for token grammars
      else if c == '\'' then
        let (chr, rest') := takeChar rest
        tokenizeLine rest' (Token.lit s!"'{chr}'" :: acc)
      -- Multi-char operators: ::= ~> ~~> :=
      else if c == ':' && rest.head? == some ':' && rest.tail.head? == some '=' then
        tokenizeLine rest.tail.tail (Token.sym "::=" :: acc)
      else if c == ':' && rest.head? == some '=' then
        tokenizeLine rest.tail (Token.sym ":=" :: acc)
      else if c == '~' && rest.head? == some '~' && rest.tail.head? == some '>' then
        tokenizeLine rest.tail.tail (Token.sym "~~>" :: acc)
      else if c == '~' && rest.head? == some '>' then
        tokenizeLine rest.tail (Token.sym "~>" :: acc)
      -- Special syntax: <ident> as single token
      else if c == '<' then
        let (special, rest') := takeSpecial rest ""
        tokenizeLine rest' (Token.sym s!"<{special}>" :: acc)
      -- Single-char symbols (ASCII)
      else if isSymChar c && c != '<' then
        tokenizeLine rest (Token.sym (String.singleton c) :: acc)
      -- Unicode symbols (single char)
      else if isUnicodeSymChar c then
        tokenizeLine rest (Token.sym (String.singleton c) :: acc)
      -- Identifier or keyword (ASCII or Unicode letter)
      else if c.isAlpha || c == '_' || isUnicodeLetter c then
        let (ident, rest') := takeIdent chars ""
        tokenizeLine rest' (Token.ident ident :: acc)
      -- Number
      else if c.isDigit then
        let (num, rest') := takeNumber chars ""
        tokenizeLine rest' (Token.number num :: acc)
      else
        -- Skip unknown character
        tokenizeLine rest acc

  takeChar (chars : List Char) : String × List Char :=
    match chars with
    | [] => ("", [])
    | '\\' :: c :: '\'' :: rest => (String.mk ['\\', c], rest)  -- escape sequence
    | c :: '\'' :: rest => (String.singleton c, rest)
    | _ => ("", chars)  -- malformed

  takeString (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | '"' :: rest => (acc, rest)
    | '\\' :: c :: rest => takeString rest (acc.push '\\' |>.push c)
    | c :: rest => takeString rest (acc.push c)

  takeIdent (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      if c.isAlpha || c.isDigit || c == '_' || isUnicodeLetter c then
        takeIdent rest (acc.push c)
      else
        (acc, chars)

  takeNumber (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | c :: rest =>
      if c.isDigit then
        takeNumber rest (acc.push c)
      else
        (acc, chars)

  takeSpecial (chars : List Char) (acc : String) : String × List Char :=
    match chars with
    | [] => (acc, [])
    | '>' :: rest => (acc, rest)
    | c :: rest =>
      if c.isAlpha || c.isDigit || c == '_' then
        takeSpecial rest (acc.push c)
      else
        (acc, chars)  -- malformed, but recover

/-- Parse a .lego file into declarations -/
def parseLegoFile (content : String) : Option Term :=
  metaInterp.parse (tokenize content)

end Lego.Bootstrap
