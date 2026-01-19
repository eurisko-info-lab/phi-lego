/-
  Seed Grammar for Bootstrap

  PURPOSE: This is the MINIMAL hardcoded grammar needed to parse Bootstrap.lego.
  Once Bootstrap.lego is loaded at runtime, its grammar REPLACES this one.

  This file exists only to break the chicken-and-egg problem:
  - We need a grammar to parse Bootstrap.lego
  - Bootstrap.lego defines the grammar
  - Solution: hardcode just enough to parse Bootstrap.lego once

  After runtime bootstrap (see Lego.Runtime):
  - This grammar is ERASED
  - All .lego files are parsed with the grammar FROM Bootstrap.lego
  - Edit Bootstrap.lego → changes take effect immediately

  DO NOT EDIT - regenerate with:
    lake exe tolean --grammar test/Bootstrap.lego > generated/BootstrapGrammar.lean
-/

import Lego.Algebra
import Lego.Interp

namespace Lego.Generated.Bootstrap

open GrammarExpr
open Lego

/-! ## Grammar Pieces -/

/-- Atom piece -/
def atomPiece : Piece := {
  name := "Atom"
  grammar := [
    ("Atom.ident", (node "ident" (ref "TOKEN.ident"))),
    ("Atom.string", (node "string" (ref "TOKEN.string"))),
    ("Atom.char", (node "char" (ref "TOKEN.char"))),
    ("Atom.number", (node "number" (ref "TOKEN.number")))
  ]
  rules := []
}

/-- Term piece -/
def termPiece : Piece := {
  name := "Term"
  grammar := [
    ("Term.term", ((node "var" (ref "Atom.ident")).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "con" ((((lit "(").seq (ref "Term.conname")).seq ((ref "Term.term").star)).seq (lit ")"))))))),
    ("Term.conname", ((ref "Atom.ident").alt (ref "TOKEN.sym")))
  ]
  rules := []
}

/-- Pattern piece -/
def patternPiece : Piece := {
  name := "Pattern"
  grammar := [
    ("Pattern.pattern", ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "con" ((((lit "(").seq (ref "Term.conname")).seq ((ref "Pattern.pattern").star)).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "con" (ref "Atom.ident")))))))
  ]
  rules := []
}

/-- Template piece -/
def templatePiece : Piece := {
  name := "Template"
  grammar := [
    ("Template.template", ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "con" ((((lit "(").seq (ref "Atom.ident")).seq ((ref "Template.template").star)).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "con" (ref "Atom.ident")))))))
  ]
  rules := []
}

/-- GrammarExpr piece -/
def grammarExprPiece : Piece := {
  name := "GrammarExpr"
  grammar := [
    ("GrammarExpr.expr", (ref "GrammarExpr.alt")),
    ("GrammarExpr.alt", ((node "alt" (((ref "GrammarExpr.seq").seq (lit "|")).seq (ref "GrammarExpr.alt"))).alt (ref "GrammarExpr.seq"))),
    ("GrammarExpr.seq", ((node "annotated" (((ref "GrammarExpr.seqBase").seq (lit "→")).seq (ref "Atom.ident"))).alt (ref "GrammarExpr.seqBase"))),
    ("GrammarExpr.seqBase", ((node "seq" ((ref "GrammarExpr.suffix").seq ((ref "GrammarExpr.suffix").star))).alt (ref "GrammarExpr.suffix"))),
    ("GrammarExpr.suffix", ((node "star" ((ref "GrammarExpr.atom").seq (lit "*"))).alt ((node "plus" ((ref "GrammarExpr.atom").seq (lit "+"))).alt ((node "opt" ((ref "GrammarExpr.atom").seq (lit "?"))).alt (ref "GrammarExpr.atom"))))),
    ("GrammarExpr.atom", ((node "lit" (ref "Atom.string")).alt ((node "chr" (ref "Atom.char")).alt ((node "ref" (ref "Atom.ident")).alt ((node "group" (((lit "(").seq (ref "GrammarExpr.expr")).seq (lit ")"))).alt ((node "special" (ref "TOKEN.special")).alt (node "empty" (lit "ε"))))))))
  ]
  rules := []
}

/-- File piece -/
def filePiece : Piece := {
  name := "File"
  grammar := [
    ("File.legoFile", ((ref "File.decl").star)),
    ("File.decl", ((ref "File.importDecl").alt ((ref "File.langDecl").alt ((ref "File.tokenDecl").alt ((ref "File.pieceDecl").alt ((ref "File.ruleDecl").alt ((ref "File.typeDecl").alt ((ref "File.testDecl").alt (ref "File.attrsDecl"))))))))),
    ("File.importDecl", (node "DImport" (((lit "import").seq (ref "Atom.ident")).seq (lit ";")))),
    ("File.langDecl", (node "DLang" (((((lit "lang").seq (ref "Atom.ident")).seq ((ref "File.imports").alt empty)).seq (lit ":=")).seq (ref "File.langBody")))),
    ("File.imports", (node "DImports" ((((lit "(").seq (ref "Atom.ident")).seq (((lit ",").seq (ref "Atom.ident")).star)).seq (lit ")")))),
    ("File.langBody", ((ref "File.innerDecl").star)),
    ("File.innerDecl", ((ref "File.tokenDecl").alt ((ref "File.pieceDecl").alt ((ref "File.ruleDecl").alt ((ref "File.typeDecl").alt ((ref "File.testDecl").alt (ref "File.attrsDecl"))))))),
    ("File.tokenDecl", (node "DToken" (((lit "token").seq (ref "Atom.ident")).seq ((ref "File.tokenItem").seq ((ref "File.tokenItem").star))))),
    ("File.tokenItem", (ref "File.prodDecl")),
    ("File.pieceDecl", (node "DPiece" (((lit "piece").seq (ref "Atom.ident")).seq ((ref "File.pieceItem").seq ((ref "File.pieceItem").star))))),
    ("File.pieceItem", ((ref "File.prodDecl").alt ((ref "File.ruleDecl").alt ((ref "File.typeDecl").alt (ref "File.testDecl"))))),
    ("File.prodDecl", (node "DGrammar" ((((ref "Atom.ident").seq (lit "::=")).seq (ref "GrammarExpr.expr")).seq (lit ";")))),
    ("File.ruleDecl", (node "DRule" (((((((lit "rule").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Pattern.pattern")).seq (lit "~>")).seq (ref "Template.template")).seq (lit ";")))),
    ("File.typeDecl", (node "DType" ((((((((lit "type").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Term.term")).seq (lit ":")).seq (ref "Term.term")).seq ((ref "File.whenClause").alt empty)).seq (lit ";")))),
    ("File.whenClause", (node "when" (((lit "when").seq (ref "Term.term")).seq (((lit ",").seq (ref "Term.term")).star)))),
    ("File.testDecl", (node "DTest" ((((((lit "test").seq (ref "Atom.string")).seq (lit ":")).seq (ref "Term.term")).seq (((lit "~~>").seq (ref "Term.term")).alt empty)).seq (lit ";")))),
    ("File.attrsDecl", (node "DAttrs" (((lit "attrs").seq (ref "Atom.ident")).seq (ref "File.attrBody")))),
    ("File.attrBody", ((ref "File.attrItem").star)),
    ("File.attrItem", ((ref "File.attrDecl").alt (ref "File.attrRuleDecl"))),
    ("File.attrDecl", (node "DAttr" (((((ref "File.attrFlow").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Term.term")).seq (lit ";")))),
    ("File.attrFlow", ((node "syn" (lit "syn")).alt (node "inh" (lit "inh")))),
    ("File.attrRuleDecl", (node "DAttrRule" ((((ref "File.attrPath").seq (lit "=")).seq (ref "Term.term")).seq (lit ";")))),
    ("File.attrPath", (node "attrPath" ((ref "Atom.ident").seq (((lit ".").seq (ref "Atom.ident")).star))))
  ]
  rules := []
}

/-! ## Combined Grammar -/

/-- All piece definitions -/
def allPieces : List Piece := [atomPiece, termPiece, patternPiece, templatePiece, grammarExprPiece, filePiece]

/-- Get all productions from all pieces -/
def allProductions : Productions :=
  allPieces.foldl (fun acc p => acc ++ p.grammar) []

end Lego.Generated.Bootstrap
