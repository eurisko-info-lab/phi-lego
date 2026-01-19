/-
  Generated Grammar from Bootstrap.lego

  This module contains ONLY the grammar piece definitions.
  Import this from your hand-written Bootstrap.lean to use
  the generated grammar while keeping hand-written tokenizer
  and other infrastructure.

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
    ("Term.term", ((node "metabinder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Term.term"))).alt ((node "metavar" ((lit "$").seq (ref "Atom.ident"))).alt ((node "ctxext" (((((((lit "[").seq (lit "$")).seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Term.term")).seq (lit "]")).seq (ref "Term.term"))).alt ((node "metasubst" (((((((lit "[").seq (lit "$")).seq (ref "Atom.ident")).seq (lit ":=")).seq (ref "Term.term")).seq (lit "]")).seq (ref "Term.term"))).alt ((node "binder" (((ref "Atom.ident").seq (lit ".")).seq (ref "Term.term"))).alt ((node "var" (ref "Atom.ident")).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "paren" (((lit "(").seq (ref "Term.termInner")).seq (lit ")")))))))))))),
    ("Term.termInner", (node "con" ((ref "Term.conname").seq ((ref "Term.termArg").star)))),
    ("Term.termArg", ((node "metabinder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Term.term"))).alt ((node "typed" ((((((lit "$").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Term.term")).seq (lit ".")).seq (ref "Term.term"))).alt ((node "metavar" ((lit "$").seq (ref "Atom.ident"))).alt ((node "colon" (lit ":")).alt ((node "dot" (lit ".")).alt ((node "arrow" (lit "→")).alt ((node "times" (lit "×")).alt ((node "join" (lit "∨")).alt ((node "meet" (lit "∧")).alt ((node "eq" (lit "=")).alt (node "arg" (ref "Term.term"))))))))))))),
    ("Term.conname", ((ref "Atom.ident").alt (ref "TOKEN.sym")))
  ]
  rules := []
}

/-- Pattern piece -/
def patternPiece : Piece := {
  name := "Pattern"
  grammar := [
    ("Pattern.pattern", ((node "binder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Pattern.pattern"))).alt ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "subst" (((((((lit "[").seq (lit "$")).seq (ref "Atom.ident")).seq (lit ":=")).seq (ref "Pattern.pattern")).seq (lit "]")).seq (ref "Pattern.pattern"))).alt ((node "paren" (((lit "(").seq (ref "Pattern.patternSeq")).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "con" (ref "Atom.ident"))))))))),
    ("Pattern.patternSeq", (node "seq" ((ref "Pattern.patternElem").seq ((ref "Pattern.patternElem").star)))),
    ("Pattern.patternElem", ((node "binder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Pattern.pattern"))).alt ((node "typed" ((((((lit "$").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Pattern.pattern")).seq (lit ".")).seq (ref "Pattern.pattern"))).alt ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "nested" (((lit "(").seq (ref "Pattern.patternSeq")).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt ((node "dot" (lit ".")).alt ((node "colon" (lit ":")).alt ((node "arrow" (lit "→")).alt ((node "tilde" (lit "~>")).alt ((node "times" (lit "×")).alt ((node "join" (lit "∨")).alt ((node "meet" (lit "∧")).alt ((node "eq" (lit "=")).alt (node "id" (ref "Atom.ident")))))))))))))))))
  ]
  rules := []
}

/-- Template piece -/
def templatePiece : Piece := {
  name := "Template"
  grammar := [
    ("Template.template", ((node "binder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Template.template"))).alt ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "subst" (((((((lit "[").seq (lit "$")).seq (ref "Atom.ident")).seq (lit ":=")).seq (ref "Template.template")).seq (lit "]")).seq (ref "Template.template"))).alt ((node "paren" (((lit "(").seq (ref "Template.templateSeq")).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt (node "con" (ref "Atom.ident"))))))))),
    ("Template.templateSeq", (node "seq" ((ref "Template.templateElem").seq ((ref "Template.templateElem").star)))),
    ("Template.templateElem", ((node "binder" ((((lit "$").seq (ref "Atom.ident")).seq (lit ".")).seq (ref "Template.template"))).alt ((node "typed" ((((((lit "$").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Template.template")).seq (lit ".")).seq (ref "Template.template"))).alt ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "nested" (((lit "(").seq (ref "Template.templateSeq")).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt ((node "num" (ref "Atom.number")).alt ((node "dot" (lit ".")).alt ((node "colon" (lit ":")).alt ((node "arrow" (lit "→")).alt ((node "tilde" (lit "~>")).alt ((node "times" (lit "×")).alt ((node "join" (lit "∨")).alt ((node "meet" (lit "∧")).alt ((node "eq" (lit "=")).alt (node "id" (ref "Atom.ident")))))))))))))))))
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
    ("File.ruleDecl", (node "DRule" ((((((((lit "rule").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Pattern.pattern")).seq (lit "~>")).seq (ref "Template.template")).seq ((ref "File.ruleGuard").alt empty)).seq (lit ";")))),
    ("File.ruleGuard", (node "guard" ((lit "when").seq (ref "Term.term")))),
    ("File.typeDecl", (node "DType" ((((((lit "type").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "File.typeJudgment")).seq ((ref "File.whenClause").alt empty)).seq (lit ";")))),
    ("File.typeJudgment", (node "judgment" ((ref "Term.term").seq (((lit ":").seq (ref "Term.term")).star)))),
    ("File.whenClause", (node "when" (((lit "when").seq (ref "File.whenCond")).seq (((lit ",").seq (ref "File.whenCond")).star)))),
    ("File.whenCond", ((node "equality" (((ref "Term.term").seq (lit "=")).seq (ref "Term.term"))).alt (node "typing" ((ref "Term.term").seq (((lit ":").seq (ref "Term.term")).alt empty))))),
    ("File.testDecl", (node "DTest" (((((((lit "test").seq (ref "Atom.string")).seq (lit ":")).seq (ref "Term.term")).seq (((lit "~~>").seq (ref "Term.term")).alt empty)).seq (((lit ":").seq (ref "Term.term")).alt empty)).seq (lit ";")))),
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
