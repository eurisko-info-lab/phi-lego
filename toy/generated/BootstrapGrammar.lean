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

/-- Token piece -/
def tokenPiece : Piece := {
  name := "Token"
  level := .token
  grammar := [
    ("Token.digit", ((lit "'0'").alt ((lit "'1'").alt ((lit "'2'").alt ((lit "'3'").alt ((lit "'4'").alt ((lit "'5'").alt ((lit "'6'").alt ((lit "'7'").alt ((lit "'8'").alt (lit "'9'"))))))))))),
    ("Token.lower", ((lit "'a'").alt ((lit "'b'").alt ((lit "'c'").alt ((lit "'d'").alt ((lit "'e'").alt ((lit "'f'").alt ((lit "'g'").alt ((lit "'h'").alt ((lit "'i'").alt ((lit "'j'").alt ((lit "'k'").alt ((lit "'l'").alt ((lit "'m'").alt ((lit "'n'").alt ((lit "'o'").alt ((lit "'p'").alt ((lit "'q'").alt ((lit "'r'").alt ((lit "'s'").alt ((lit "'t'").alt ((lit "'u'").alt ((lit "'v'").alt ((lit "'w'").alt ((lit "'x'").alt ((lit "'y'").alt (lit "'z'"))))))))))))))))))))))))))),
    ("Token.upper", ((lit "'A'").alt ((lit "'B'").alt ((lit "'C'").alt ((lit "'D'").alt ((lit "'E'").alt ((lit "'F'").alt ((lit "'G'").alt ((lit "'H'").alt ((lit "'I'").alt ((lit "'J'").alt ((lit "'K'").alt ((lit "'L'").alt ((lit "'M'").alt ((lit "'N'").alt ((lit "'O'").alt ((lit "'P'").alt ((lit "'Q'").alt ((lit "'R'").alt ((lit "'S'").alt ((lit "'T'").alt ((lit "'U'").alt ((lit "'V'").alt ((lit "'W'").alt ((lit "'X'").alt ((lit "'Y'").alt (lit "'Z'"))))))))))))))))))))))))))),
    ("Token.greek", ((lit "'α'").alt ((lit "'β'").alt ((lit "'γ'").alt ((lit "'δ'").alt ((lit "'ε'").alt ((lit "'ζ'").alt ((lit "'η'").alt ((lit "'θ'").alt ((lit "'ι'").alt ((lit "'κ'").alt ((lit "'λ'").alt ((lit "'μ'").alt ((lit "'ν'").alt ((lit "'ξ'").alt ((lit "'ο'").alt ((lit "'π'").alt ((lit "'ρ'").alt ((lit "'σ'").alt ((lit "'τ'").alt ((lit "'υ'").alt ((lit "'φ'").alt ((lit "'χ'").alt ((lit "'ψ'").alt ((lit "'ω'").alt ((lit "'Α'").alt ((lit "'Β'").alt ((lit "'Γ'").alt ((lit "'Δ'").alt ((lit "'Ε'").alt ((lit "'Ζ'").alt ((lit "'Η'").alt ((lit "'Θ'").alt ((lit "'Ι'").alt ((lit "'Κ'").alt ((lit "'Λ'").alt ((lit "'Μ'").alt ((lit "'Ν'").alt ((lit "'Ξ'").alt ((lit "'Ο'").alt ((lit "'Π'").alt ((lit "'Ρ'").alt ((lit "'Σ'").alt ((lit "'Τ'").alt ((lit "'Υ'").alt ((lit "'Φ'").alt ((lit "'Χ'").alt ((lit "'Ψ'").alt (lit "'Ω'"))))))))))))))))))))))))))))))))))))))))))))))))),
    ("Token.alpha", ((ref "Token.lower").alt ((ref "Token.upper").alt ((ref "Token.greek").alt (lit "'_'"))))),
    ("Token.symch", ((lit "'('").alt ((lit "')'").alt ((lit "'['").alt ((lit "']'").alt ((lit "'{'").alt ((lit "'}'").alt ((lit "'<'").alt ((lit "'>'").alt ((lit "':'").alt ((lit "';'").alt ((lit "','").alt ((lit "'.'").alt ((lit "'|'").alt ((lit "'!'").alt ((lit "'?'").alt ((lit "'@'").alt ((lit "'#'").alt ((lit "'$'").alt ((lit "'%'").alt ((lit "'^'").alt ((lit "'&'").alt ((lit "'*'").alt ((lit "'+'").alt ((lit "'-'").alt ((lit "'='").alt ((lit "'~'").alt ((lit "'/'").alt ((lit "'\\\\'").alt ((lit "'→'").alt ((lit "'←'").alt ((lit "'↔'").alt (lit "'⊕'"))))))))))))))))))))))))))))))))),
    ("Token.ident", ((ref "Token.alpha").seq (((ref "Token.alpha").alt (ref "Token.digit")).star))),
    ("Token.number", ((ref "Token.digit").seq ((ref "Token.digit").star))),
    ("Token.string", (((lit "'\"'").seq ((ref "Token.strchar").star)).seq (lit "'\"'"))),
    ("Token.strchar", (((empty.seq (lit "'\\\\'")).seq (ref "Token.escape")).alt (ref "Token.printable"))),
    ("Token.escape", ((lit "'\"'").alt ((lit "'\\\\'").alt ((lit "'n'").alt ((lit "'t'").alt (lit "'r'")))))),
    ("Token.printable", ((ref "Token.alpha").alt ((ref "Token.digit").alt ((ref "Token.symch").alt (lit "' '")))))
  ]
  rules := []
}

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
    ("Pattern.pattern", ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "con" ((((lit "(").seq (ref "Term.conname")).seq ((ref "Pattern.pattern").star)).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt (node "con" (ref "Atom.ident"))))))
  ]
  rules := []
}

/-- Template piece -/
def templatePiece : Piece := {
  name := "Template"
  grammar := [
    ("Template.template", ((node "var" ((lit "$").seq (ref "Atom.ident"))).alt ((node "con" ((((lit "(").seq (ref "Atom.ident")).seq ((ref "Template.template").star)).seq (lit ")"))).alt ((node "lit" (ref "Atom.string")).alt (node "con" (ref "Atom.ident"))))))
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
    ("File.decl", ((ref "File.importDecl").alt ((ref "File.langDecl").alt ((ref "File.tokenDecl").alt ((ref "File.pieceDecl").alt ((ref "File.ruleDecl").alt (ref "File.testDecl"))))))),
    ("File.importDecl", (node "DImport" (((lit "import").seq (ref "Atom.ident")).seq (lit ";")))),
    ("File.langDecl", (node "DLang" (((((lit "lang").seq (ref "Atom.ident")).seq ((ref "File.imports").alt empty)).seq (lit ":=")).seq (ref "File.langBody")))),
    ("File.imports", (node "DImports" ((((lit "(").seq (ref "Atom.ident")).seq (((lit ",").seq (ref "Atom.ident")).star)).seq (lit ")")))),
    ("File.langBody", ((ref "File.innerDecl").star)),
    ("File.innerDecl", ((ref "File.tokenDecl").alt ((ref "File.pieceDecl").alt ((ref "File.ruleDecl").alt (ref "File.testDecl"))))),
    ("File.tokenDecl", (node "DToken" (((lit "token").seq (ref "Atom.ident")).seq ((ref "File.prodDecl").seq ((ref "File.prodDecl").star))))),
    ("File.pieceDecl", (node "DPiece" (((lit "piece").seq (ref "Atom.ident")).seq ((ref "File.prodDecl").seq ((ref "File.prodDecl").star))))),
    ("File.prodDecl", (node "DGrammar" ((((ref "Atom.ident").seq (lit "::=")).seq (ref "GrammarExpr.expr")).seq (lit ";")))),
    ("File.ruleDecl", (node "DRule" (((((((lit "rule").seq (ref "Atom.ident")).seq (lit ":")).seq (ref "Pattern.pattern")).seq (lit "~>")).seq (ref "Template.template")).seq (lit ";")))),
    ("File.testDecl", (node "DTest" ((((((lit "test").seq (ref "Atom.string")).seq (lit ":")).seq (ref "Term.term")).seq (((lit "~~>").seq (ref "Term.term")).alt empty)).seq (lit ";"))))
  ]
  rules := []
}

/-! ## Combined Grammar -/

/-- All piece definitions -/
def allPieces : List Piece := [tokenPiece, atomPiece, termPiece, patternPiece, templatePiece, grammarExprPiece, filePiece]

/-- Get all productions from all pieces -/
def allProductions : Productions :=
  allPieces.foldl (fun acc p => acc ++ p.grammar) []

end Lego.Generated.Bootstrap
