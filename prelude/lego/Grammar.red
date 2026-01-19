import prelude
import data.list
import data.string

data Atom where
| char
| chars
| ident
| metavar
| number
| regex
| reserved
| string

data File where
| autocutDecl
| commentDecl
| commentText
| defDecl
| fileDecl
| fileDeclWithWs
| grammarDecl
| grammarProd (name : ident) (rhs : grammarExprFull)
| importDecl
| inheritDecl
| langDecl
| langDirectBody
| langItem
| langItemWithWs
| langParent
| langParents
| langParentsOpt
| lawDecl
| lawOp
| legoFile (decls : list (fileDeclWithWs))
| pieceDecl
| pieceItem
| productionWithWs
| qualIdent
| ruleDecl
| ruleArrow
| ruleStub
| sectionMarker
| testDecl
| testExpected
| testOpts
| testOpt
| whitespace

data GrammarExpr where
| altContinuation (alt2 : grammarAlt)
| grammarAlt
| grammarAltTerm
| grammarAtom
| grammarAtomTerm
| grammarExpr
| grammarExprFull (rhs : grammarExpr)
| grammarExprTerm
| grammarSeq (seq1 : grammarSuffix)
| grammarSeqTerm
| grammarSuffix
| grammarSuffixTerm
| grammarWhitespace
| production (name : ident) (rhs : grammarExpr)
| productionNode

data Pattern where
| pattern

data Rule where
| guard (c : term)
| rule

data Template where
| template

data Term where
| term
| typedBinder

data Test where
| test
| testOptions
| testOption

def parse-print-roundtrip : (t : term) → path term (parse (print t)) t =
  -- TODO: prove by induction on term structure
  elim [...]