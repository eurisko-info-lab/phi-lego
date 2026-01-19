import Init

namespace Generated

inductive Atom where
  | char
  | chars
  | ident
  | metavar
  | number
  | regex
  | reserved
  | string
  deriving Repr, BEq, Inhabited

inductive File where
  | autocutDecl
  | commentDecl
  | commentText
  | defDecl
  | fileDecl
  | fileDeclWithWs
  | grammarDecl
  | grammarProd : name : String → rhs : GrammarExprFull → _
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
  | legoFile : decls : List (FileDeclWithWs) → _
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
  deriving Repr, BEq, Inhabited

inductive GrammarExpr where
  | altContinuation : alt2 : GrammarAlt → _
  | grammarAlt
  | grammarAltTerm
  | grammarAtom
  | grammarAtomTerm
  | grammarExpr
  | grammarExprFull : rhs : GrammarExpr → _
  | grammarExprTerm
  | grammarSeq : seq1 : GrammarSuffix → _
  | grammarSeqTerm
  | grammarSuffix
  | grammarSuffixTerm
  | grammarWhitespace
  | production : name : String → rhs : GrammarExpr → _
  | productionNode
  deriving Repr, BEq, Inhabited

inductive Pattern where
  | pattern
  deriving Repr, BEq, Inhabited

inductive Rule where
  | guard : c : Term → _
  | rule
  deriving Repr, BEq, Inhabited

inductive Template where
  | template
  deriving Repr, BEq, Inhabited

inductive Term where
  | term
  | typedBinder
  deriving Repr, BEq, Inhabited

inductive Test where
  | test
  | testOptions
  | testOption
  deriving Repr, BEq, Inhabited

structure Iso where
  forward : α → Option β
  backward : β → Option α
  deriving Repr, BEq

structure Rule where
  name : String
  lhs : Term
  rhs : Term
  deriving Repr, BEq



end Generated