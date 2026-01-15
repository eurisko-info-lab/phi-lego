/-
  Lego.Bootstrap: The Meta-Grammar (pre-compiled)

  This is exactly like Grammar.sexpr - a pre-compiled grammar that can parse
  other grammars. But structurally it's just another Language, not special.

  The grammar pieces are generated from Bootstrap.lego.
  The tokenizer is also in generated/ (hand-written initially, eventually generated).
  The rules are generated from Bootstrap.lego.

  To regenerate:
    lake exe tolean --grammar test/Bootstrap.lego -o generated/BootstrapGrammar.lean
    lake exe tolean --tokenizer test/Bootstrap.lego -o generated/BootstrapTokenizer.lean
    lake exe tolean --rules test/Bootstrap.lego -o generated/BootstrapRules.lean
-/

import Lego.Algebra
import Lego.Interp
import BootstrapGrammar
import BootstrapTokenizer
import BootstrapRules

namespace Lego.Bootstrap

open GrammarExpr

/-! ## Grammar (imported from generated) -/

def allPieces := Lego.Generated.Bootstrap.allPieces

/-- The complete Meta language -/
def metaGrammar : Language := {
  name := "Meta"
  pieces := allPieces
}

/-- Build the interpreter for parsing .lego files -/
def metaInterp : LangInterp := metaGrammar.toInterp "File.legoFile"

/-! ## Tokenizer (imported from generated) -/

def tokenize := Lego.Generated.Bootstrap.tokenize

/-! ## Rules (imported from generated) -/

def allRules := Lego.Generated.Bootstrap.allRules
def ruleInterp := Lego.Generated.Bootstrap.ruleInterp
def normalize := Lego.Generated.Bootstrap.normalize

/-! ## Parsing -/

/-- Parse a .lego file into declarations -/
def parseLegoFile (content : String) : Option Term :=
  metaInterp.parse (tokenize content)

end Lego.Bootstrap
