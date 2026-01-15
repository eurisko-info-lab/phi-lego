/-
  Lego.Bootstrap: The Meta-Grammar (pre-compiled)

  This is exactly like Grammar.sexpr - a pre-compiled grammar that can parse
  other grammars. But structurally it's just another Language, not special.

  The grammar pieces are generated from Bootstrap.lego.
  The tokenizer is also in generated/ (hand-written initially, eventually generated).

  To regenerate:
    lake exe tolean --grammar test/Bootstrap.lego -o generated/BootstrapGrammar.lean
    lake exe tolean --tokenizer test/Bootstrap.lego -o generated/BootstrapTokenizer.lean
-/

import Lego.Algebra
import Lego.Interp
import BootstrapGrammar
import BootstrapTokenizer

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

/-! ## Parsing -/

/-- Parse a .lego file into declarations -/
def parseLegoFile (content : String) : Option Term :=
  metaInterp.parse (tokenize content)

end Lego.Bootstrap
