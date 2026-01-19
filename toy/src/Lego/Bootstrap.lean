/-
  Lego.Bootstrap: The Seed Grammar (hardcoded)

  PURPOSE: Parse Bootstrap.lego ONCE to get the real grammar.

  This module is the "seed" that breaks the chicken-and-egg problem:
  - We need a grammar to parse Bootstrap.lego
  - Bootstrap.lego defines the grammar
  - This hardcoded seed parses Bootstrap.lego
  - Then Runtime.lean uses the PARSED grammar for everything else

  Architecture:
    ┌─────────────────────┐
    │  This Module        │ ──parses──▶ Bootstrap.lego
    │  (hardcoded seed)   │                   │
    └─────────────────────┘                   │
                                              ▼
                                      ┌─────────────────┐
                                      │ Runtime Grammar │ ──parses──▶ *.lego
                                      │ (from Bootstrap)│
                                      └─────────────────┘

  The hardcoded parts (in generated/):
  - BootstrapGrammar.lean: grammar productions
  - BootstrapTokenizer.lean: character-level tokenizer
  - BootstrapRules.lean: interpreter rules

  To regenerate (if Bootstrap.lego changes):
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
