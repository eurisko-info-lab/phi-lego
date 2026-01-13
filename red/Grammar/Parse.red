-- Grammar/Parse.red
-- Parsing as a cubical relation, not a function
-- Ambiguity becomes higher-dimensional structure

module Grammar.Parse where

open import Grammar.Core
open import Data.List
open import Data.String

------------------------------------------------------------
-- Parse relation
-- Parse G xs A : input tokens xs parse as nonterminal A
------------------------------------------------------------

data Parse (G : Grammar) :
  List String → String → Type where

  parse-prod :
    ∀ {xs A}
    → (p : Production)
    → (Production.lhs p ≡ A)
    → Parse G xs A

------------------------------------------------------------
-- Cubical equality of parses
-- Used to represent ambiguity / coherence
------------------------------------------------------------

data Parse≡ {G xs A} :
  Parse G xs A → Parse G xs A → Type where

  refl : ∀ p → Parse≡ p p
