-- Grammar/Core.red
-- Core definitions for grammars in Lego / RedTT
-- Grammars are structural objects, not strings

module Grammar.Core where

open import Data.List
open import Data.String

------------------------------------------------------------
-- Symbols used in productions
------------------------------------------------------------

data Sym : Type where
  terminal    : String → Sym
  nonterminal : String → Sym

------------------------------------------------------------
-- Productions: A ::= α
------------------------------------------------------------

record Production : Type where
  field
    lhs : String        -- nonterminal name
    rhs : List Sym      -- sequence of symbols

------------------------------------------------------------
-- Grammar = finite set of productions
------------------------------------------------------------

record Grammar : Type where
  field
    prods : List Production
