-- Rewrite/Core.red
-- Rewriting as a cubical relation
-- This matches Lego's ~> semantics

module Rewrite.Core where

open import Data.List
open import Data.String

------------------------------------------------------------
-- Terms
------------------------------------------------------------

data Term : Type where
  var : String → Term
  con : String → List Term → Term

------------------------------------------------------------
-- One-step rewrite relation
------------------------------------------------------------

data Rewrite : Term → Term → Type where
  step : ∀ {t u} → Rewrite t u

------------------------------------------------------------
-- Cubical equality between rewrites
------------------------------------------------------------

data Rewrite≡ {t u} :
  Rewrite t u → Rewrite t u → Type where

  refl : ∀ r → Rewrite≡ r r
