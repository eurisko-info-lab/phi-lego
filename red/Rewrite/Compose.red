-- Rewrite/Compose.red
-- Composition and normalization as path composition

module Rewrite.Compose where

open import Rewrite.Core

------------------------------------------------------------
-- Rewrite composition
------------------------------------------------------------

compose :
  ∀ {t u v}
  → Rewrite t u
  → Rewrite u v
  → Rewrite t v
compose r₁ r₂ = step
