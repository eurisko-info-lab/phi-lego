-- Pipeline.red
-- End-to-end Lego pipeline inside cubical type theory

module Pipeline where

open import Grammar.Core
open import Grammar.Parse
open import Grammar.Pushout
open import Grammar.ParsePushout
open import Rewrite.Core
open import Rewrite.Compose

------------------------------------------------------------
-- Conceptual pipeline:
--
-- Grammar
--   ↓ pushout
-- Grammar
--   ↓ parse (cubical)
-- Syntax tree
--   ↓ rewrite paths
-- Normal form
------------------------------------------------------------

PipelineInvariant :
  ∀ {G₀ G₁ G₂ xs A}
  → Pushout G₀ G₁ G₂
  → Parse G₁ xs A
  → Parse G₂ xs A
  → Type
PipelineInvariant po p₁ p₂ =
  Parse≡ (parse-left po p₁)
          (parse-right po p₂)
