-- Grammar/ParsePushout.red
-- Parsing is stable under grammar pushouts
-- Ambiguity yields cubical paths

module Grammar.ParsePushout where

open import Grammar.Core
open import Grammar.Parse
open import Grammar.Pushout

------------------------------------------------------------
-- Left injection preserves parses
------------------------------------------------------------

parse-left :
  ∀ {G₀ G₁ G₂ xs A}
  → (po : Pushout G₀ G₁ G₂)
  → Parse G₁ xs A
  → Parse (Pushout.G⊔ po) xs A
parse-left po p = p

------------------------------------------------------------
-- Right injection preserves parses
------------------------------------------------------------

parse-right :
  ∀ {G₀ G₁ G₂ xs A}
  → (po : Pushout G₀ G₁ G₂)
  → Parse G₂ xs A
  → Parse (Pushout.G⊔ po) xs A
parse-right po p = p

------------------------------------------------------------
-- Coherence: same input parsed two ways
-- gives a cubical path
------------------------------------------------------------

parse-coherence :
  ∀ {G₀ G₁ G₂ xs A}
  → (po : Pushout G₀ G₁ G₂)
  → (p₁ : Parse G₁ xs A)
  → (p₂ : Parse G₂ xs A)
  → Parse≡ (parse-left po p₁)
            (parse-right po p₂)
parse-coherence po p₁ p₂ = refl _
