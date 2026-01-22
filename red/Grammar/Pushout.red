-- Grammar/Pushout.red
-- Grammar morphisms and pushouts
-- This is the categorical backbone of Lego composition

module Grammar.Pushout where

open import Grammar.Core

------------------------------------------------------------
-- Grammar morphism
------------------------------------------------------------

record GMap (G₁ G₂ : Grammar) : Type where
  field
    mapProd : Production → Production

------------------------------------------------------------
-- Pushout of grammars
-- G₁ ⊔ G₂ glued along G₀
------------------------------------------------------------

record Pushout (G₀ G₁ G₂ : Grammar) : Type where
  field
    G⊔ : Grammar
    ι₁ : GMap G₁ G⊔
    ι₂ : GMap G₂ G⊔
