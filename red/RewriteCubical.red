-- RewriteCubical.redtt
-- Single-file cubical rewrite universe for Lego
-- Rewriting = Paths, Confluence = Squares, Computation = Transport

module RewriteCubical where

open import Cubical.Core
open import Cubical.Path
open import Cubical.Transport

------------------------------------------------------------
-- 1. Syntax: Generic Terms
------------------------------------------------------------

data Term : Type where
  var  : String → Term
  con  : String → List Term → Term

------------------------------------------------------------
-- 2. Rewrite = Path
------------------------------------------------------------

Rewrite₁ : Term → Term → Type
Rewrite₁ t u = Path Term t u

------------------------------------------------------------
-- 3. Composition of rewrites
------------------------------------------------------------

rewrite-comp :
  ∀ {t u v}
  → Rewrite₁ t u
  → Rewrite₁ u v
  → Rewrite₁ t v
rewrite-comp = _∙_

------------------------------------------------------------
-- 4. Transport = Evaluation
------------------------------------------------------------

eval :
  ∀ {t u}
  → Rewrite₁ t u
  → Term
  → Term
eval r x = transport (λ _ → Term) r x

------------------------------------------------------------
-- 5. Lambda Calculus (compiled Lego rules)
------------------------------------------------------------

-- β-reduction
beta :
  ∀ {x t body arg}
  → Rewrite₁
      (con "app"
        [ con "lam" [ var x , t , body ]
        , arg ])
      body

------------------------------------------------------------
-- 6. Path Operations (HoTT / Cubical)
------------------------------------------------------------

refl-path :
  ∀ {a}
  → Rewrite₁ (con "refl" [a]) (con "refl" [a])

path-comp-refl-l :
  ∀ {a p}
  → Rewrite₁
      (con "·" [ con "refl" [a] , p ])
      p

path-comp-refl-r :
  ∀ {p b}
  → Rewrite₁
      (con "·" [ p , con "refl" [b] ])
      p

path-inverse :
  ∀ {a p}
  → Rewrite₁
      (con "·" [ p , con "⁻¹" [p] ])
      (con "refl" [a])

------------------------------------------------------------
-- 7. Cubical Interval
------------------------------------------------------------

i0 i1 : Term

interval-meet-i0 :
  ∀ {x}
  → Rewrite₁ (con "∧" [i0 , x]) i0

interval-join-i1 :
  ∀ {x}
  → Rewrite₁ (con "∨" [i1 , x]) i1

interval-rev-i0 :
  Rewrite₁ (con "~" [i0]) i1

interval-rev-i1 :
  Rewrite₁ (con "~" [i1]) i0

------------------------------------------------------------
-- 8. Transport (coe)
------------------------------------------------------------

transp-i1 :
  ∀ {A a}
  → Rewrite₁ (con "transp" [A , i1 , a]) a

transp-const :
  ∀ {A φ a}
  → Rewrite₁
      (con "transp"
        [ con "lam" [ var "i" , A ]
        , φ
        , a ])
      a

------------------------------------------------------------
-- 9. Interaction Nets (Graphs as Terms)
------------------------------------------------------------

data Net : Type

RewriteNet : Net → Net → Type
RewriteNet n m = Path Net n m

beta-net :
  ∀ {l a}
  → RewriteNet
      (con "active" [ con "lam" [l] , con "app" [a] ])
      (con "rewire" [l , a])

dup-dup :
  ∀ {d1 d2}
  → RewriteNet
      (con "active" [ con "dup" [d1] , con "dup" [d2] ])
      (con "wire" [d1 , d2])

------------------------------------------------------------
-- 10. Confluence = Squares
------------------------------------------------------------

Square :
  ∀ {A}
  → A → A → A → A → Type
Square a b c d =
  Path (Path A a d)
       (_∙_)
       (_∙_)

beta-critical :
  ∀ {a}
  → Square
      (con "·" [ con "refl" [a] , con "refl" [a] ])
      (con "refl" [a])
      (con "refl" [a])
      (con "refl" [a])

------------------------------------------------------------
-- 11. Higher Structure (free, optional)
------------------------------------------------------------

Cube :
  ∀ {A}
  → A → A → A → A → A → A → A → A → Type
Cube _ _ _ _ _ _ _ _ = Type

------------------------------------------------------------
-- 12. Meaning
------------------------------------------------------------

-- • Every Lego rewrite rule = Path constructor
-- • Every evaluation = Transport
-- • Every critical pair = Square
-- • INets, LC, HoTT share one engine
-- • VM = Cubical normalizer
-- • Optimization = path contraction

