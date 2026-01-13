-- CubicalVM.redtt
-- Projection & Realizer for Lego Cubical VM → RedTT

module CubicalVM where

-- =====================================================
-- 1. RedTT Term Projection
-- =====================================================

-- Core Cubical Terms
data Term : Type where
  var : String → Term
  lam : String → Term → Term
  app : Term → Term → Term
  refl : Term → Term
  sym : Term → Term
  comp : Term → Term → Term
  lamPath : String → Term → Term
  transport : Term → Term → Term
  circle : Term
  base : Term
  loop : Term

-- Projection functions: Lego → RedTT
-- Here we translate each Lego piece into a RedTT term

-- Identity / J
projJ : Term → Term → Term → Term → Term
projJ A C d p =
  transport (lamPath "i" (refl d)) p

-- Path operations
projComp : Term → Term → Term
projComp (refl a) p = p
projComp p (refl a) = p
projComp p q = comp p q

projSym : Term → Term
projSym (refl a) = refl a
projSym p = sym p

-- HITs (circle)
projLoop : Term → Term
projLoop i =
  case i of
    "i0" → base
    "i1" → base
    _    → loop

-- INet β as path
projBeta : Term → Term → Term
projBeta (lam x b) a =
  transport (lamPath x (refl b)) a
projBeta t1 t2 = app t1 t2

-- =====================================================
-- 2. Realizer / Interpreter
-- =====================================================

-- The VM state: term + interval environment
record VMState where
  constructor mkState
  term : Term
  ienv : List (String × String)  -- interval variable bindings

-- Evaluate term along a path
eval : VMState → Term
eval st =
  let t = st.term in
  case t of
    app (lam x b) a → eval (mkState (projBeta (lam x b) a) st.ienv)
    transport (lamPath i p) j →
      -- Kan filling along the interval
      case j of
        "i0" → eval (mkState (@ p "i0") st.ienv)
        "i1" → eval (mkState (@ p "i1") st.ienv)
        _    → transport (lamPath i p) j
    transport (refl a) x → eval (mkState x st.ienv)
    comp (refl a) p → eval (mkState p st.ienv)
    comp p (refl a) → eval (mkState p st.ienv)
    sym (refl a) → eval (mkState (refl a) st.ienv)
    lam x b → lam x (eval (mkState b st.ienv))
    app f a → app (eval (mkState f st.ienv)) (eval (mkState a st.ienv))
    _ → t

-- =====================================================
-- 3. Utilities for Interval & Path Filling
-- =====================================================

-- Apply interval substitution
(@) : Term → String → Term
(@) p i =
  case p of
    lamPath j body →
      if i == j then body else lamPath j body
    _ → p

-- =====================================================
-- 4. Example: Identity function
-- =====================================================

idTerm : Term
idTerm = lam "x" (var "x")

idApplied : Term
idApplied = eval (mkState (app idTerm (var "y")) [])

-- =====================================================
-- 5. Example: Circle HIT
-- =====================================================

circleAtI0 : Term
circleAtI0 = eval (mkState (projLoop "i0") [])

circleAtI1 : Term
circleAtI1 = eval (mkState (projLoop "i1") [])

-- =====================================================
-- End of CubicalVM.redtt
-- =====================================================
