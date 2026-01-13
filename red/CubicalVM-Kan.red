-- CubicalVM-Kan.redtt
-- Cubical VM extended: dependent-path substitution & Kan composition

module CubicalVMKan where

import CubicalVM

-- =====================================================
-- 1. Kan-dependent substitution (for coe / transport)
-- =====================================================

-- Substitute an interval variable along a path
substI : String → Term → Term → Term
substI i j t =
  case t of
    var x → var x
    lam x b → lam x (substI i j b)
    app f a → app (substI i j f) (substI i j a)
    refl a → refl (substI i j a)
    sym p → sym (substI i j p)
    comp p q → comp (substI i j p) (substI i j q)
    lamPath i' b → 
      if i' == i then lamPath i' b else lamPath i' (substI i j b)
    transport A a → transport (substI i j A) (substI i j a)
    coe A i' j' a → coe (substI i j A) (substI i j i') (substI i j j') (substI i j a)
    hcomp A φ a0 a1 → hcomp (substI i j A) (substI i j φ) (substI i j a0) (substI i j a1)
    _ → t  -- circle, base, loop, etc.

-- =====================================================
-- 2. Coe microcode with interval reduction
-- =====================================================

projCoe : Term → Term → Term → Term → Term
projCoe A i j a =
  case (i, j) of
    (i0, i0) → a
    (i1, i1) → a
    (_, _)   → coe A i j a  -- non-trivial: keep coe

-- =====================================================
-- 3. HComp microcode with filling
-- =====================================================

projHComp : Term → Term → Term → Term → Term
projHComp A φ a0 a1 =
  case φ of
    i0 → a0
    i1 → a1
    _  → 
      -- Compute partial filling along φ
      let filledA0 = substI "i" i0 A in
      let filledA1 = substI "i" i1 A in
      hcomp filledA0 φ a0 a1

-- =====================================================
-- 4. Transport along paths
-- =====================================================

projTransport : Term → Term → Term
projTransport (lamPath i body) j =
  substI i j body
projTransport (refl a) x = a
projTransport t x = transport t x

-- =====================================================
-- 5. J eliminator with microcode
-- =====================================================

projJ : Term → Term → Term → Term → Term
projJ A C d (refl a) = d
projJ A C d p = J A C d p

-- =====================================================
-- 6. Evaluation (with Kan rules)
-- =====================================================

eval : VMState → Term
eval st =
  let t = st.term in
  case t of
    app f a → projApp (eval (mkState f st.ienv)) (eval (mkState a st.ienv))
    lam x b → lam x (eval (mkState b st.ienv))

    comp p q → projComp (eval (mkState p st.ienv)) (eval (mkState q st.ienv))
    sym p → projSym (eval (mkState p st.ienv))
    lamPath i b → lamPath i (eval (mkState b st.ienv))

    transport t x → projTransport (eval (mkState t st.ienv)) (eval (mkState x st.ienv))
    J A C d p → projJ (eval (mkState A st.ienv))
                      (eval (mkState C st.ienv))
                      (eval (mkState d st.ienv))
                      (eval (mkState p st.ienv))

    refl a → refl (eval (mkState a st.ienv))
    circle → circle
    base → base
    loop → loop
    susp t → projSusp (eval (mkState t st.ienv))
    trunc t → projTrunc (eval (mkState t st.ienv))
    nTrunc n t → projNTrunc n (eval (mkState t st.ienv))

    i0 → i0
    i1 → i1
    neg i → projNeg (eval (mkState i st.ienv))
    meet i j → projMeet (eval (mkState i st.ienv)) (eval (mkState j st.ienv))
    join i j → projJoin (eval (mkState i st.ienv)) (eval (mkState j st.ienv))

    coe A i j a → projCoe (eval (mkState A st.ienv))
                            (eval (mkState i st.ienv))
                            (eval (mkState j st.ienv))
                            (eval (mkState a st.ienv))

    hcomp A φ a0 a1 → projHComp (eval (mkState A st.ienv))
                                 (eval (mkState φ st.ienv))
                                 (eval (mkState a0 st.ienv))
                                 (eval (mkState a1 st.ienv))

    var x → var x

-- =====================================================
-- 7. Examples / Tests with Kan composition
-- =====================================================

-- Non-trivial coe along interval
coeTest : Term
coeTest = eval (mkState (coe (lamPath "i" (var "A")) i0 i1 (var "a")) [])

-- Non-trivial hcomp along φ
hcompTest : Term
hcompTest = eval (mkState (hcomp (lamPath "i" (var "A")) negI0 (var "a0") (var "a1")) [])

-- Transport along lamPath
transportTest : Term
transportTest = eval (mkState (transport (lamPath "i" (var "x")) i1) [])

-- J applied to refl
jTest : Term
jTest = eval (mkState (projJ (var "A") (lam "x" (var "B")) (var "d") (refl (var "a"))) [])

-- =====================================================
-- End of CubicalVM-Kan.redtt
-- =====================================================
