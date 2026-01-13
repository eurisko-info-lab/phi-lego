-- CubicalVM.redtt
-- Cubical VM with microcoded rewrite cells and full cubical interval
-- Paths, HITs, transport, J, microcoded interval operations

module CubicalVM where

-- =====================================================
-- 1. Core Terms
-- =====================================================

data Term : Type where
  var : String → Term
  lam : String → Term → Term
  app : Term → Term → Term

  -- Identity / Paths
  refl : Term → Term
  sym : Term → Term
  comp : Term → Term → Term
  lamPath : String → Term → Term
  transport : Term → Term → Term
  J : Term → Term → Term → Term → Term

  -- HITs
  circle : Term
  base : Term
  loop : Term
  susp : Term → Term
  trunc : Term → Term
  nTrunc : Nat → Term → Term

  -- Cubical interval
  i0 : Term
  i1 : Term
  neg : Term → Term
  meet : Term → Term → Term
  join : Term → Term → Term

  -- Kan operations
  coe : Term → Term → Term → Term   -- coe A i j a
  hcomp : Term → Term → Term → Term → Term  -- hcomp A φ a0 a1

-- =====================================================
-- 2. Projection / Microcode Layer
-- =====================================================

-- App / Lam
projApp : Term → Term → Term
projApp (lam x b) a = app (lam x b) a
projApp f a = app f a

-- Path operations
projComp : Term → Term → Term
projComp (refl a) p = p
projComp p (refl a) = p
projComp p q = comp p q

projSym : Term → Term
projSym (refl a) = refl a
projSym p = sym p

projLamPath : String → Term → String → Term
projLamPath i body j = if i == j then body else lamPath i body

projTransport : Term → Term → Term
projTransport (lamPath i body) j = projLamPath i body j
projTransport (refl a) x = x
projTransport t x = transport t x

projJ : Term → Term → Term → Term → Term
projJ A C d (refl a) = d
projJ A C d p = J A C d p

-- Loop / HITs
projLoop : String → Term
projLoop i =
  case i of
    "i0" → base
    "i1" → base
    _    → loop

projSusp : Term → Term
projSusp t = susp t

projTrunc : Term → Term
projTrunc t = trunc t

projNTrunc : Nat → Term → Term
projNTrunc n t = nTrunc n t

-- =====================================================
-- 3. Cubical Interval Projections
-- =====================================================

projNeg : Term → Term
projNeg i =
  case i of
    i0 → i1
    i1 → i0
    _  → neg i

projMeet : Term → Term → Term
projMeet i j =
  case (i, j) of
    (i0, _) → i0
    (_, i0) → i0
    (i1, x) → x
    (x, i1) → x
    _       → meet i j

projJoin : Term → Term → Term
projJoin i j =
  case (i, j) of
    (i1, _) → i1
    (_, i1) → i1
    (i0, x) → x
    (x, i0) → x
    _       → join i j

-- =====================================================
-- 4. Kan / Coe / HComp microcode
-- =====================================================

projCoe : Term → Term → Term → Term
projCoe A i j a =
  if i == j then a else coe A i j a

projHComp : Term → Term → Term → Term → Term
projHComp A φ a0 a1 =
  -- If φ trivial, return a1
  case φ of
    i0 → a0
    i1 → a1
    _  → hcomp A φ a0 a1

-- =====================================================
-- 5. VM State
-- =====================================================

record VMState where
  constructor mkState
  term : Term
  ienv : List (String × String)  -- interval bindings

-- =====================================================
-- 6. Interpreter / Realizer
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
-- 7. Examples / Tests
-- =====================================================

-- Identity function
idTerm : Term
idTerm = lam "x" (var "x")

idApplied : Term
idApplied = eval (mkState (app idTerm (var "y")) [])

-- Circle endpoints
circleI0 : Term
circleI0 = eval (mkState i0 [])

circleI1 : Term
circleI1 = eval (mkState i1 [])

-- Interval operations
negI0 : Term
negI0 = eval (mkState (neg i0) [])

meetExample : Term
meetExample = eval (mkState (meet i0 i1) [])

joinExample : Term
joinExample = eval (mkState (join i0 i1) [])

-- Transport along refl
transportExample : Term
transportExample = eval (mkState (transport (lamPath "i" (refl (var "x"))) i0) [])

-- Coe trivial
coeExample : Term
coeExample = eval (mkState (coe (lamPath "i" (var "A")) i0 i0 (var "a")) [])

-- HComp trivial
hcompExample : Term
hcompExample = eval (mkState (hcomp (lamPath "i" (var "A")) i0 (var "a0") (var "a1")) [])

-- Path composition
pathCompExample : Term
pathCompExample = eval (mkState (projComp (refl (var "x")) (refl (var "y"))) [])

-- J eliminator applied to refl
jExample : Term
jExample = eval (mkState (projJ (var "A") (lam "x" (var "B")) (var "d") (refl (var "a"))) [])

-- =====================================================
-- End of CubicalVM.redtt
-- =====================================================
