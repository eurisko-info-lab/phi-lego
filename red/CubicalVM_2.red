-- CubicalVM.redtt
-- Full Cubical VM: Paths, HITs, J eliminator, transports
-- Microcode → RedTT projection + realizer/interpreter

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

-- =====================================================
-- 2. Interval & micro-operations
-- =====================================================

(@) : Term → String → Term
(@) p i =
  case p of
    lamPath j body →
      if i == j then body else lamPath j body
    _ → p

-- =====================================================
-- 3. Path operations
-- =====================================================

projComp : Term → Term → Term
projComp (refl a) p = p
projComp p (refl a) = p
projComp p q = comp p q

projSym : Term → Term
projSym (refl a) = refl a
projSym p = sym p

-- =====================================================
-- 4. J eliminator
-- =====================================================

-- J : Path induction
-- J A C d p reduces to d if p is refl
projJ : Term → Term → Term → Term → Term
projJ A C d (refl a) = d
projJ A C d p = J A C d p

-- =====================================================
-- 5. Transport (Coe) in dependent types
-- =====================================================

projTransport : Term → Term → Term
projTransport (lamPath i body) j = (@ (lamPath i body) j)
projTransport (refl a) x = x
projTransport t x = transport t x

-- =====================================================
-- 6. HITs
-- =====================================================

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
-- 7. VM state
-- =====================================================

record VMState where
  constructor mkState
  term : Term
  ienv : List (String × String)  -- interval variable bindings

-- =====================================================
-- 8. Interpreter / Realizer
-- =====================================================

eval : VMState → Term
eval st =
  let t = st.term in
  case t of
    app (lam x b) a → eval (mkState (projTransport (lamPath x (refl b)) a) st.ienv)
    app f a → app (eval (mkState f st.ienv)) (eval (mkState a st.ienv))

    transport (lamPath i body) j → eval (mkState (@ (lamPath i body) j) st.ienv)
    transport (refl a) x → eval (mkState x st.ienv)
    transport t x → transport (eval (mkState t st.ienv)) (eval (mkState x st.ienv))

    comp (refl a) p → eval (mkState p st.ienv)
    comp p (refl a) → eval (mkState p st.ienv)
    comp p q → comp (eval (mkState p st.ienv)) (eval (mkState q st.ienv))

    sym (refl a) → refl a
    sym p → sym (eval (mkState p st.ienv))

    J A C d (refl a) → eval (mkState d st.ienv)
    J A C d p → J (eval (mkState A st.ienv))
                   (eval (mkState C st.ienv))
                   (eval (mkState d st.ienv))
                   (eval (mkState p st.ienv))

    lam x b → lam x (eval (mkState b st.ienv))
    refl a → refl (eval (mkState a st.ienv))
    lamPath i b → lamPath i (eval (mkState b st.ienv))
    circle → circle
    base → base
    loop → loop
    susp t → susp (eval (mkState t st.ienv))
    trunc t → trunc (eval (mkState t st.ienv))
    nTrunc n t → nTrunc n (eval (mkState t st.ienv))
    var x → var x

-- =====================================================
-- 9. Examples
-- =====================================================

-- Identity function
idTerm : Term
idTerm = lam "x" (var "x")

idApplied : Term
idApplied = eval (mkState (app idTerm (var "y")) [])

-- Circle HIT along endpoints
circleI0 : Term
circleI0 = eval (mkState (projLoop "i0") [])

circleI1 : Term
circleI1 = eval (mkState (projLoop "i1") [])

-- Transport along refl
transportExample : Term
transportExample = eval (mkState (transport (lamPath "i" (refl (var "x"))) "i0") [])

-- Path composition
pathCompExample : Term
pathCompExample = eval (mkState (projComp (refl (var "x")) (refl (var "y"))) [])

-- J eliminator applied to refl
jExample : Term
jExample = eval (mkState (projJ (var "A") (lam "x" (var "B")) (var "d") (refl (var "a"))) [])

-- =====================================================
-- End of CubicalVM.redtt
-- =====================================================
