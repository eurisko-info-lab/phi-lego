-- CubicalVM-HIT.redtt
-- Cubical VM with Higher Inductive Types
-- Extends CubicalVM-Kan with circle, suspension, truncation reductions

module CubicalVMHIT where

import CubicalVMKan

-- =====================================================
-- 1. Circle microcode
-- =====================================================

-- Loop projection: trivial path returns base
projLoop : Term → Term
projLoop (loop) = loop
projLoop t = t

-- Circle transport along path
projTransportCircle : Term → Term
projTransportCircle base = base
projTransportCircle loop = loop

-- =====================================================
-- 2. Suspension (susp)
-- =====================================================

-- suspends a type A over interval [i0,i1]
projSusp : Term → Term
projSusp (susp A) = susp A
projSusp t = t

-- =====================================================
-- 3. Truncations
-- =====================================================

-- trunc n A reduces when n = 0, etc.
projTrunc : Term → Term
projTrunc (trunc A) = trunc A
projTrunc t = t

projNTrunc : Nat → Term → Term
projNTrunc 0 A = Unit  -- 0-trunc collapses to contractible
projNTrunc n A = nTrunc n A

-- =====================================================
-- 4. Extend evaluation to HITs
-- =====================================================

evalHIT : VMState → Term
evalHIT st =
  let t = st.term in
  case t of
    circle → circle
    base → base
    loop → loop
    susp A → projSusp (evalHIT (mkState A st.ienv))
    trunc A → projTrunc (evalHIT (mkState A st.ienv))
    nTrunc n A → projNTrunc n (evalHIT (mkState A st.ienv))
    _ → eval st  -- fallback to previous CubicalVMKan eval

-- =====================================================
-- 5. Example HIT computations
-- =====================================================

-- Circle base transport
circleBaseTest : Term
circleBaseTest = evalHIT (mkState (transport base i1) [])

-- Loop microcode test
loopTest : Term
loopTest = evalHIT (mkState loop [])

-- Suspension example
suspTest : Term
suspTest = evalHIT (mkState (susp (var "A")) [])

-- Truncation example
truncTest0 : Term
truncTest0 = evalHIT (mkState (nTrunc 0 (var "A")) [])
truncTest1 : Term
truncTest1 = evalHIT (mkState (nTrunc 1 (var "A")) [])

-- =====================================================
-- 6. Integration with Coe / HComp
-- =====================================================

-- Coe over HITs
projCoeHIT : Term → Term → Term → Term → Term
projCoeHIT A i j a =
  case A of
    circle → a
    base → a
    loop → loop
    susp t → susp (projCoeHIT t i j a)
    trunc t → trunc (projCoeHIT t i j a)
    nTrunc n t → nTrunc n (projCoeHIT t i j a)
    _ → projCoe A i j a

-- HComp over HITs
projHCompHIT : Term → Term → Term → Term → Term
projHCompHIT A φ a0 a1 =
  case A of
    circle → projHComp A φ a0 a1
    base → a1
    loop → projHComp A φ a0 a1
    susp t → projHCompHIT t φ a0 a1
    trunc t → projHCompHIT t φ a0 a1
    nTrunc n t → projHCompHIT t φ a0 a1
    _ → projHComp A φ a0 a1

-- =====================================================
-- 7. Extended eval
-- =====================================================

evalHITFull : VMState → Term
evalHITFull st =
  let t = st.term in
  case t of
    circle → circle
    base → base
    loop → loop
    susp A → projSusp (evalHITFull (mkState A st.ienv))
    trunc A → projTrunc (evalHITFull (mkState A st.ienv))
    nTrunc n A → projNTrunc n (evalHITFull (mkState A st.ienv))
    coe A i j a → projCoeHIT (evalHITFull (mkState A st.ienv))
                           (evalHITFull (mkState i st.ienv))
                           (evalHITFull (mkState j st.ienv))
                           (evalHITFull (mkState a st.ienv))
    hcomp A φ a0 a1 → projHCompHIT (evalHITFull (mkState A st.ienv))
                                    (evalHITFull (mkState φ st.ienv))
                                    (evalHITFull (mkState a0 st.ienv))
                                    (evalHITFull (mkState a1 st.ienv))
    _ → evalHIT st  -- fallback to coe / Kan evaluation

-- =====================================================
-- End of CubicalVM-HIT.redtt
-- =====================================================
