-- CubicalVMHIT-Tests.redtt
-- Tests for CubicalVMHIT microcoded evaluation

module CubicalVMHITTests where

import CubicalVMHIT

-- =====================================================
-- 1. Circle tests
-- =====================================================

-- Transport base along interval: should stay base
circleBaseTest : Term
circleBaseTest =
  let st = mkState (coe circle i0 i1 base) []
  in evalHITFull st
-- Expected: base

-- Loop evaluation: should stay loop
loopTest : Term
loopTest =
  let st = mkState loop []
  in evalHITFull st
-- Expected: loop

-- =====================================================
-- 2. Suspension tests
-- =====================================================

-- suspends type A over interval
suspTest : Term
suspTest =
  let st = mkState (susp (var "A")) []
  in evalHITFull st
-- Expected: susp (var "A")

-- =====================================================
-- 3. Truncation tests
-- =====================================================

-- 0-trunc collapses to contractible type
truncTest0 : Term
truncTest0 =
  let st = mkState (nTrunc 0 (var "A")) []
  in evalHITFull st
-- Expected: Unit

-- 1-trunc keeps as is
truncTest1 : Term
truncTest1 =
  let st = mkState (nTrunc 1 (var "A")) []
  in evalHITFull st
-- Expected: nTrunc 1 (var "A")

-- =====================================================
-- 4. Coe / Transport tests
-- =====================================================

-- Coe along circle path: base → base
coeCircleTest : Term
coeCircleTest =
  let st = mkState (coe circle i0 i1 base) []
  in evalHITFull st
-- Expected: base

-- Coe along suspension
coeSuspTest : Term
coeSuspTest =
  let st = mkState (coe (susp (var "A")) i0 i1 (var "a")) []
  in evalHITFull st
-- Expected: susp (var "a")

-- =====================================================
-- 5. HComp tests
-- =====================================================

-- HComp over circle: reduces to target at i1
hcompCircleTest : Term
hcompCircleTest =
  let st = mkState (hcomp circle phi base loop) []
  in evalHITFull st
-- Expected: loop

-- HComp over truncation
hcompTruncTest : Term
hcompTruncTest =
  let st = mkState (hcomp (nTrunc 0 (var "A")) phi base loop) []
  in evalHITFull st
-- Expected: Unit

-- =====================================================
-- 6. Path / J tests
-- =====================================================

-- Identity path J applied to refl
jReflTest : Term
jReflTest =
  let st = mkState (J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a"))) []
  in evalHITFull st
-- Expected: lam "x" (var "A") (var "C")

-- =====================================================
-- 7. Circle + loop + coe integration
-- =====================================================

circleLoopCoeTest : Term
circleLoopCoeTest =
  let st = mkState (coe circle i0 i1 loop) []
  in evalHITFull st
-- Expected: loop

-- =====================================================
-- 8. Suspension + HComp integration
-- =====================================================

suspHCompTest : Term
suspHCompTest =
  let st = mkState (hcomp (susp (var "A")) phi (var "a") (var "b")) []
  in evalHITFull st
-- Expected: susp (hcomp (var "A") phi (var "a") (var "b"))

-- =====================================================
-- End of CubicalVMHIT-Tests.redtt
-- =====================================================
