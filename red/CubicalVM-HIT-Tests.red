-- CubicalVMHIT.redtt
-- Full Cubical VM with HITs, Paths, coe, hcomp
-- Includes automated tests

module CubicalVMHIT where

-----------------------------------------------------
-- 1. Term definitions
-----------------------------------------------------

-- Basic cubical terms
data Term : Type where
  var   : String → Term
  lam   : String → Term → Term → Term
  app   : Term → Term → Term
  Id    : Term → Term → Term → Term
  refl  : Term → Term
  J     : Term → Term → Term → Term → Term
  -- Paths
  pathComp : Term → Term → Term
  pathInv  : Term → Term
  ap       : Term → Term → Term
  apd      : Term → Term → Term
  -- Higher Inductive Types
  circle   : Term
  base     : Term
  loop     : Term
  susp     : Term → Term
  trunc    : ℕ → Term → Term
  nTrunc   : ℕ → Term → Term
  -- Transport / Coe / HComp
  coe      : Term → Term → Term → Term
  hcomp    : Term → Term → Term → Term
  -- Other
  Unit     : Term

-----------------------------------------------------
-- 2. Cubical VM microcode state
-----------------------------------------------------

record State : Type where
  constructor mkState
  term : Term
  env  : List (String × Term)

-- Simple lookup
lookupVar : String → List (String × Term) → Term
lookupVar x [] = var x
lookupVar x ((y,v)::ys) = if x == y then v else lookupVar x ys

-----------------------------------------------------
-- 3. VM evaluation microcode
-----------------------------------------------------

-- Evaluate paths and HITs
evalHITFull : State → Term
evalHITFull (mkState t env) = case t of

  -- Variables
  var x => lookupVar x env

  -- Lambda application
  app (lam x ty body) arg =>
    evalHITFull (mkState body ((x,arg)::env))

  app f a =>
    let f' = evalHITFull (mkState f env)
        a' = evalHITFull (mkState a env)
    in app f' a'

  lam x ty body => lam x (evalHITFull (mkState ty env)) (evalHITFull (mkState body env))

  -- Identity types
  Id A a b => Id (evalHITFull (mkState A env)) (evalHITFull (mkState a env)) (evalHITFull (mkState b env))
  refl a => refl (evalHITFull (mkState a env))
  J A C d (refl a) => evalHITFull (mkState d env)
  J A C d p => J (evalHITFull (mkState A env)) (evalHITFull (mkState C env)) (evalHITFull (mkState d env)) (evalHITFull (mkState p env))

  -- Path operations
  pathComp (refl a) p => evalHITFull (mkState p env)
  pathComp p (refl b) => evalHITFull (mkState p env)
  pathComp p (pathInv p') => refl (evalHITFull (mkState p env))
  pathInv p => pathInv (evalHITFull (mkState p env))
  ap f p => ap (evalHITFull (mkState f env)) (evalHITFull (mkState p env))
  apd f p => apd (evalHITFull (mkState f env)) (evalHITFull (mkState p env))

  -- Higher inductive types
  circle => circle
  base   => base
  loop   => loop
  susp A => susp (evalHITFull (mkState A env))
  trunc n A => if n == 0 then Unit else trunc n (evalHITFull (mkState A env))
  nTrunc n A => if n == 0 then Unit else nTrunc n (evalHITFull (mkState A env))

  -- Transport / Coe
  coe A i0 i1 a => a
  hcomp A φ u v => case A of
                      circle => v
                      trunc 0 _ => Unit
                      susp B => susp (hcomp B φ u v)
                      _      => hcomp (evalHITFull (mkState A env)) (evalHITFull (mkState φ env)) (evalHITFull (mkState u env)) (evalHITFull (mkState v env))

  Unit => Unit

-----------------------------------------------------
-- 4. Automated tests
-----------------------------------------------------

-- Circle tests
circleBaseTest = evalHITFull (mkState (coe circle base base) [])
loopTest       = evalHITFull (mkState loop [])

-- Suspension tests
suspTest       = evalHITFull (mkState (susp (var "A")) [])

-- Truncation tests
truncTest0     = evalHITFull (mkState (nTrunc 0 (var "A")) [])
truncTest1     = evalHITFull (mkState (nTrunc 1 (var "A")) [])

-- Coe / Transport tests
coeCircleTest  = evalHITFull (mkState (coe circle base base) [])
coeSuspTest    = evalHITFull (mkState (coe (susp (var "A")) base base) [])

-- HComp tests
hcompCircleTest = evalHITFull (mkState (hcomp circle (var "φ") base loop) [])
hcompTruncTest  = evalHITFull (mkState (hcomp (nTrunc 0 (var "A")) (var "φ") base loop) [])

-- Path / J tests
jReflTest = evalHITFull (mkState (J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a"))) [])

-- Integration tests
circleLoopCoeTest = evalHITFull (mkState (coe circle loop loop) [])
suspHCompTest     = evalHITFull (mkState (hcomp (susp (var "A")) (var "φ") (var "a") (var "b")) [])

-----------------------------------------------------
-- 5. End of CubicalVMHIT.redtt
-----------------------------------------------------
