-- CubicalVMHITStep.redtt
-- Cubical VM with step-by-step evaluation tracing

module CubicalVMHITStep where

-----------------------------------------------------
-- 1. Term definitions
-----------------------------------------------------

data Term : Type where
  var   : String → Term
  lam   : String → Term → Term → Term
  app   : Term → Term → Term
  Id    : Term → Term → Term → Term
  refl  : Term → Term
  J     : Term → Term → Term → Term → Term
  pathComp : Term → Term → Term
  pathInv  : Term → Term
  ap       : Term → Term → Term
  apd      : Term → Term → Term
  circle   : Term
  base     : Term
  loop     : Term
  susp     : Term → Term
  trunc    : ℕ → Term → Term
  nTrunc   : ℕ → Term → Term
  coe      : Term → Term → Term → Term
  hcomp    : Term → Term → Term → Term
  Unit     : Term

-----------------------------------------------------
-- 2. VM state
-----------------------------------------------------

record State : Type where
  constructor mkState
  term : Term
  env  : List (String × Term)

lookupVar : String → List (String × Term) → Term
lookupVar x [] = var x
lookupVar x ((y,v)::ys) = if x == y then v else lookupVar x ys

-----------------------------------------------------
-- 3. Stepper microcode: single-step evaluation
-----------------------------------------------------

step : State → Maybe State
step (mkState t env) = case t of

  -- Variables
  var x => Nothing

  -- Beta reduction
  app (lam x ty body) arg => Just (mkState body ((x,arg)::env))
  app f a => case step (mkState f env) of
               Just f' => Just (mkState (app f' a) env)
               Nothing => case step (mkState a env) of
                            Just a' => Just (mkState (app f a') env)
                            Nothing => Nothing

  lam x ty body => case step (mkState ty env) of
                     Just ty' => Just (mkState (lam x ty' body) env)
                     Nothing => case step (mkState body env) of
                                  Just b' => Just (mkState (lam x ty b') env)
                                  Nothing => Nothing

  -- Identity types
  J A C d (refl a) => Just (mkState d env)
  J A C d p => case step (mkState p env) of
                 Just p' => Just (mkState (J A C d p') env)
                 Nothing => Nothing
  Id A a b => case step (mkState A env) of
                Just A' => Just (mkState (Id A' a b) env)
                Nothing => case step (mkState a env) of
                             Just a' => Just (mkState (Id A a' b) env)
                             Nothing => case step (mkState b env) of
                                          Just b' => Just (mkState (Id A a b') env)
                                          Nothing => Nothing
  refl a => case step (mkState a env) of
              Just a' => Just (mkState (refl a') env)
              Nothing => Nothing

  -- Path operations
  pathComp (refl a) p => Just (mkState p env)
  pathComp p (refl b) => Just (mkState p env)
  pathComp p (pathInv p') => Just (mkState (refl p) env)
  pathComp p q => case step (mkState p env) of
                    Just p' => Just (mkState (pathComp p' q) env)
                    Nothing => case step (mkState q env) of
                                 Just q' => Just (mkState (pathComp p q') env)
                                 Nothing => Nothing
  pathInv p => case step (mkState p env) of
                 Just p' => Just (mkState (pathInv p') env)
                 Nothing => Nothing
  ap f p => case step (mkState f env) of
              Just f' => Just (mkState (ap f' p) env)
              Nothing => case step (mkState p env) of
                           Just p' => Just (mkState (ap f p') env)
                           Nothing => Nothing
  apd f p => case step (mkState f env) of
               Just f' => Just (mkState (apd f' p) env)
               Nothing => case step (mkState p env) of
                            Just p' => Just (mkState (apd f p') env)
                            Nothing => Nothing

  -- HITs
  circle => Nothing
  base   => Nothing
  loop   => Nothing
  susp A => case step (mkState A env) of
              Just A' => Just (mkState (susp A') env)
              Nothing => Nothing
  trunc n A => if n == 0 then Nothing else case step (mkState A env) of
                                             Just A' => Just (mkState (trunc n A') env)
                                             Nothing => Nothing
  nTrunc n A => if n == 0 then Nothing else case step (mkState A env) of
                                              Just A' => Just (mkState (nTrunc n A') env)
                                              Nothing => Nothing

  -- Transport / Coe / HComp
  coe A i0 i1 => Just (mkState i0 env)
  hcomp A φ u v => case A of
                     circle => Just (mkState v env)
                     trunc 0 _ => Just (mkState Unit env)
                     susp B => Just (mkState (susp (hcomp B φ u v)) env)
                     _ => Nothing

  Unit => Nothing

-----------------------------------------------------
-- 4. Full evaluation using stepper
-----------------------------------------------------

evalTrace : State → List Term
evalTrace st = case step st of
                 Just st' => (term st) :: evalTrace st'
                 Nothing  => [term st]

evalTerm : Term → List Term
evalTerm t = evalTrace (mkState t [])

-----------------------------------------------------
-- 5. Stepper / trace tests
-----------------------------------------------------

-- Example: J with refl
jTraceTest = evalTerm (J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a")))

-- Circle + coe trace
circleCoeTrace = evalTerm (coe circle base loop)

-- HComp trace
hcompTrace = evalTerm (hcomp circle (var "φ") base loop)

-- Path composition trace
pathTrace = evalTerm (pathComp (refl (var "a")) (var "p"))

-- Suspension trace
suspTrace = evalTerm (susp (var "A"))

-- Truncation trace
truncTrace0 = evalTerm (nTrunc 0 (var "A"))
truncTrace1 = evalTerm (nTrunc 1 (var "A"))

-----------------------------------------------------
-- 6. End of CubicalVMHITStep.redtt
-----------------------------------------------------
