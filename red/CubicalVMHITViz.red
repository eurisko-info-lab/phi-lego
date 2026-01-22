-- CubicalVMHITViz.redtt
-- Cubical VM + interactive net trace visualization

module CubicalVMHITViz where

-----------------------------------------------------
-- 1. Terms (same as previous)
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
-- 2. VM state with net representation
-----------------------------------------------------

record Node : Type where
  constructor mkNode
  id   : ℕ
  kind : String
  term : Term

record Edge : Type where
  constructor mkEdge
  from : ℕ
  to   : ℕ

record State : Type where
  constructor mkState
  term  : Term
  env   : List (String × Term)
  nodes : List Node
  edges : List Edge
  counter : ℕ  -- fresh node IDs

lookupVar : String → List (String × Term) → Term
lookupVar x [] = var x
lookupVar x ((y,v)::ys) = if x == y then v else lookupVar x ys

freshNode : String → Term → State → (Node × State)
freshNode kind t st =
  let n = counter st
  in (mkNode n kind t, mkState (term st) (env st) ((mkNode n kind t)::nodes st) (edges st) (n+1))

-----------------------------------------------------
-- 3. Stepper microcode with net updates
-----------------------------------------------------

step : State → Maybe State
step st = let t = term st in
  case t of
    var x => Nothing

    app (lam x ty body) arg =>
      let st' = mkState body ((x,arg)::env st) (nodes st) (edges st) (counter st)
      in Just st'

    app f a =>
      case step (mkState f (env st) (nodes st) (edges st) (counter st)) of
        Just stf => Just (mkState (app (term stf) a) (env stf) (nodes stf) (edges stf) (counter stf))
        Nothing =>
          case step (mkState a (env st) (nodes st) (edges st) (counter st)) of
            Just sta => Just (mkState (app f (term sta)) (env sta) (nodes sta) (edges sta) (counter sta))
            Nothing => Nothing

    lam x ty body =>
      case step (mkState ty (env st) (nodes st) (edges st) (counter st)) of
        Just sty => Just (mkState (lam x (term sty) body) (env sty) (nodes sty) (edges sty) (counter sty))
        Nothing =>
          case step (mkState body (env st) (nodes st) (edges st) (counter st)) of
            Just sb => Just (mkState (lam x ty (term sb)) (env sb) (nodes sb) (edges sb) (counter sb))
            Nothing => Nothing

    -- HITs / paths
    J A C d (refl a) => Just (mkState d (env st) (nodes st) (edges st) (counter st))
    J A C d p => case step (mkState p (env st) (nodes st) (edges st) (counter st)) of
                   Just sp => Just (mkState (J A C d (term sp)) (env sp) (nodes sp) (edges sp) (counter sp))
                   Nothing => Nothing

    refl a => case step (mkState a (env st) (nodes st) (edges st) (counter st)) of
                Just sa => Just (mkState (refl (term sa)) (env sa) (nodes sa) (edges sa) (counter sa))
                Nothing => Nothing

    pathComp (refl a) p => Just (mkState p (env st) (nodes st) (edges st) (counter st))
    pathComp p (refl b) => Just (mkState p (env st) (nodes st) (edges st) (counter st))
    pathComp p (pathInv p') => Just (mkState (refl p) (env st) (nodes st) (edges st) (counter st))
    pathComp p q =>
      case step (mkState p (env st) (nodes st) (edges st) (counter st)) of
        Just sp => Just (mkState (pathComp (term sp) q) (env sp) (nodes sp) (edges sp) (counter sp))
        Nothing =>
          case step (mkState q (env st) (nodes st) (edges st) (counter st)) of
            Just sq => Just (mkState (pathComp p (term sq)) (env sq) (nodes sq) (edges sq) (counter sq))
            Nothing => Nothing

    pathInv p =>
      case step (mkState p (env st) (nodes st) (edges st) (counter st)) of
        Just sp => Just (mkState (pathInv (term sp)) (env sp) (nodes sp) (edges sp) (counter sp))
        Nothing => Nothing

    coe A i0 i1 => Just (mkState i0 (env st) (nodes st) (edges st) (counter st))
    hcomp A φ u v => Just (mkState v (env st) (nodes st) (edges st) (counter st))

    _ => Nothing

-----------------------------------------------------
-- 4. Evaluate with step-by-step net snapshots
-----------------------------------------------------

evalTrace : State → List State
evalTrace st = case step st of
                 Just st' => st :: evalTrace st'
                 Nothing  => [st]

evalTerm : Term → List State
evalTerm t = evalTrace (mkState t [] [] [] 0)

-----------------------------------------------------
-- 5. Net visualization
-----------------------------------------------------

showNode : Node → String
showNode n = "#" ++ show n.id ++ ":" ++ n.kind ++ "{" ++ show n.term ++ "}"

showEdge : Edge → String
showEdge e = show e.from ++ " → " ++ show e.to

showNet : State → String
showNet st =
  "Nodes:\n" ++ String.concatMap (\n => showNode n ++ "\n") (nodes st) ++
  "Edges:\n" ++ String.concatMap (\e => showEdge e ++ "\n") (edges st)

showTrace : List State → String
showTrace = String.concatMap (\st => "--- Step ---\n" ++ showNet st ++ "\n")

-----------------------------------------------------
-- 6. Example traces
-----------------------------------------------------

example1 = evalTerm (J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a")))
example2 = evalTerm (pathComp (refl (var "a")) (var "p"))
example3 = evalTerm (coe circle base loop)

-- Print the traces (nodes/edges) for inspection
trace1 = showTrace example1
trace2 = showTrace example2
trace3 = showTrace example3

-----------------------------------------------------
-- End of CubicalVMHITViz.redtt
-----------------------------------------------------
