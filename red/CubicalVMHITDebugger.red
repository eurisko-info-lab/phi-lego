-- CubicalVMDebugger.redtt
-- Interactive Cubical VM debugger with live net trace

module CubicalVMDebugger where

import CubicalVMHITViz

-----------------------------------------------------
-- 1. Interactive stepper
-----------------------------------------------------

record Debugger : Type where
  constructor mkDebugger
  trace    : List State
  current  : ℕ  -- index in trace

currentState : Debugger → State
currentState dbg = case List.nth dbg.trace dbg.current of
                     Just st => st
                     Nothing => case dbg.trace of
                                  [] => mkState Unit [] [] [] 0
                                  (st::_) => st

nextStep : Debugger → Debugger
nextStep dbg =
  if dbg.current + 1 < List.length dbg.trace then
    mkDebugger dbg.trace (dbg.current + 1)
  else dbg

prevStep : Debugger → Debugger
prevStep dbg =
  if dbg.current > 0 then
    mkDebugger dbg.trace (dbg.current - 1)
  else dbg

-----------------------------------------------------
-- 2. Node highlighting for HITs / Paths / Coe
-----------------------------------------------------

highlightNode : Node → String
highlightNode n =
  match n.term with
  | J _ _ _ _ => "⭐ " ++ showNode n
  | refl _    => "✅ " ++ showNode n
  | pathComp _ _ => "➡ " ++ showNode n
  | pathInv _    => "↩ " ++ showNode n
  | coe _ _ _    => "🔄 " ++ showNode n
  | hcomp _ _ _  => "🌐 " ++ showNode n
  | _ => showNode n

showHighlightedNet : State → String
showHighlightedNet st =
  "Nodes:\n" ++ String.concatMap (\n => highlightNode n ++ "\n") (nodes st) ++
  "Edges:\n" ++ String.concatMap (\e => showEdge e ++ "\n") (edges st)

-----------------------------------------------------
-- 3. Interactive REPL simulation
-----------------------------------------------------

interactiveLoop : Debugger → IO ()
interactiveLoop dbg = do
  IO.println ("=== Step " ++ show dbg.current ++ " ===")
  IO.println (showHighlightedNet (currentState dbg))
  IO.println "[n]ext, [p]rev, [q]uit?"
  cmd <- IO.getLine
  match cmd with
  | "n" => interactiveLoop (nextStep dbg)
  | "p" => interactiveLoop (prevStep dbg)
  | "q" => IO.println "Debugger exited."
  | _   => interactiveLoop dbg

-----------------------------------------------------
-- 4. Launch debugger on term
-----------------------------------------------------

launchDebugger : Term → IO ()
launchDebugger t =
  let trace = evalTerm t
  in interactiveLoop (mkDebugger trace 0)

-----------------------------------------------------
-- 5. Examples
-----------------------------------------------------

exampleJ = J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a"))
examplePath = pathComp (refl (var "a")) (var "p")
exampleCoe = coe circle base loop

-- Launch interactive debugger
debugJ = launchDebugger exampleJ
debugPath = launchDebugger examplePath
debugCoe = launchDebugger exampleCoe)

-----------------------------------------------------
-- End of CubicalVMDebugger.redtt
-----------------------------------------------------
