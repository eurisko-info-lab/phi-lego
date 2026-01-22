-- CubicalVMGraph.redtt
-- Real-time Cubical VM graph visualization

module CubicalVMGraph where

import CubicalVMHITViz
import Graphics.SVG
import List
import String

-----------------------------------------------------
-- 1. Graph layout and rendering
-----------------------------------------------------

-- A 2D position
record Pos : Type where
  constructor mkPos
  x : ℕ
  y : ℕ

-- Compute layout for nodes
layoutNodes : List Node → List (Node × Pos)
layoutNodes ns =
  let positions = List.indexedMap (\i n -> (n, mkPos (i*120) 100)) ns
  in positions

-- Map edges to coordinates
layoutEdges : List Edge → List (Pos × Pos) → List (Pos × Pos)
layoutEdges edges positions =
  List.map (\e ->
    let (n1Pos, n2Pos) =
      (List.find (\(n, _) => n.id == e.src) positions,
       List.find (\(n, _) => n.id == e.dst) positions)
    in case (n1Pos, n2Pos) of
         (Just (_, p1), Just (_, p2)) => (p1, p2)
         _ => (mkPos 0 0, mkPos 0 0)
  ) edges

-----------------------------------------------------
-- 2. Node highlighting
-----------------------------------------------------

highlightColor : Node → String
highlightColor n =
  match n.term with
  | J _ _ _ _      => "gold"
  | refl _         => "green"
  | pathComp _ _   => "blue"
  | pathInv _      => "red"
  | coe _ _ _      => "purple"
  | hcomp _ _ _    => "orange"
  | _              => "lightgray"

-----------------------------------------------------
-- 3. Render SVG
-----------------------------------------------------

renderNode : (Node × Pos) → SVG
renderNode (n, p) =
  circle (toFloat p.x) (toFloat p.y) 40
         [ fill := highlightColor n, stroke := "black", stroke_width := "2" ] ++
  text (toFloat (p.x-15)) (toFloat (p.y+5)) (showNode n)
       [ font_size := "16px", fill := "black" ]

renderEdge : (Pos × Pos) → SVG
renderEdge (p1, p2) =
  line (toFloat p1.x) (toFloat p1.y)
       (toFloat p2.x) (toFloat p2.y)
       [ stroke := "black", stroke_width := "2" ]

renderGraph : State → SVG
renderGraph st =
  let nodePos = layoutNodes (nodes st)
      edgeCoords = layoutEdges (edges st) nodePos
      nodeSVG = List.map renderNode nodePos
      edgeSVG = List.map renderEdge edgeCoords
  in svg (4000, 1000) (edgeSVG ++ nodeSVG)

-----------------------------------------------------
-- 4. Interactive stepper
-----------------------------------------------------

record GraphDebugger : Type where
  constructor mkGraphDebugger
  trace : List State
  current : ℕ

currentGraphState : GraphDebugger → State
currentGraphState dbg =
  case List.nth dbg.trace dbg.current of
    Just st => st
    Nothing => mkState Unit [] [] [] 0

nextGraphStep : GraphDebugger → GraphDebugger
nextGraphStep dbg =
  if dbg.current + 1 < List.length dbg.trace then
    mkGraphDebugger dbg.trace (dbg.current + 1)
  else dbg

prevGraphStep : GraphDebugger → GraphDebugger
prevGraphStep dbg =
  if dbg.current > 0 then
    mkGraphDebugger dbg.trace (dbg.current - 1)
  else dbg

-----------------------------------------------------
-- 5. Launch visualization
-----------------------------------------------------

launchGraphDebugger : Term → IO ()
launchGraphDebugger t =
  let trace = evalTerm t
      dbg = mkGraphDebugger trace 0
  in visualizeLoop dbg

visualizeLoop : GraphDebugger → IO ()
visualizeLoop dbg = do
  let st = currentGraphState dbg
  let svgGraph = renderGraph st
  IO.displaySVG svgGraph
  IO.println "[n]ext, [p]rev, [q]uit?"
  cmd <- IO.getLine
  match cmd with
    | "n" => visualizeLoop (nextGraphStep dbg)
    | "p" => visualizeLoop (prevGraphStep dbg)
    | "q" => IO.println "Exited."
    | _   => visualizeLoop dbg

-----------------------------------------------------
-- 6. Examples
-----------------------------------------------------

exampleJ = J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a"))
examplePath = pathComp (refl (var "a")) (var "p")
exampleCoe = coe circle base loop

debugJ = launchGraphDebugger exampleJ
debugPath = launchGraphDebugger examplePath
debugCoe = launchGraphDebugger exampleCoe

-----------------------------------------------------
-- End of CubicalVMGraph.redtt
-----------------------------------------------------
