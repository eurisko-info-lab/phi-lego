-- CubicalIDE.redtt
-- Full IDE for Cubical VM + INets + Paths + HITs

module CubicalIDE where

import Base
import Graph
import Graphics.SVG
import List
import String

-----------------------------------------------------
-- 1. Term & Grammar
-----------------------------------------------------
-- Lambda, Cubical, PathOps, HITs
piece Term
  term ::= var | lam | app | path | hit | coe
  var ::= "(" "var" name ")"
  lam ::= "(" "lam" name type term ")"
  app ::= "(" "app" term term ")"
  path ::= "refl" term | term "·" term | term "⁻¹"
  hit ::= "circle" | "S¹" | "base" | "loop" | "trunc" nat term
  coe ::= "coe" term term term

type ::= "Type" | name

-----------------------------------------------------
-- 2. INet / Optimal reduction
-----------------------------------------------------
-- Nodes and ports
record Node : Type where
  constructor mkNode
  id : ℕ
  term : Term

record Edge : Type where
  constructor mkEdge
  src : ℕ
  dst : ℕ

record State : Type where
  constructor mkState
  nodes : List Node
  edges : List Edge
  ports : List Pos
  step : ℕ

-- Interaction rules (microcoded)
rules:
  (interact (lam $l) (app $a)) ~> -- Lam-App annihilation
    connectBodyBinder $l $a

  (interact (app $a) (dup $d)) ~>
    commuteAppDup $a $d

  (interact (lam $l) (dup $d)) ~>
    commuteLamDup $l $d

  (interact (dup $d1) (dup $d2)) ~> annihilateDupDup $d1 $d2

  (interact (era $e) (node $type $n)) ~> eraseAllPorts $type $n

-----------------------------------------------------
-- 3. Cubical microcode
-----------------------------------------------------
rules:
  -- Path operations
  (@ (refl $a) $i) ~> $a
  (@ (sym $p) $i) ~> (@ $p (~ $i))
  (@ (funext $h) $i) ~> (λ x . (@ ($h x) $i))

  -- Transport / coe
  (transp $A i1 $a) ~> $a
  (transp (λᵢ $i . $A) $φ $a) ~> $a
  (coe $A $i0 $i1) ~> microcodeCoe $A $i0 $i1

  -- Path composition
  ($p · (refl $b)) ~> $p
  ((refl $a) · $p) ~> $p
  ($p · ($p ⁻¹)) ~> (refl $a)

-----------------------------------------------------
-- 4. Graph visualization
-----------------------------------------------------
record Pos : Type where
  constructor mkPos
  x : ℕ
  y : ℕ

layoutNodes : List Node → List (Node × Pos)
layoutNodes ns = List.indexedMap (\i n -> (n, mkPos (i*120) 100)) ns

layoutEdges : List Edge → List (Node × Pos) → List (Pos × Pos)
layoutEdges edges positions =
  List.map (\e ->
    let (Just (_, p1)) = List.find (\(n, _) => n.id == e.src) positions
    let (Just (_, p2)) = List.find (\(n, _) => n.id == e.dst) positions
    in (p1, p2)
  ) edges

highlightColor : Node → String
highlightColor n =
  match n.term with
  | J _ _ _ _ => "gold"
  | refl _    => "green"
  | pathComp _ _ => "blue"
  | pathInv _ => "red"
  | coe _ _ _ => "purple"
  | hcomp _ _ _ => "orange"
  | _         => "lightgray"

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
  in svg (4000, 1000)
         (List.map renderEdge edgeCoords ++ List.map renderNode nodePos)

-----------------------------------------------------
-- 5. Interactive debugger
-----------------------------------------------------
record GraphDebugger : Type where
  constructor mkGraphDebugger
  trace : List State
  current : ℕ

currentGraphState : GraphDebugger → State
currentGraphState dbg =
  case List.nth dbg.trace dbg.current of
    Just st => st
    Nothing => mkState [] [] [] 0

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

launchGraphDebugger : Term → IO ()
launchGraphDebugger t =
  let trace = evalTerm t -- full Cubical VM trace
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
-- 6. Example Terms
-----------------------------------------------------
exampleJ = J (var "A") (lam "x" (var "A") (var "C")) (refl (var "a"))
examplePath = pathComp (refl (var "a")) (var "p")
exampleCoe = coe circle base loop

debugJ = launchGraphDebugger exampleJ
debugPath = launchGraphDebugger examplePath
debugCoe = launchGraphDebugger exampleCoe

-----------------------------------------------------
-- End of Cubical IDE
-----------------------------------------------------
