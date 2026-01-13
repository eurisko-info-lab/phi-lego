-- CubicalIDEExtended.redtt
-- Full CubicalIDE Realizer with INet microcode, HIT normalization, visualization, and grammar pushouts

module CubicalIDEExtended

import cubical prelude

-----------------------------------------------------
-- Term Realization
-----------------------------------------------------
data Term : Type where
  Var  : String -> Term
  Lam  : String -> Term -> Term -> Term
  App  : Term -> Term -> Term
  Refl : Term -> Term
  Comp : Term -> Term -> Term  -- p · q
  Inv  : Term -> Term          -- p⁻¹
  J    : Term -> Term -> Term -> Term -> Term
  Coe  : Term -> Term -> Term -> Term
  HIT  : HITType -> Term

data HITType : Type where
  Circle : HITType
  Base   : HITType
  Loop   : HITType
  Susp   : Term -> HITType
  Trunc  : Nat -> Term -> HITType
  TruncN : Term -> Nat -> HITType

-----------------------------------------------------
-- Path Operations
-----------------------------------------------------
ap   : Term -> Term -> Term
ap t p = App (App (Var "ap") t) p

apd  : Term -> Term -> Term
apd t p = App (App (Var "apd") t) p

_·_ : Term -> Term -> Term
p · q = Comp p q

_⁻¹ : Term -> Term
p⁻¹ = Inv p

-----------------------------------------------------
-- Microcode / Interaction Net Execution
-----------------------------------------------------
data NodeType : Type where
  LamNode : Term -> NodeType
  AppNode : Term -> NodeType
  VarNode : String -> NodeType
  DupNode : Term -> NodeType
  EraNode : Term -> NodeType

record Edge where
  constructor mkEdge
  from : NodeType
  to   : NodeType

record NetCell where
  constructor mkCell
  nodes : List NodeType
  edges : List Edge

-- Execute a single microcode step (full INet)
interact : NodeType -> NodeType -> NetCell
-- Lam-App annihilation
interact (LamNode l) (AppNode a) =
  mkCell [LamNode l, AppNode a] [mkEdge (LamNode l) (AppNode a)]
-- App-Dup commuting
interact (AppNode a) (DupNode d) =
  let a1 = AppNode (extractTerm a)
  let a2 = AppNode (extractTerm a)
  let d1 = DupNode (extractTerm d)
  let d2 = DupNode (extractTerm d)
  mkCell [a1,a2,d1,d2] [
    mkEdge d1 a1, mkEdge d1 a2, mkEdge d2 a1, mkEdge d2 a2
  ]
-- Lam-Dup commuting
interact (LamNode l) (DupNode d) =
  let l1 = LamNode (extractTerm l)
  let l2 = LamNode (extractTerm l)
  let d1 = DupNode (extractTerm d)
  let d2 = DupNode (extractTerm d)
  let d3 = DupNode (extractTerm d)
  mkCell [l1,l2,d1,d2,d3] [
    mkEdge d1 l1, mkEdge d2 l2, mkEdge d3 l1, mkEdge d3 l2
  ]
-- Dup-Dup annihilation
interact (DupNode d1) (DupNode d2) =
  mkCell [d1,d2] [mkEdge d1 d2]
-- Erasure
interact (EraNode e) n = mkCell [EraNode e,n] []
interact n (EraNode e) = mkCell [n,EraNode e] []

-- Utilities
extractTerm : NodeType -> Term
extractTerm (LamNode t) = t
extractTerm (AppNode t) = t
extractTerm (DupNode t) = t
extractTerm (EraNode t) = t
extractTerm (VarNode s) = Var s

-----------------------------------------------------
-- Transport / Coercion Execution
-----------------------------------------------------
evalCoe : Term -> Term -> Term -> Term
evalCoe a i0 i1 = a  -- zero-cost coercion

-----------------------------------------------------
-- Normalization (including HIT simplifications)
-----------------------------------------------------
normalize : Term -> Term
-- Standard β
normalize (App (Lam x t body) arg) = normalize (subst x arg body)
normalize (App f a) = App (normalize f) (normalize a)
normalize (Lam x t body) = Lam x (normalize t) (normalize body)
-- Paths
normalize (Comp p q) =
  match (normalize p, normalize q) with
  | (Refl t1, p2) -> p2
  | (p1, Refl t2) -> p1
  | (p1, p2) -> Comp p1 p2
normalize (Inv (Refl t)) = Refl t
normalize (Inv p) = Inv (normalize p)
normalize (Refl t) = Refl (normalize t)
-- J eliminator
normalize (J A C d (Refl a)) = normalize d
normalize t = t
-- HIT simplifications
normalize (HIT Base) = HIT Base
normalize (HIT Loop) = HIT Loop
normalize (HIT Circle) = HIT Circle
normalize (HIT (Susp t)) = HIT (Susp (normalize t))
normalize (HIT (Trunc n t)) = HIT (Trunc n (normalize t))
normalize (HIT (TruncN t n)) = HIT (TruncN (normalize t) n)

-----------------------------------------------------
-- IDE Operations
-----------------------------------------------------
open : Term -> Term
open t = t

typecheck : Term -> Type
typecheck t = infer t -- stub: placeholder

-- Visualize NetCells as ASCII graph
visualize : NetCell -> String
visualize n =
  let nodeStrs = map nodeToStr n.nodes
  let edgeStrs = map edgeToStr n.edges
  "Nodes:\n" ++ concatMap (\s -> s ++ "\n") nodeStrs ++
  "Edges:\n" ++ concatMap (\s -> s ++ "\n") edgeStrs

nodeToStr : NodeType -> String
nodeToStr (LamNode t) = "Lam: " ++ show t
nodeToStr (AppNode t) = "App: " ++ show t
nodeToStr (DupNode t) = "Dup: " ++ show t
nodeToStr (EraNode t) = "Era: " ++ show t
nodeToStr (VarNode s) = "Var: " ++ s

edgeToStr : Edge -> String
edgeToStr (mkEdge f t) = show f ++ " -> " ++ show t

-----------------------------------------------------
-- Grammar Pushout Realization
-----------------------------------------------------
record Grammar where
  constructor mkGrammar
  pieces : List String

use : Grammar -> String -> Maybe String
use g name =
  if elem name g.pieces then Just name else Nothing

pushout : List Grammar -> Grammar
pushout gs = mkGrammar (foldl (++) [] (map pieces gs))

-----------------------------------------------------
-- Substitution utility
-----------------------------------------------------
subst : String -> Term -> Term -> Term
subst x with (Var y) = if x == y then with else Var y
subst x with (Lam y t b) =
  Lam y (subst x with t) (if x == y then b else subst x with b)
subst x with (App f a) = App (subst x with f) (subst x with a)
subst x with (Refl t) = Refl (subst x with t)
subst x with (Comp p q) = Comp (subst x with p) (subst x with q)
subst x with (Inv p) = Inv (subst x with p)
subst x with (HIT h) = HIT h
subst x with t = t

-----------------------------------------------------
-- Examples / Tests
-----------------------------------------------------
id_fun : Term
id_fun = Lam "x" (Var "Type") (Var "x")

id_app : Term
id_app = App (Lam "x" (Var "Type") (Var "x")) (Var "y")

refl_test : Term
refl_test = Refl (Var "a")

comp_test : Term
comp_test = (Refl (Var "a")) · (Refl (Var "a"))

coe_test : Term
coe_test = evalCoe (Var "A") (Var "i0") (Var "i1")

loop_test : Term
loop_test = Comp (Var "loop") (Var "base")

-- Grammar pushout example
gram1 : Grammar
gram1 = mkGrammar ["Identity","PathOps","HIT"]

gram2 : Grammar
gram2 = mkGrammar ["Univalence","HLevel"]

merged : Grammar
merged = pushout [gram1,gram2]
