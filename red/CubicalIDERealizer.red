-- CubicalIDERealizer.redtt
-- RedTT realizer for CubicalIDE Lego VM

module CubicalIDERealizer

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

-- composition & inversion
_·_ : Term -> Term -> Term
p · q = Comp p q

_⁻¹ : Term -> Term
p⁻¹ = Inv p

-----------------------------------------------------
-- Microcode / Interaction Net Execution
-----------------------------------------------------
-- Represent nodes as NetCells
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

-- Execute microcode step (Lam-App annihilation)
interact : NodeType -> NodeType -> NetCell
interact (LamNode l) (AppNode a) =
  mkCell [LamNode l, AppNode a] [mkEdge (LamNode l) (AppNode a)]

-- Duplication commuting, erasure, etc., could be added analogously

-----------------------------------------------------
-- Transport / Coercion Execution
-----------------------------------------------------
evalCoe : Term -> Term -> Term -> Term
evalCoe a i0 i1 = a  -- zero-cost coercion, realized as identity

-----------------------------------------------------
-- Normalization
-----------------------------------------------------
normalize : Term -> Term
normalize (App (Lam x t body) arg) =
  normalize (subst x arg body)
normalize (App f a) =
  App (normalize f) (normalize a)
normalize (Lam x t body) =
  Lam x (normalize t) (normalize body)
normalize (Refl t) = Refl (normalize t)
normalize (Comp p q) = Comp (normalize p) (normalize q)
normalize (Inv p) = Inv (normalize p)
normalize t = t

-----------------------------------------------------
-- IDE Operations
-----------------------------------------------------
open : Term -> Term
open t = t

typecheck : Term -> Type
typecheck t = infer t  -- stub: could call RedTT type inference

visualize : NetCell -> String
visualize n = show n  -- stub: could render graph

-----------------------------------------------------
-- Grammar Pushout Realization
-----------------------------------------------------
-- Each Lego piece is represented as a RedTT type
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
