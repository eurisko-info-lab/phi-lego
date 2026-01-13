-- CubicalIDE_LegoIntegration.redtt
-- Extends CubicalIDEExtended with Lego compilation, INet conversion, and visualization

module CubicalIDE_LegoIntegration

import CubicalIDEExtended

-----------------------------------------------------
-- Lego AST (subset for HoTT/Cubical)
-----------------------------------------------------
data LegoTerm : Type where
  LVar   : String -> LegoTerm
  LLam   : String -> LegoTerm -> LegoTerm -> LegoTerm
  LApp   : LegoTerm -> LegoTerm -> LegoTerm
  LRefl  : LegoTerm -> LegoTerm
  LComp  : LegoTerm -> LegoTerm -> LegoTerm
  LInv   : LegoTerm -> LegoTerm
  LJ     : LegoTerm -> LegoTerm -> LegoTerm -> LegoTerm -> LegoTerm
  LCoe   : LegoTerm -> LegoTerm -> LegoTerm -> LegoTerm
  LHIT   : HITType -> LegoTerm

-- Example Lego source pieces
id_lego : LegoTerm
id_lego = LLam "x" (LVar "Type") (LVar "x")

app_id_lego : LegoTerm
app_id_lego = LApp id_lego (LVar "y")

refl_lego : LegoTerm
refl_lego = LRefl (LVar "a")

loop_lego : LegoTerm
loop_lego = LComp (LVar "loop") (LVar "base")

-----------------------------------------------------
-- Compiler: LegoTerm -> Term
-----------------------------------------------------
compileTerm : LegoTerm -> Term
compileTerm (LVar x)       = Var x
compileTerm (LLam x t b)   = Lam x (compileTerm t) (compileTerm b)
compileTerm (LApp f a)     = App (compileTerm f) (compileTerm a)
compileTerm (LRefl t)      = Refl (compileTerm t)
compileTerm (LComp p q)    = Comp (compileTerm p) (compileTerm q)
compileTerm (LInv p)       = Inv (compileTerm p)
compileTerm (LJ a c d r)   = J (compileTerm a) (compileTerm c) (compileTerm d) (compileTerm r)
compileTerm (LCoe a i0 i1) = Coe (compileTerm a) (compileTerm i0) (compileTerm i1)
compileTerm (LHIT h)       = HIT h

-----------------------------------------------------
-- NetCell conversion (INet)
-----------------------------------------------------
toINetCell : Term -> NetCell
toINetCell (Var x) = mkCell [VarNode x] []
toINetCell (Lam x t b) =
  let tNet = toINetCell t
  let bNet = toINetCell b
  let lamNode = LamNode (Lam x t b)
  mkCell [lamNode] [mkEdge lamNode (head bNet.nodes)]
toINetCell (App f a) =
  let fNet = toINetCell f
  let aNet = toINetCell a
  let appNode = AppNode (App f a)
  mkCell [appNode] [mkEdge appNode (head fNet.nodes), mkEdge appNode (head aNet.nodes)]
toINetCell (Refl t) =
  let tNet = toINetCell t
  mkCell [Refl (normalize t)] [mkEdge (Refl (normalize t)) (head tNet.nodes)]
toINetCell (Comp p q) =
  let pNet = toINetCell p
  let qNet = toINetCell q
  mkCell [Comp (normalize p) (normalize q)] [mkEdge (Comp p q) (head pNet.nodes), mkEdge (Comp p q) (head qNet.nodes)]
toINetCell (Inv p) =
  let pNet = toINetCell p
  mkCell [Inv (normalize p)] [mkEdge (Inv p) (head pNet.nodes)]
toINetCell (J a c d r) =
  let rNet = toINetCell r
  mkCell [J (normalize a) (normalize c) (normalize d) (normalize r)] [mkEdge (J a c d r) (head rNet.nodes)]
toINetCell (Coe a i0 i1) =
  let aNet = toINetCell a
  mkCell [Coe a i0 i1] [mkEdge (Coe a i0 i1) (head aNet.nodes)]
toINetCell (HIT h) = mkCell [HIT h] []

-----------------------------------------------------
-- IDE integration
-----------------------------------------------------
-- Compile LegoTerm, normalize, convert to NetCell, visualize
compileAndVisualize : LegoTerm -> String
compileAndVisualize t =
  let term = normalize (compileTerm t)
  let net  = toINetCell term
  visualize net

-- Example usage
id_net : String
id_net = compileAndVisualize id_lego

app_id_net : String
app_id_net = compileAndVisualize app_id_lego

refl_net : String
refl_net = compileAndVisualize refl_lego

loop_net : String
loop_net = compileAndVisualize loop_lego

-----------------------------------------------------
-- Grammar Pushout Integration
-----------------------------------------------------
-- Dynamically merge Lego grammar pieces
mergedGrammar : Grammar
mergedGrammar = pushout [gram1, gram2]

useMergedPiece : String -> Maybe String
useMergedPiece name = use mergedGrammar name
