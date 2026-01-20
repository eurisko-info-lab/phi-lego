/-
  Lego.Cubical.Domain: Generated from Domain.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Domain.lego
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Domain

open Lego.Core
open Lego.Core.Expr
/-- dzero -/
def dzero : Expr → Expr
  |  => (dconst (num (number 0)))
  | e => e
/-- done -/
def done : Expr → Expr
  |  => (dconst (num (number 1)))
  | e => e
/-- ofLevel -/
def ofLevel : Expr → Expr
  | .lzero => dzero
  | .lsuc $l => (dsuc (ofLevel $l))
  | .lmax $l1 $l2 => (dmax (ofLevel $l1) (ofLevel $l2))
  | .lvar $n => (dlvar $n)
  | e => e
/-- dimOfExpr -/
def dimOfExpr : Expr → Expr
  | .dim0 => (some ddim0)
  | .dim1 => (some ddim1)
  | .dimVar $n => (some (dvar $n))
  | $e => none
  | e => e
/-- dimToExpr -/
def dimToExpr : Expr → Expr
  | .ddim0 => dim0
  | .ddim1 => dim1
  | .dvar $n => (dimVar $n)
  | e => e
/-- dimEqD -/
def dimEqD : Expr → Expr
  | .ddim0, .ddim0 => true
  | .ddim1, .ddim1 => true
  | .dvar $n, .dvar $m => (eq $n $m)
  | e => e
/-- dCofIsTrue -/
def dCofIsTrue : Expr → Expr
  | .dcof_top => true
  | .dcof_bot => false
  | .dcof_eq $d1 $d2 => (dimEqD $d1 $d2)
  | .dcof_join $φ $ψ => (or (dCofIsTrue $φ) (dCofIsTrue $ψ))
  | .dcof_meet $φ $ψ => (and (dCofIsTrue $φ) (dCofIsTrue $ψ))
  | e => e
/-- dCofIsFalse -/
def dCofIsFalse : Expr → Expr
  | $φ => (not (dCofIsTrue $φ))
  | e => e
/-- denvLookup -/
def denvLookup : Expr → Expr
  | .num .number 0, .denvCons $v $rest => (some $v)
  | .suc $n, .denvCons $v $rest => (denvLookup $n $rest)
  | $n, .denvNil => none
  | e => e
/-- denvExtend -/
def denvExtend : Expr → Expr
  | $v, $env => (denvCons $v $env)
  | e => e
/-- dCloApply -/
def dCloApply : Expr → Expr
  | .dclo $body $env, $arg => (deval (denvCons $arg $env) $body)
  | e => e
/-- deval -/
def deval : Expr → Expr
  | $env, .ix $n => (fromOption (denvLookup $n $env) (dneu (dcut (dneuVar $n) dtpUnknown)))
  | $env, .lit $s => (dlit $s)
  | $env, .lam $body => (dlam (dclo $body $env))
  | $env, .app $f $a => (dApply (deval $env $f) (deval $env $a))
  | $env, .pi $A $B => (dpi (dtpOf (deval $env $A)) (dclo $B $env))
  | $env, .sigma $A $B => (dsigma (dtpOf (deval $env $A)) (dclo $B $env))
  | $env, .pair $a $b => (dpair (deval $env $a) (deval $env $b))
  | $env, .fst $p => (dFst (deval $env $p))
  | $env, .snd $p => (dSnd (deval $env $p))
  | $env, .univ $l => (duniv (ofLevel $l))
  | $env, .path $A $a $b => (dpath (dtpOf (deval $env $A)) (deval $env $a) (deval $env $b))
  | $env, .plam $body => (dplam (dclo $body $env))
  | $env, .papp $p $r => (dPApp (deval $env $p) (dimOfExprForce $r))
  | $env, .refl $a => (drefl (deval $env $a))
  | $env, .nat => dnat
  | $env, .zero => dzeroN
  | $env, .suc $n => (dsucN (deval $env $n))
  | $env, .circle => dcircle
  | $env, .base => dbase
  | $env, .loop $r => (dloop (dimOfExprForce $r))
  | e => e
/-- dApply -/
def dApply : Expr → Expr
  | .dlam $clo, $arg => (dCloApply $clo $arg)
  | .dneu .dcut $neu $tp, $arg => (dneu (dcut (dneuApp $neu $arg) (dtpApply $tp $arg)))
  | e => e
/-- dFst -/
def dFst : Expr → Expr
  | .dpair $a $b => $a
  | .dneu .dcut $neu $tp => (dneu (dcut (dneuFst $neu) (dtpFst $tp)))
  | e => e
/-- dSnd -/
def dSnd : Expr → Expr
  | .dpair $a $b => $b
  | .dneu .dcut $neu $tp => (dneu (dcut (dneuSnd $neu) (dtpSnd $tp)))
  | e => e
/-- dPApp -/
def dPApp : Expr → Expr
  | .dplam $clo, $d => (dCloApplyDim $clo $d)
  | .drefl $a, $d => $a
  | .dneu .dcut $neu $tp, $d => (dneu (dcut (dneuPApp $neu $d) (dtpPApp $tp $d)))
  | e => e
end Lego.Cubical.Domain
