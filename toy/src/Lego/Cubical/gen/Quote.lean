/-
  Lego.Cubical.Quote: Generated from Quote.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Quote.lego
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Quote

open Lego.Core
open Lego.Core.Expr
/-- qenvEmpty -/
def qenvEmpty : Expr → Expr
  |  => (qenv (num (number 0)) (num (number 0)))
  | e => e
/-- qenvSucc -/
def qenvSucc : Expr → Expr
  | .qenv $l $dl => (qenv (suc $l) $dl)
  | e => e
/-- qenvSuccDim -/
def qenvSuccDim : Expr → Expr
  | .qenv $l $dl => (qenv $l (suc $dl))
  | e => e
/-- levelToIndex -/
def levelToIndex : Expr → Expr
  | .qenv $l $dl, $lvl => (sub (sub $l $lvl) (num (number 1)))
  | e => e
/-- dimLevelToIndex -/
def dimLevelToIndex : Expr → Expr
  | .qenv $l $dl, $lvl => (sub (sub $dl $lvl) (num (number 1)))
  | e => e
/-- generic -/
def generic : Expr → Expr
  | .qenv $l $dl => (ix $l)
  | e => e
/-- genericDim -/
def genericDim : Expr → Expr
  | .qenv $l $dl => (dimVar $dl)
  | e => e
/-- shiftFrom -/
def shiftFrom : Expr → Expr
  | .ix $k, $n, $cutoff => (if (geq $k $cutoff) (ix (add $k $n)) (ix $k))
  | .lam $body, $n, $cutoff => (lam (shiftFrom $body $n (suc $cutoff)))
  | .app $f $a, $n, $cutoff => (app (shiftFrom $f $n $cutoff) (shiftFrom $a $n $cutoff))
  | .pi $A $B, $n, $cutoff => (pi (shiftFrom $A $n $cutoff) (shiftFrom $B $n (suc $cutoff)))
  | .sigma $A $B, $n, $cutoff => (sigma (shiftFrom $A $n $cutoff) (shiftFrom $B $n (suc $cutoff)))
  | .pair $a $b, $n, $cutoff => (pair (shiftFrom $a $n $cutoff) (shiftFrom $b $n $cutoff))
  | .fst $p, $n, $cutoff => (fst (shiftFrom $p $n $cutoff))
  | .snd $p, $n, $cutoff => (snd (shiftFrom $p $n $cutoff))
  | .plam $body, $n, $cutoff => (plam (shiftFrom $body $n $cutoff))
  | .papp $p $r, $n, $cutoff => (papp (shiftFrom $p $n $cutoff) $r)
  | .lit $s, $n, $cutoff => (lit $s)
  | .univ $l, $n, $cutoff => (univ $l)
  | e => e
/-- quoteCon -/
def quoteCon : Expr → Expr
  | $env, .dlit $s => (lit $s)
  | $env, .dlam .dclo $body $cloEnv => (lam (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) dtpUnknown)) $cloEnv) $body)))
  | $env, .dpair $a $b => (pair (quoteCon $env $a) (quoteCon $env $b))
  | $env, .duniv $l => (univ (quoteLevel $l))
  | $env, .dpi $A .dclo $B $cloEnv => (pi (quoteTp $env $A) (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) $A)) $cloEnv) $B)))
  | $env, .dsigma $A .dclo $B $cloEnv => (sigma (quoteTp $env $A) (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) $A)) $cloEnv) $B)))
  | $env, .dpath $A $a $b => (path (quoteTp $env $A) (quoteCon $env $a) (quoteCon $env $b))
  | $env, .dplam .dclo $body $cloEnv => (plam (quoteCon (qenvSuccDim $env) (deval (denvCons (dneu (dcut (dneuVar (qenvDimLevel $env)) dtpI)) $cloEnv) $body)))
  | $env, .drefl $a => (refl (quoteCon $env $a))
  | $env, .dnat => nat
  | $env, .dzeroN => zero
  | $env, .dsucN $n => (suc (quoteCon $env $n))
  | $env, .dcircle => circle
  | $env, .dbase => base
  | $env, .dloop $d => (loop (quoteDim $d))
  | $env, .dneu $cut => (quoteNeutral $env $cut)
  | e => e
/-- quoteTp -/
def quoteTp : Expr → Expr
  | $env, .dtpUniv $l => (univ (quoteLevel $l))
  | $env, .dtpPi $A $clo => (pi (quoteTp $env $A) (quoteTpClo (qenvSucc $env) $clo))
  | $env, .dtpSigma $A $clo => (sigma (quoteTp $env $A) (quoteTpClo (qenvSucc $env) $clo))
  | $env, .dtpPath $A $a $b => (path (quoteTp $env $A) (quoteCon $env $a) (quoteCon $env $b))
  | $env, .dtpNat => nat
  | $env, .dtpCircle => circle
  | $env, .dtpNeu $cut => (quoteNeutral $env $cut)
  | e => e
/-- quoteNeutral -/
def quoteNeutral : Expr → Expr
  | $env, .dcut .dneuVar $l $tp => (ix (levelToIndex $env $l))
  | $env, .dcut .dneuApp $neu $arg $tp => (app (quoteNeutral $env (dcut $neu dtpUnknown)) (quoteCon $env $arg))
  | $env, .dcut .dneuFst $neu $tp => (fst (quoteNeutral $env (dcut $neu dtpUnknown)))
  | $env, .dcut .dneuSnd $neu $tp => (snd (quoteNeutral $env (dcut $neu dtpUnknown)))
  | $env, .dcut .dneuPApp $neu $d $tp => (papp (quoteNeutral $env (dcut $neu dtpUnknown)) (quoteDim $d))
  | $env, .dcut .dneuNatElim $P $z $s $neu $tp => (natElim (quoteCon $env $P) (quoteCon $env $z) (quoteCon $env $s) (quoteNeutral $env (dcut $neu dtpNat)))
  | $env, .dcut .dneuCircleElim $P $b $l $neu $tp => (circleElim (quoteCon $env $P) (quoteCon $env $b) (quoteCon $env $l) (quoteNeutral $env (dcut $neu dtpCircle)))
  | e => e
/-- quoteLevel -/
def quoteLevel : Expr → Expr
  | .dconst $n => (ofNat $n)
  | .dlvar $n => (lvar $n)
  | .dmax $l1 $l2 => (lmax (quoteLevel $l1) (quoteLevel $l2))
  | .dsuc $l => (lsuc (quoteLevel $l))
  | e => e
/-- ofNat -/
def ofNat : Expr → Expr
  | .num .number 0 => lzero
  | .suc $n => (lsuc (ofNat $n))
  | e => e
/-- quoteDim -/
def quoteDim : Expr → Expr
  | .ddim0 => dim0
  | .ddim1 => dim1
  | .dvar $n => (dimVar $n)
  | e => e
/-- nbe -/
def nbe : Expr → Expr
  | $t => (quoteCon qenvEmpty (deval denvNil $t))
  | e => e
/-- nbeWithEnv -/
def nbeWithEnv : Expr → Expr
  | $env, $t => (quoteCon qenvEmpty (deval $env $t))
  | e => e
end Lego.Cubical.Quote
