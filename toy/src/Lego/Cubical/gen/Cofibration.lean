/-
  Lego.Cubical.Cofibration: Generated from Cofibration.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Cofibration.lego
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Cofibration

open Lego.Core
open Lego.Core.Expr
/-- isDim0 -/
def isDim0 : Expr → Expr
  | .dim0 => true
  | .dim1 => false
  | .dimVar $n => false
  | e => e
/-- isDim1 -/
def isDim1 : Expr → Expr
  | .dim0 => false
  | .dim1 => true
  | .dimVar $n => false
  | e => e
/-- dimEq -/
def dimEq : Expr → Expr
  | .dim0, .dim0 => true
  | .dim1, .dim1 => true
  | .dimVar $n, .dimVar $m => (eq $n $m)
  | e => e
/-- top -/
def top : Expr → Expr
  |  => cof_top
  | e => e
/-- bot -/
def bot : Expr → Expr
  |  => cof_bot
  | e => e
/-- cofEq -/
def cofEq : Expr → Expr
  | $r, $r => cof_top
  | .dim0, .dim1 => cof_bot
  | .dim1, .dim0 => cof_bot
  | e => e
/-- cofLe -/
def cofLe : Expr → Expr
  | $r, $s => (cof_or (cof_eq $r dim0) (cof_eq $s dim1))
  | e => e
/-- boundary -/
def boundary : Expr → Expr
  | $r => (cof_or (cof_eq $r dim0) (cof_eq $r dim1))
  | e => e
/-- cof_and -/
def cof_and : Expr → Expr
  | .cof_top, $φ => $φ
  | $φ, .cof_top => $φ
  | .cof_bot, $φ => cof_bot
  | $φ, .cof_bot => cof_bot
  | $φ, $φ => $φ
  | e => e
/-- cof_or -/
def cof_or : Expr → Expr
  | .cof_bot, $φ => $φ
  | $φ, .cof_bot => $φ
  | .cof_top, $φ => cof_top
  | $φ, .cof_top => cof_top
  | $φ, $φ => $φ
  | e => e
/-- normCof -/
def normCof : Expr → Expr
  | .cof_top => cof_top
  | .cof_bot => cof_bot
  | .cof_eq $r $s => (cofEq $r $s)
  | .cof_and $φ $ψ => (cof_and (normCof $φ) (normCof $ψ))
  | .cof_or $φ $ψ => (cof_or (normCof $φ) (normCof $ψ))
  | e => e
/-- cofTrue -/
def cofTrue : Expr → Expr
  | .cof_top => true
  | .cof_bot => false
  | .cof_eq $r $s => (dimEq $r $s)
  | .cof_and $φ $ψ => (and (cofTrue $φ) (cofTrue $ψ))
  | .cof_or $φ $ψ => (or (cofTrue $φ) (cofTrue $ψ))
  | e => e
/-- cofFalse -/
def cofFalse : Expr → Expr
  | $φ => (not (cofTrue $φ))
  | e => e
/-- entails -/
def entails : Expr → Expr
  | $φ, $ψ => (cofTrue (cof_or (cof_not $φ) $ψ))
  | e => e
/-- cof_not -/
def cof_not : Expr → Expr
  | .cof_top => cof_bot
  | .cof_bot => cof_top
  | e => e
/-- substCof -/
def substCof : Expr → Expr
  | $n, $r, .cof_top => cof_top
  | $n, $r, .cof_bot => cof_bot
  | $n, $r, .cof_eq $s $t => (cof_eq (substDimInDim $n $r $s) (substDimInDim $n $r $t))
  | $n, $r, .cof_and $φ $ψ => (cof_and (substCof $n $r $φ) (substCof $n $r $ψ))
  | $n, $r, .cof_or $φ $ψ => (cof_or (substCof $n $r $φ) (substCof $n $r $ψ))
  | e => e
/-- substDimInDim -/
def substDimInDim : Expr → Expr
  | $n, $r, .dimVar $n => $r
  | $n, $r, .dim0 => dim0
  | $n, $r, .dim1 => dim1
  | e => e
/-- forallDim -/
def forallDim : Expr → Expr
  | $i, $φ => (cof_and (substCof $i dim0 $φ) (substCof $i dim1 $φ))
  | e => e
/-- existsDim -/
def existsDim : Expr → Expr
  | $i, $φ => (cof_or (substCof $i dim0 $φ) (substCof $i dim1 $φ))
  | e => e
end Lego.Cubical.Cofibration
