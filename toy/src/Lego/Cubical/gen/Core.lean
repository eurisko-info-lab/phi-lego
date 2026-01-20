/-
  Lego.Cubical.Core: Generated from Core.lego

  DO NOT EDIT - regenerate with:
    lake exe generated-pipeline Core.lego
-/

import Lego.Cubical.Core

namespace Lego.Cubical.Core

open Lego.Core
open Lego.Core.Expr
/-- lmax -/
def lmax : Expr → Expr
  | $l, $l => $l
  | .lzero, $l => $l
  | $l, .lzero => $l
  | .lsuc $l1, .lsuc $l2 => (lsuc (lmax $l1 $l2))
  | e => e
/-- app -/
def app : Expr → Expr
  | .lam $body, $arg => (subst (num (number 0)) $arg $body)
  | e => e
/-- fst -/
def fst : Expr → Expr
  | .pair $a $b => $a
  | e => e
/-- snd -/
def snd : Expr → Expr
  | .pair $a $b => $b
  | e => e
/-- letE -/
def letE : Expr → Expr
  | $ty, $val, $body => (subst (num (number 0)) $val $body)
  | e => e
/-- cof_eq -/
def cof_eq : Expr → Expr
  | $r, $r => cof_top
  | .dim0, .dim1 => cof_bot
  | .dim1, .dim0 => cof_bot
  | e => e
/-- cof_and -/
def cof_and : Expr → Expr
  | .cof_top, $φ => $φ
  | .cof_bot, $φ => cof_bot
  | e => e
/-- cof_or -/
def cof_or : Expr → Expr
  | .cof_top, $φ => cof_top
  | .cof_bot, $φ => $φ
  | e => e
/-- papp -/
def papp : Expr → Expr
  | .plam $body, .dim0 => (substDim (num (number 0)) dim0 $body)
  | .plam $body, .dim1 => (substDim (num (number 0)) dim1 $body)
  | .refl $a, $r => $a
  | e => e
/-- coe -/
def coe : Expr → Expr
  | $r, $r, $A, $a => $a
  | e => e
/-- hcom -/
def hcom : Expr → Expr
  | $r, $r, $A, $φ, $cap => $cap
  | e => e
/-- vin -/
def vin : Expr → Expr
  | .dim0, $a, $b => $a
  | .dim1, $a, $b => $b
  | e => e
/-- natElim -/
def natElim : Expr → Expr
  | $P, $z, $s, .zero => $z
  | $P, $z, $s, .suc $n => (app (app $s $n) (natElim $P $z $s $n))
  | e => e
/-- loop -/
def loop : Expr → Expr
  | .dim0 => base
  | .dim1 => base
  | e => e
/-- circleElim -/
def circleElim : Expr → Expr
  | $P, $b, $l, .base => $b
  | e => e
/-- subOut -/
def subOut : Expr → Expr
  | .subIn $e => $e
  | e => e
/-- shift -/
def shift : Expr → Expr
  | $k, $n, .ix $m => (ix (if (geq $m $k) (add $m $n) $m))
  | $k, $n, .lam $body => (lam (shift (add $k (num (number 1))) $n $body))
  | $k, $n, .app $f $a => (app (shift $k $n $f) (shift $k $n $a))
  | $k, $n, .pi $A $B => (pi (shift $k $n $A) (shift (add $k (num (number 1))) $n $B))
  | e => e
/-- subst -/
def subst : Expr → Expr
  | $k, $v, .ix $k => $v
  | $k, $v, .lam $body => (lam (subst (add $k (num (number 1))) (shift (num (number 0)) (num (number 1)) $v) $body))
  | $k, $v, .app $f $a => (app (subst $k $v $f) (subst $k $v $a))
  | e => e
/-- normalize -/
def normalize : Expr → Expr
  | .num .number 0, $t => $t
  | e => e
/-- normalizeStep -/
def normalizeStep : Expr → Expr
  | $fuel, .some $t => (normalize $fuel $t)
  | $fuel, .none => $t
  | e => e
end Lego.Cubical.Core
