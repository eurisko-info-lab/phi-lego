(DImport import (modulePath Lego .

Algebra) ;)

namespace Core

  section Level

    def level : Parser :=
      ((annotated str "zero" → lzero) <|> ((annotated str "suc" level → lsuc) <|> ((annotated str "max" level level → lmax) <|> (annotated str "lvar" (special <number>) → lvar))))

    def maxIdempotent (t : Term) : Term :=
      match t with
      | (lmax $l $l) => $l
      | _ => t

    def maxZeroL (t : Term) : Term :=
      match t with
      | (lmax (lzero) $l) => $l
      | _ => t

    def maxZeroR (t : Term) : Term :=
      match t with
      | (lmax $l (lzero)) => $l
      | _ => t

    def maxSucSuc (t : Term) : Term :=
      match t with
      | (lmax (lsuc $l1) (lsuc $l2)) => (lsuc (lmax $l1 $l2))
      | _ => t

    -- Test: test
    -- (lmax (lsuc $(lzero)) (lsuc $(lzero)))

    -- Test: test
    -- (lmax $(lzero) (lsuc $(lzero)))

  end Level

  section Expr

    def term : Parser :=
      ((annotated str "ix" (special <number>) → ix) <|> ((annotated str "lit" (special <string>) → lit) <|> ((annotated str "lam" term → lam) <|> ((annotated str "app" term term → app) <|> ((annotated str "pi" term term → pi) <|> ((annotated str "sigma" term term → sigma) <|> ((annotated str "pair" term term → pair) <|> ((annotated str "fst" term → fst) <|> ((annotated str "snd" term → snd) <|> ((annotated str "letE" term term term → letE) <|> (annotated str "univ" level → univ)))))))))))

    def beta (t : Term) : Term :=
      match t with
      | (app (lam $body) $arg) => (subst (num (number 0)) $arg $body)
      | _ => t

    def fstPair (t : Term) : Term :=
      match t with
      | (fst (pair $a $b)) => $a
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | (snd (pair $a $b)) => $b
      | _ => t

    def letBeta (t : Term) : Term :=
      match t with
      | (letE $ty $val $body) => (subst (num (number 0)) $val $body)
      | _ => t

    -- Test: test
    -- (app (lam (ix (num (number 0)))) (lit str "x"))

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Expr

  section Dimension

    def term : Parser :=
      ((annotated str "dim0" → dim0) <|> ((annotated str "dim1" → dim1) <|> (annotated str "dimVar" (special <number>) → dimVar)))

  end Dimension

  section Cofibration

    def term : Parser :=
      ((annotated str "cof_top" → cof_top) <|> ((annotated str "cof_bot" → cof_bot) <|> ((annotated str "cof_eq" term term → cof_eq) <|> ((annotated str "cof_and" term term → cof_and) <|> (annotated str "cof_or" term term → cof_or)))))

    def eqRefl (t : Term) : Term :=
      match t with
      | (cof_eq $r $r) => (cof_top)
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | (cof_eq (dim0) (dim1)) => (cof_bot)
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | (cof_eq (dim1) (dim0)) => (cof_bot)
      | _ => t

    def andTop (t : Term) : Term :=
      match t with
      | (cof_and (cof_top) $φ) => $φ
      | _ => t

    def andBot (t : Term) : Term :=
      match t with
      | (cof_and (cof_bot) $φ) => (cof_bot)
      | _ => t

    def orTop (t : Term) : Term :=
      match t with
      | (cof_or (cof_top) $φ) => (cof_top)
      | _ => t

    def orBot (t : Term) : Term :=
      match t with
      | (cof_or (cof_bot) $φ) => $φ
      | _ => t

    -- Test: test
    -- (cof_eq $(dim0) $(dim0))

    -- Test: test
    -- (cof_eq $(dim0) $(dim1))

  end Cofibration

  section Path

    def term : Parser :=
      ((annotated str "path" term term term → path) <|> ((annotated str "plam" term → plam) <|> ((annotated str "papp" term term → papp) <|> (annotated str "refl" term → refl))))

    def plamApp0 (t : Term) : Term :=
      match t with
      | (papp (plam $body) (dim0)) => (substDim (num (number 0)) (dim0) $body)
      | _ => t

    def plamApp1 (t : Term) : Term :=
      match t with
      | (papp (plam $body) (dim1)) => (substDim (num (number 0)) (dim1) $body)
      | _ => t

    def reflApp (t : Term) : Term :=
      match t with
      | (papp (refl $a) $r) => $a
      | _ => t

    -- Test: test
    -- (papp (refl (lit str "a")) $(dim0))

  end Path

  section Kan

    def term : Parser :=
      ((annotated str "coe" term term term term → coe) <|> ((annotated str "hcom" term term term term term → hcom) <|> ((annotated str "hcomTube" term term term tubes term → hcomTube) <|> ((annotated str "com" term term term tubes term → com) <|> ((annotated str "ghcom" term term term tubes term → ghcom) <|> (annotated str "gcom" term term term tubes term → gcom))))))

    def tubes : Parser :=
      (annotated many (tube) → tubes)

    def tube : Parser :=
      (annotated str "(" term str "," term str ")" → tube)

    def coeRefl (t : Term) : Term :=
      match t with
      | (coe $r $r $A $a) => $a
      | _ => t

    def hcomRefl (t : Term) : Term :=
      match t with
      | (hcom $r $r $A $φ $cap) => $cap
      | _ => t

    -- Test: test
    -- (coe $(dim0) $(dim0) (univ $(lzero)) (lit str "A"))

  end Kan

  section FHCom

    def term : Parser :=
      ((annotated str "fhcom" term term term tubes → fhcom) <|> ((annotated str "boxEl" term term term tubes → boxEl) <|> (annotated str "capEl" term term term tubes term → capEl)))

  end FHCom

  section Sys

    def term : Parser :=
      (annotated str "sys" branches → sys)

    def branches : Parser :=
      (annotated many (branch) → branches)

    def branch : Parser :=
      (annotated str "(" term str "," term str ")" → branch)

  end Sys

  section VType

    def term : Parser :=
      ((annotated str "vtype" term term term term → vtype) <|> ((annotated str "vin" term term term → vin) <|> (annotated str "vproj" term term term term term → vproj)))

    def vin0 (t : Term) : Term :=
      match t with
      | (vin (dim0) $a $b) => $a
      | _ => t

    def vin1 (t : Term) : Term :=
      match t with
      | (vin (dim1) $a $b) => $b
      | _ => t

    -- Test: test
    -- (vin $(dim0) (lit str "a") (lit str "b"))

    -- Test: test
    -- (vin $(dim1) (lit str "a") (lit str "b"))

  end VType

  section Nat

    def term : Parser :=
      ((annotated str "nat" → nat) <|> ((annotated str "zero" → zero) <|> ((annotated str "suc" term → suc) <|> (annotated str "natElim" term term term term → natElim))))

    def natElimZero (t : Term) : Term :=
      match t with
      | (natElim $P $z $s (zero)) => $z
      | _ => t

    def natElimSuc (t : Term) : Term :=
      match t with
      | (natElim $P $z $s (suc $n)) => (app (app $s $n) (natElim $P $z $s $n))
      | _ => t

    -- Test: test
    -- (natElim $(P) $(z) $(s) $(zero))

  end Nat

  section Circle

    def term : Parser :=
      ((annotated str "circle" → circle) <|> ((annotated str "base" → base) <|> ((annotated str "loop" term → loop) <|> (annotated str "circleElim" term term term term → circleElim))))

    def loop0 (t : Term) : Term :=
      match t with
      | (loop (dim0)) => (base)
      | _ => t

    def loop1 (t : Term) : Term :=
      match t with
      | (loop (dim1)) => (base)
      | _ => t

    def circleElimBase (t : Term) : Term :=
      match t with
      | (circleElim $P $b $l (base)) => $b
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Circle

  section Extension

    def term : Parser :=
      ((annotated str "ext" (special <number>) term term term → ext) <|> ((annotated str "extLam" (special <number>) term → extLam) <|> (annotated str "extApp" term dimList → extApp)))

    def dimList : Parser :=
      (annotated many (term) → dimList)

  end Extension

  section Sub

    def term : Parser :=
      ((annotated str "sub" term term term → sub) <|> ((annotated str "subIn" term → subIn) <|> (annotated str "subOut" term → subOut)))

    def subBeta (t : Term) : Term :=
      match t with
      | (subOut (subIn $e)) => $e
      | _ => t

    -- Test: test
    -- ()

  end Sub

  section Shift

    def shiftIx (t : Term) : Term :=
      match t with
      | (shift $k $n (ix $m)) => (ix (if (geq $m $k) (add $m $n) $m))
      | _ => t

    def shiftLam (t : Term) : Term :=
      match t with
      | (shift $k $n (lam $body)) => (lam (shift (add $k (num (number 1))) $n $body))
      | _ => t

    def shiftApp (t : Term) : Term :=
      match t with
      | (shift $k $n (app $f $a)) => (app (shift $k $n $f) (shift $k $n $a))
      | _ => t

    def shiftPi (t : Term) : Term :=
      match t with
      | (shift $k $n (pi $A $B)) => (pi (shift $k $n $A) (shift (add $k (num (number 1))) $n $B))
      | _ => t

  end Shift

  section Subst

    def substIxHit (t : Term) : Term :=
      match t with
      | (subst $k $v (ix $k)) => $v
      | _ => t

    def substIxMiss (t : Term) : Term :=
      match t with
      | (subst $k $v (ix $m)) => (ix (if (gt $m $k) (sub $m (num (number 1))) $m))
      | _ => t

    def substLam (t : Term) : Term :=
      match t with
      | (subst $k $v (lam $body)) => (lam (subst (add $k (num (number 1))) (shift (num (number 0)) (num (number 1)) $v) $body))
      | _ => t

    def substApp (t : Term) : Term :=
      match t with
      | (subst $k $v (app $f $a)) => (app (subst $k $v $f) (subst $k $v $a))
      | _ => t

  end Subst

  section Normalize

    def normalize (t : Term) : Term :=
      match t with
      | (normalize $fuel $t) => (normalizeStep (sub $fuel (num (number 1))) (step $t))
      | _ => t

    def normalizeZero (t : Term) : Term :=
      match t with
      | (normalize (num (number 0)) $t) => $t
      | _ => t

    def normalizeStep (t : Term) : Term :=
      match t with
      | (normalizeStep $fuel (some $t)) => (normalize $fuel $t)
      | _ => t

    def normalizeStepNone (t : Term) : Term :=
      match t with
      | (normalizeStep $fuel (none)) => $t
      | _ => t

  end Normalize

end Core