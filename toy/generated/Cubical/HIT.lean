(DImport import (modulePath Core) ;)

(DImport import (modulePath Kan) ;)

namespace HIT

  section HITKind

    def hitKind : Parser :=
      ((annotated str "natHIT" → natHIT) <|> (annotated str "circleHIT" → circleHIT))

    def hitKindToString (t : Term) : Term :=
      match t with
      | (hitKindToString (natHIT)) => str "Nat"
      | _ => t

    def hitKindToStringCircle (t : Term) : Term :=
      match t with
      | (hitKindToString (circleHIT)) => str "Circle"
      | _ => t

    def isNatHIT (t : Term) : Term :=
      match t with
      | (isNatHIT (natHIT)) => (true)
      | _ => t

    def isNatHITOther (t : Term) : Term :=
      match t with
      | (isNatHIT $k) => (false)
      | _ => t

    def isCircleHIT (t : Term) : Term :=
      match t with
      | (isCircleHIT (circleHIT)) => (true)
      | _ => t

    def isCircleHITOther (t : Term) : Term :=
      match t with
      | (isCircleHIT $k) => (false)
      | _ => t

  end HITKind

  section NatKan

    def hcomNatEq (t : Term) : Term :=
      match t with
      | (hcomNat $r $r $φ $tubes $base) => $base
      | _ => t

    def hcomNat (t : Term) : Term :=
      match t with
      | (hcomNat $r $r' $φ $tubes $base) => (hcomNatStep $φ $tubes $base)
      | _ => t

    def hcomNatStep (t : Term) : Term :=
      match t with
      | (hcomNatStep (cof_bot) $tubes $base) => $base
      | _ => t

    def hcomNatStepTrue (t : Term) : Term :=
      match t with
      | (hcomNatStep (cof_top) $tubes $base) => (app (app $tubes (dim1)) (lit str "trivial-proof"))
      | _ => t

    def hcomNatStepOther (t : Term) : Term :=
      match t with
      | (hcomNatStep $φ $tubes $base) => (hcom_nat $φ $tubes $base)
      | _ => t

    def coeNat (t : Term) : Term :=
      match t with
      | (coeNat $r $r' (lam (nat)) $v) => $v
      | _ => t

    def coeNatSimple (t : Term) : Term :=
      match t with
      | (coeNatSimple $r $r' $v) => $v
      | _ => t

  end NatKan

  section NatIntro

    def natZero (t : Term) : Term :=
      match t with
      | (natZero) => (intro (zero))
      | _ => t

    def natSucc (t : Term) : Term :=
      match t with
      | (natSucc $n) => (intro (succ $n))
      | _ => t

    def isNatIntro (t : Term) : Term :=
      match t with
      | (isNatIntro (intro (zero))) => (true)
      | _ => t

    def isNatIntroSucc (t : Term) : Term :=
      match t with
      | (isNatIntro (intro (succ $n))) => (true)
      | _ => t

    def isNatIntroOther (t : Term) : Term :=
      match t with
      | (isNatIntro $e) => (false)
      | _ => t

    def natIntroVal (t : Term) : Term :=
      match t with
      | (natIntroVal (intro (zero))) => (zero)
      | _ => t

    def natIntroValSucc (t : Term) : Term :=
      match t with
      | (natIntroVal (intro (succ $n))) => (succ $n)
      | _ => t

  end NatIntro

  section NatElim

    def natElim (t : Term) : Term :=
      match t with
      | (natElim $P $z $s (intro (zero))) => $z
      | _ => t

    def natElimSucc (t : Term) : Term :=
      match t with
      | (natElim $P $z $s (intro (succ $n))) => (app (app $s $n) (natElim $P $z $s $n))
      | _ => t

    def natElimNeutral (t : Term) : Term :=
      match t with
      | (natElim $P $z $s $n) => (elim (nat) $P $z $s $n)
      | _ => t

  end NatElim

  section CircleKan

    def hcomCircleEq (t : Term) : Term :=
      match t with
      | (hcomCircle $r $r $φ $tubes $cap) => $cap
      | _ => t

    def hcomCircle (t : Term) : Term :=
      match t with
      | (hcomCircle $r $r' $φ $tubes $cap) => (hcomCircleBody $r $r' $φ $tubes $cap)
      | _ => t

    def hcomCircleBody (t : Term) : Term :=
      match t with
      | (hcomCircleBody $r $r' $φ $tubes (intro (base))) => (intro (base))
      | _ => t

    def hcomCircleBodyLoop (t : Term) : Term :=
      match t with
      | (hcomCircleBody $r $r' $φ $tubes (intro (loop $i))) => (hcom_circle $r $r' $φ $tubes (intro (loop $i)))
      | _ => t

    def hcomCircleBodyOther (t : Term) : Term :=
      match t with
      | (hcomCircleBody $r $r' $φ $tubes $cap) => (hcom_circle $r $r' $φ $tubes $cap)
      | _ => t

    def coeCircle (t : Term) : Term :=
      match t with
      | (coeCircle $r $r' (lam (S1)) $v) => $v
      | _ => t

    def coeCircleSimple (t : Term) : Term :=
      match t with
      | (coeCircleSimple $r $r' $v) => $v
      | _ => t

  end CircleKan

  section CircleIntro

    def circleBase (t : Term) : Term :=
      match t with
      | (circleBase) => (intro (base))
      | _ => t

    def circleLoop (t : Term) : Term :=
      match t with
      | (circleLoop $i) => (intro (loop $i))
      | _ => t

    def isCircleIntro (t : Term) : Term :=
      match t with
      | (isCircleIntro (intro (base))) => (true)
      | _ => t

    def isCircleIntroLoop (t : Term) : Term :=
      match t with
      | (isCircleIntro (intro (loop $i))) => (true)
      | _ => t

    def isCircleIntroOther (t : Term) : Term :=
      match t with
      | (isCircleIntro $e) => (false)
      | _ => t

    def circleIntroKind (t : Term) : Term :=
      match t with
      | (circleIntroKind (intro (base))) => (base)
      | _ => t

    def circleIntroKindLoop (t : Term) : Term :=
      match t with
      | (circleIntroKind (intro (loop $i))) => (loop)
      | _ => t

  end CircleIntro

  section CircleElim

    def circleElim (t : Term) : Term :=
      match t with
      | (circleElim $P $b $l (intro (base))) => $b
      | _ => t

    def circleElimLoop (t : Term) : Term :=
      match t with
      | (circleElim $P $b $l (intro (loop $i))) => (papp $l $i)
      | _ => t

    def circleElimNeutral (t : Term) : Term :=
      match t with
      | (circleElim $P $b $l $x) => (elim (circle) $P $b $l $x)
      | _ => t

  end CircleElim

  section LoopSpace

    def loopRefl (t : Term) : Term :=
      match t with
      | (loopRefl) => (plam (lit str "_") (intro (base)))
      | _ => t

    def loopPath (t : Term) : Term :=
      match t with
      | (loopPath) => (plam (lit str "i") (intro (loop (ix (num (number 0))))))
      | _ => t

    def loopConcat (t : Term) : Term :=
      match t with
      | (loopConcat $p $q) => (plam (lit str "i") (hcom (S1) (dim0) (dim1 (paren ( (cof_disj (paren ( (cof_eq (ix (num (number 0))) dim0) )) (paren ( (cof_eq (ix (num (number 0))) dim1) ))) )) (paren ( (lam (paren ( (lam (paren ( (cofSplit (ix (num (number 1))) (paren ( (cof_eq (ix (num (number 1))) dim0) )) (paren ( (papp (shift (num (number 0)) (num (number 2)) $p) (ix (num (number 0)))) )) (paren ( (cof_eq (ix (num (number 1))) dim1) )) (paren ( (papp (shift (num (number 0)) (num (number 2)) $q) (ix (num (number 0)))) ))) ))) ))) )) (intro (base)))))
      | _ => t

    def loopInverse (t : Term) : Term :=
      match t with
      | (loopInverse $p) => (plam (lit str "i") (papp $p (dim_neg (ix (num (number 0))))))
      | _ => t

  end LoopSpace

  section HITDispatch

    def hitHcom (t : Term) : Term :=
      match t with
      | (hitHcom (natHIT) $r $r' $φ $tubes $cap) => (hcomNat $r $r' $φ $tubes $cap)
      | _ => t

    def hitHcomCircle (t : Term) : Term :=
      match t with
      | (hitHcom (circleHIT) $r $r' $φ $tubes $cap) => (hcomCircle $r $r' $φ $tubes $cap)
      | _ => t

    def hitCoe (t : Term) : Term :=
      match t with
      | (hitCoe (natHIT) $r $r' $line $v) => (coeNatSimple $r $r' $v)
      | _ => t

    def hitCoeCircle (t : Term) : Term :=
      match t with
      | (hitCoe (circleHIT) $r $r' $line $v) => (coeCircleSimple $r $r' $v)
      | _ => t

  end HITDispatch

  section HITBoundary

    def loopBoundary0 (t : Term) : Term :=
      match t with
      | (loopBoundary (intro (loop (dim0)))) => (intro (base))
      | _ => t

    def loopBoundary1 (t : Term) : Term :=
      match t with
      | (loopBoundary (intro (loop (dim1)))) => (intro (base))
      | _ => t

    def loopBoundaryOk (t : Term) : Term :=
      match t with
      | (checkLoopBoundary (intro (base)) (intro (base))) => (true)
      | _ => t

    def hitCheckBoundaryNat (t : Term) : Term :=
      match t with
      | (hitCheckBoundary (natHIT) $ctor $bounds) => (true)
      | _ => t

    def hitCheckBoundaryCircle (t : Term) : Term :=
      match t with
      | (hitCheckBoundary (circleHIT) $ctor $bounds) => (checkCircleBoundary $ctor $bounds)
      | _ => t

    def checkCircleBoundary (t : Term) : Term :=
      match t with
      | (checkCircleBoundary (base) $bounds) => (true)
      | _ => t

    def checkCircleBoundaryLoop (t : Term) : Term :=
      match t with
      | (checkCircleBoundary (loop $i) $bounds) => (and (eq (subst (num (number 0)) (dim0) $bounds) (intro (base))) (eq (subst (num (number 0)) (dim1) $bounds) (intro (base))))
      | _ => t

  end HITBoundary

  section HITQuote

    def quoteNat (t : Term) : Term :=
      match t with
      | (quoteHIT (natHIT) (intro (zero))) => (surface (zero))
      | _ => t

    def quoteNatSucc (t : Term) : Term :=
      match t with
      | (quoteHIT (natHIT) (intro (succ $n))) => (surface (succ (quoteHIT (natHIT) $n)))
      | _ => t

    def quoteCircle (t : Term) : Term :=
      match t with
      | (quoteHIT (circleHIT) (intro (base))) => (surface (base))
      | _ => t

    def quoteCircleLoop (t : Term) : Term :=
      match t with
      | (quoteHIT (circleHIT) (intro (loop $i))) => (surface (loop (quoteDim $i)))
      | _ => t

  end HITQuote

  section HITNormalize

    def normalizeNat (t : Term) : Term :=
      match t with
      | (normalizeHIT (natHIT) (intro (zero))) => (intro (zero))
      | _ => t

    def normalizeNatSucc (t : Term) : Term :=
      match t with
      | (normalizeHIT (natHIT) (intro (succ $n))) => (intro (succ (normalizeHIT (natHIT) $n)))
      | _ => t

    def normalizeCircle (t : Term) : Term :=
      match t with
      | (normalizeHIT (circleHIT) (intro (base))) => (intro (base))
      | _ => t

    def normalizeCircleLoop (t : Term) : Term :=
      match t with
      | (normalizeHIT (circleHIT) (intro (loop $i))) => (intro (loop (normalizeDim $i)))
      | _ => t

    def normalizeCircleLoop0 (t : Term) : Term :=
      match t with
      | (normalizeHIT (circleHIT) (intro (loop (dim0)))) => (intro (base))
      | _ => t

    def normalizeCircleLoop1 (t : Term) : Term :=
      match t with
      | (normalizeHIT (circleHIT) (intro (loop (dim1)))) => (intro (base))
      | _ => t

  end HITNormalize

end HIT