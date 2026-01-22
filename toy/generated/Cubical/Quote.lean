(DImport import (modulePath Core) ;)

(DImport import (modulePath Domain) ;)

namespace Quote

  section QuoteEnv

    def qenv : Parser :=
      (annotated str "qenv" (special <number>) (special <number>) → qenv)

    def qenvEmpty (t : Term) : Term :=
      match t with
      | (qenvEmpty) => (qenv (num (number 0)) (num (number 0)))
      | _ => t

    def qenvSucc (t : Term) : Term :=
      match t with
      | (qenvSucc (qenv $l $dl)) => (qenv (suc $l) $dl)
      | _ => t

    def qenvSuccDim (t : Term) : Term :=
      match t with
      | (qenvSuccDim (qenv $l $dl)) => (qenv $l (suc $dl))
      | _ => t

    def levelToIndex (t : Term) : Term :=
      match t with
      | (levelToIndex (qenv $l $dl) $lvl) => (sub (sub $l $lvl) (num (number 1)))
      | _ => t

    def dimLevelToIndex (t : Term) : Term :=
      match t with
      | (dimLevelToIndex (qenv $l $dl) $lvl) => (sub (sub $dl $lvl) (num (number 1)))
      | _ => t

    -- Test: test
    -- (levelToIndex (qenv (num (number 3)) (num (number 0))) (num (number 0)))

  end QuoteEnv

  section Generic

    def generic (t : Term) : Term :=
      match t with
      | (generic (qenv $l $dl)) => (ix $l)
      | _ => t

    def genericDim (t : Term) : Term :=
      match t with
      | (genericDim (qenv $l $dl)) => (dimVar $dl)
      | _ => t

  end Generic

  section Shift

    def shiftFromIx (t : Term) : Term :=
      match t with
      | (shiftFrom (ix $k) $n $cutoff) => (if (geq $k $cutoff) (ix (add $k $n)) (ix $k))
      | _ => t

    def shiftFromLam (t : Term) : Term :=
      match t with
      | (shiftFrom (lam $body) $n $cutoff) => (lam (shiftFrom $body $n (suc $cutoff)))
      | _ => t

    def shiftFromApp (t : Term) : Term :=
      match t with
      | (shiftFrom (app $f $a) $n $cutoff) => (app (shiftFrom $f $n $cutoff) (shiftFrom $a $n $cutoff))
      | _ => t

    def shiftFromPi (t : Term) : Term :=
      match t with
      | (shiftFrom (pi $A $B) $n $cutoff) => (pi (shiftFrom $A $n $cutoff) (shiftFrom $B $n (suc $cutoff)))
      | _ => t

    def shiftFromSigma (t : Term) : Term :=
      match t with
      | (shiftFrom (sigma $A $B) $n $cutoff) => (sigma (shiftFrom $A $n $cutoff) (shiftFrom $B $n (suc $cutoff)))
      | _ => t

    def shiftFromPair (t : Term) : Term :=
      match t with
      | (shiftFrom (pair $a $b) $n $cutoff) => (pair (shiftFrom $a $n $cutoff) (shiftFrom $b $n $cutoff))
      | _ => t

    def shiftFromFst (t : Term) : Term :=
      match t with
      | (shiftFrom (fst $p) $n $cutoff) => (fst (shiftFrom $p $n $cutoff))
      | _ => t

    def shiftFromSnd (t : Term) : Term :=
      match t with
      | (shiftFrom (snd $p) $n $cutoff) => (snd (shiftFrom $p $n $cutoff))
      | _ => t

    def shiftFromPlam (t : Term) : Term :=
      match t with
      | (shiftFrom (plam $body) $n $cutoff) => (plam (shiftFrom $body $n $cutoff))
      | _ => t

    def shiftFromPapp (t : Term) : Term :=
      match t with
      | (shiftFrom (papp $p $r) $n $cutoff) => (papp (shiftFrom $p $n $cutoff) $r)
      | _ => t

    def shiftFromLit (t : Term) : Term :=
      match t with
      | (shiftFrom (lit $s) $n $cutoff) => (lit $s)
      | _ => t

    def shiftFromUniv (t : Term) : Term :=
      match t with
      | (shiftFrom (univ $l) $n $cutoff) => (univ $l)
      | _ => t

    def shiftFromDim (t : Term) : Term :=
      match t with
      | (shiftFrom $d $n $cutoff) => $d
      | _ => t

  end Shift

  section QuoteCon

    def quoteLit (t : Term) : Term :=
      match t with
      | (quoteCon $env (dlit $s)) => (lit $s)
      | _ => t

    def quoteLam (t : Term) : Term :=
      match t with
      | (quoteCon $env (dlam (dclo $body $cloEnv))) => (lam (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) (dtpUnknown))) $cloEnv) $body)))
      | _ => t

    def quotePair (t : Term) : Term :=
      match t with
      | (quoteCon $env (dpair $a $b)) => (pair (quoteCon $env $a) (quoteCon $env $b))
      | _ => t

    def quoteUniv (t : Term) : Term :=
      match t with
      | (quoteCon $env (duniv $l)) => (univ (quoteLevel $l))
      | _ => t

    def quotePi (t : Term) : Term :=
      match t with
      | (quoteCon $env (dpi $A (dclo $B $cloEnv))) => (pi (quoteTp $env $A) (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) $A)) $cloEnv) $B)))
      | _ => t

    def quoteSigma (t : Term) : Term :=
      match t with
      | (quoteCon $env (dsigma $A (dclo $B $cloEnv))) => (sigma (quoteTp $env $A) (quoteCon (qenvSucc $env) (deval (denvCons (dneu (dcut (dneuVar (qenvLevel $env)) $A)) $cloEnv) $B)))
      | _ => t

    def quotePath (t : Term) : Term :=
      match t with
      | (quoteCon $env (dpath $A $a $b)) => (path (quoteTp $env $A) (quoteCon $env $a) (quoteCon $env $b))
      | _ => t

    def quotePlam (t : Term) : Term :=
      match t with
      | (quoteCon $env (dplam (dclo $body $cloEnv))) => (plam (quoteCon (qenvSuccDim $env) (deval (denvCons (dneu (dcut (dneuVar (qenvDimLevel $env)) (dtpI))) $cloEnv) $body)))
      | _ => t

    def quoteRefl (t : Term) : Term :=
      match t with
      | (quoteCon $env (drefl $a)) => (refl (quoteCon $env $a))
      | _ => t

    def quoteNat (t : Term) : Term :=
      match t with
      | (quoteCon $env (dnat)) => (nat)
      | _ => t

    def quoteZero (t : Term) : Term :=
      match t with
      | (quoteCon $env (dzeroN)) => (zero)
      | _ => t

    def quoteSuc (t : Term) : Term :=
      match t with
      | (quoteCon $env (dsucN $n)) => (suc (quoteCon $env $n))
      | _ => t

    def quoteCircle (t : Term) : Term :=
      match t with
      | (quoteCon $env (dcircle)) => (circle)
      | _ => t

    def quoteBase (t : Term) : Term :=
      match t with
      | (quoteCon $env (dbase)) => (base)
      | _ => t

    def quoteLoop (t : Term) : Term :=
      match t with
      | (quoteCon $env (dloop $d)) => (loop (quoteDim $d))
      | _ => t

    def quoteNeu (t : Term) : Term :=
      match t with
      | (quoteCon $env (dneu $cut)) => (quoteNeutral $env $cut)
      | _ => t

  end QuoteCon

  section QuoteTp

    def quoteTpUniv (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpUniv $l)) => (univ (quoteLevel $l))
      | _ => t

    def quoteTpPi (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpPi $A $clo)) => (pi (quoteTp $env $A) (quoteTpClo (qenvSucc $env) $clo))
      | _ => t

    def quoteTpSigma (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpSigma $A $clo)) => (sigma (quoteTp $env $A) (quoteTpClo (qenvSucc $env) $clo))
      | _ => t

    def quoteTpPath (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpPath $A $a $b)) => (path (quoteTp $env $A) (quoteCon $env $a) (quoteCon $env $b))
      | _ => t

    def quoteTpNat (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpNat)) => (nat)
      | _ => t

    def quoteTpCircle (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpCircle)) => (circle)
      | _ => t

    def quoteTpNeu (t : Term) : Term :=
      match t with
      | (quoteTp $env (dtpNeu $cut)) => (quoteNeutral $env $cut)
      | _ => t

  end QuoteTp

  section QuoteNeutral

    def quoteNeuVar (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuVar $l) $tp)) => (ix (levelToIndex $env $l))
      | _ => t

    def quoteNeuApp (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuApp $neu $arg) $tp)) => (app (quoteNeutral $env (dcut $neu (dtpUnknown))) (quoteCon $env $arg))
      | _ => t

    def quoteNeuFst (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuFst $neu) $tp)) => (fst (quoteNeutral $env (dcut $neu (dtpUnknown))))
      | _ => t

    def quoteNeuSnd (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuSnd $neu) $tp)) => (snd (quoteNeutral $env (dcut $neu (dtpUnknown))))
      | _ => t

    def quoteNeuPApp (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuPApp $neu $d) $tp)) => (papp (quoteNeutral $env (dcut $neu (dtpUnknown))) (quoteDim $d))
      | _ => t

    def quoteNeuNatElim (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuNatElim $P $z $s $neu) $tp)) => (natElim (quoteCon $env $P) (quoteCon $env $z) (quoteCon $env $s) (quoteNeutral $env (dcut $neu (dtpNat))))
      | _ => t

    def quoteNeuCircleElim (t : Term) : Term :=
      match t with
      | (quoteNeutral $env (dcut (dneuCircleElim $P $b $l $neu) $tp)) => (circleElim (quoteCon $env $P) (quoteCon $env $b) (quoteCon $env $l) (quoteNeutral $env (dcut $neu (dtpCircle))))
      | _ => t

  end QuoteNeutral

  section QuoteLevel

    def quoteLevelConst (t : Term) : Term :=
      match t with
      | (quoteLevel (dconst $n)) => (ofNat $n)
      | _ => t

    def quoteLevelVar (t : Term) : Term :=
      match t with
      | (quoteLevel (dlvar $n)) => (lvar $n)
      | _ => t

    def quoteLevelMax (t : Term) : Term :=
      match t with
      | (quoteLevel (dmax $l1 $l2)) => (lmax (quoteLevel $l1) (quoteLevel $l2))
      | _ => t

    def quoteLevelSuc (t : Term) : Term :=
      match t with
      | (quoteLevel (dsuc $l)) => (lsuc (quoteLevel $l))
      | _ => t

    def ofNat0 (t : Term) : Term :=
      match t with
      | (ofNat (num (number 0))) => (lzero)
      | _ => t

    def ofNatS (t : Term) : Term :=
      match t with
      | (ofNat (suc $n)) => (lsuc (ofNat $n))
      | _ => t

  end QuoteLevel

  section QuoteDim

    def quoteDim0 (t : Term) : Term :=
      match t with
      | (quoteDim (ddim0)) => (dim0)
      | _ => t

    def quoteDim1 (t : Term) : Term :=
      match t with
      | (quoteDim (ddim1)) => (dim1)
      | _ => t

    def quoteDimVar (t : Term) : Term :=
      match t with
      | (quoteDim (dvar $n)) => (dimVar $n)
      | _ => t

  end QuoteDim

  section NbE

    def nbe (t : Term) : Term :=
      match t with
      | (nbe $t) => (quoteCon (qenvEmpty (deval (denvNil) $t)))
      | _ => t

    def nbeEnv (t : Term) : Term :=
      match t with
      | (nbeWithEnv $env $t) => (quoteCon (qenvEmpty (deval $env $t)))
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end NbE

end Quote