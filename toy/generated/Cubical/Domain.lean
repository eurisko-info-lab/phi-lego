(DImport import (modulePath Core) ;)

namespace Domain

  section DLevel

    def dlevel : Parser :=
      ((annotated str "const" (special <number>) → dconst) <|> ((annotated str "dlvar" (special <number>) → dlvar) <|> ((annotated str "dmax" dlevel dlevel → dmax) <|> (annotated str "dsuc" dlevel → dsuc))))

    def dlevZero (t : Term) : Term :=
      match t with
      | (dzero) => (dconst (num (number 0)))
      | _ => t

    def dlevOne (t : Term) : Term :=
      match t with
      | (done) => (dconst (num (number 1)))
      | _ => t

    def ofLevelZero (t : Term) : Term :=
      match t with
      | (ofLevel (lzero)) => (dzero)
      | _ => t

    def ofLevelSuc (t : Term) : Term :=
      match t with
      | (ofLevel (lsuc $l)) => (dsuc (ofLevel $l))
      | _ => t

    def ofLevelMax (t : Term) : Term :=
      match t with
      | (ofLevel (lmax $l1 $l2)) => (dmax (ofLevel $l1) (ofLevel $l2))
      | _ => t

    def ofLevelVar (t : Term) : Term :=
      match t with
      | (ofLevel (lvar $n)) => (dlvar $n)
      | _ => t

  end DLevel

  section Dim

    def dim : Parser :=
      ((annotated str "ddim0" → ddim0) <|> ((annotated str "ddim1" → ddim1) <|> (annotated str "dvar" (special <number>) → dvar)))

    def dimOfExprD0 (t : Term) : Term :=
      match t with
      | (dimOfExpr (dim0)) => (some (ddim0))
      | _ => t

    def dimOfExprD1 (t : Term) : Term :=
      match t with
      | (dimOfExpr (dim1)) => (some (ddim1))
      | _ => t

    def dimOfExprVar (t : Term) : Term :=
      match t with
      | (dimOfExpr (dimVar $n)) => (some (dvar $n))
      | _ => t

    def dimOfExprOther (t : Term) : Term :=
      match t with
      | (dimOfExpr $e) => (none)
      | _ => t

    def dimToExprD0 (t : Term) : Term :=
      match t with
      | (dimToExpr (ddim0)) => (dim0)
      | _ => t

    def dimToExprD1 (t : Term) : Term :=
      match t with
      | (dimToExpr (ddim1)) => (dim1)
      | _ => t

    def dimToExprVar (t : Term) : Term :=
      match t with
      | (dimToExpr (dvar $n)) => (dimVar $n)
      | _ => t

    def dimEqD0 (t : Term) : Term :=
      match t with
      | (dimEqD (ddim0) (ddim0)) => (true)
      | _ => t

    def dimEqD1 (t : Term) : Term :=
      match t with
      | (dimEqD (ddim1) (ddim1)) => (true)
      | _ => t

    def dimEqVar (t : Term) : Term :=
      match t with
      | (dimEqD (dvar $n) (dvar $m)) => (eq $n $m)
      | _ => t

    def dimEqMixed (t : Term) : Term :=
      match t with
      | (dimEqD $d1 $d2) => (false)
      | _ => t

    -- Test: test
    -- (dimEqD $(ddim0) $(ddim0))

    -- Test: test
    -- (dimEqD $(ddim0) $(ddim1))

  end Dim

  section DCof

    def dcof : Parser :=
      ((annotated str "dcof_top" → dcof_top) <|> ((annotated str "dcof_bot" → dcof_bot) <|> ((annotated str "dcof_eq" dim dim → dcof_eq) <|> ((annotated str "dcof_join" dcof dcof → dcof_join) <|> (annotated str "dcof_meet" dcof dcof → dcof_meet)))))

    def isTrueTop (t : Term) : Term :=
      match t with
      | (dCofIsTrue (dcof_top)) => (true)
      | _ => t

    def isTrueBot (t : Term) : Term :=
      match t with
      | (dCofIsTrue (dcof_bot)) => (false)
      | _ => t

    def isTrueEq (t : Term) : Term :=
      match t with
      | (dCofIsTrue (dcof_eq $d1 $d2)) => (dimEqD $d1 $d2)
      | _ => t

    def isTrueJoin (t : Term) : Term :=
      match t with
      | (dCofIsTrue (dcof_join $φ $ψ)) => (or (dCofIsTrue $φ) (dCofIsTrue $ψ))
      | _ => t

    def isTrueMeet (t : Term) : Term :=
      match t with
      | (dCofIsTrue (dcof_meet $φ $ψ)) => (and (dCofIsTrue $φ) (dCofIsTrue $ψ))
      | _ => t

    def isFalse (t : Term) : Term :=
      match t with
      | (dCofIsFalse $φ) => (not (dCofIsTrue $φ))
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end DCof

  section DEnv

    def denv : Parser :=
      ((annotated str "denvNil" → denvNil) <|> (annotated str "denvCons" dcon denv → denvCons))

    def envLookup0 (t : Term) : Term :=
      match t with
      | (denvLookup (num (number 0)) (denvCons $v $rest)) => (some $v)
      | _ => t

    def envLookupS (t : Term) : Term :=
      match t with
      | (denvLookup (suc $n) (denvCons $v $rest)) => (denvLookup $n $rest)
      | _ => t

    def envLookupNil (t : Term) : Term :=
      match t with
      | (denvLookup $n (denvNil)) => (none)
      | _ => t

    def envExtend (t : Term) : Term :=
      match t with
      | (denvExtend $v $env) => (denvCons $v $env)
      | _ => t

    -- Test: test
    -- (denvLookup (num (number 0)) (denvCons (dlit str "x") $(denvNil)))

  end DEnv

  section DClo

    def dclo : Parser :=
      (annotated str "dclo" term denv → dclo)

    def cloApply (t : Term) : Term :=
      match t with
      | (dCloApply (dclo $body $env) $arg) => (deval (denvCons $arg $env) $body)
      | _ => t

  end DClo

  section DCon

    def dcon : Parser :=
      ((annotated str "dlit" (special <string>) → dlit) <|> ((annotated str "dlam" dclo → dlam) <|> ((annotated str "dpair" dcon dcon → dpair) <|> ((annotated str "dpi" dtp dclo → dpi) <|> ((annotated str "dsigma" dtp dclo → dsigma) <|> ((annotated str "duniv" dlevel → duniv) <|> ((annotated str "dpath" dtp dcon dcon → dpath) <|> ((annotated str "dplam" dclo → dplam) <|> ((annotated str "drefl" dcon → drefl) <|> ((annotated str "dnat" → dnat) <|> ((annotated str "dzero" → dzeroN) <|> ((annotated str "dsuc" dcon → dsucN) <|> ((annotated str "dcircle" → dcircle) <|> ((annotated str "dbase" → dbase) <|> ((annotated str "dloop" dim → dloop) <|> (annotated str "dneu" dcut → dneu))))))))))))))))

  end DCon

  section DTp

    def dtp : Parser :=
      ((annotated str "dtpUniv" dlevel → dtpUniv) <|> ((annotated str "dtpPi" dtp dclo → dtpPi) <|> ((annotated str "dtpSigma" dtp dclo → dtpSigma) <|> ((annotated str "dtpPath" dtp dcon dcon → dtpPath) <|> ((annotated str "dtpNat" → dtpNat) <|> ((annotated str "dtpCircle" → dtpCircle) <|> (annotated str "dtpNeu" dcut → dtpNeu)))))))

  end DTp

  section DCut

    def dcut : Parser :=
      (annotated str "dcut" dneu dtp → dcut)

    def dneu : Parser :=
      ((annotated str "dneuVar" (special <number>) → dneuVar) <|> ((annotated str "dneuApp" dneu dcon → dneuApp) <|> ((annotated str "dneuFst" dneu → dneuFst) <|> ((annotated str "dneuSnd" dneu → dneuSnd) <|> ((annotated str "dneuPApp" dneu dim → dneuPApp) <|> ((annotated str "dneuNatElim" dcon dcon dcon dneu → dneuNatElim) <|> (annotated str "dneuCircleElim" dcon dcon dcon dneu → dneuCircleElim)))))))

  end DCut

  section Eval

    def evalIx (t : Term) : Term :=
      match t with
      | (deval $env (ix $n)) => (fromOption (denvLookup $n $env) (dneu (dcut (dneuVar $n) (dtpUnknown))))
      | _ => t

    def evalLit (t : Term) : Term :=
      match t with
      | (deval $env (lit $s)) => (dlit $s)
      | _ => t

    def evalLam (t : Term) : Term :=
      match t with
      | (deval $env (lam $body)) => (dlam (dclo $body $env))
      | _ => t

    def evalApp (t : Term) : Term :=
      match t with
      | (deval $env (app $f $a)) => (dApply (deval $env $f) (deval $env $a))
      | _ => t

    def evalPi (t : Term) : Term :=
      match t with
      | (deval $env (pi $A $B)) => (dpi (dtpOf (deval $env $A)) (dclo $B $env))
      | _ => t

    def evalSigma (t : Term) : Term :=
      match t with
      | (deval $env (sigma $A $B)) => (dsigma (dtpOf (deval $env $A)) (dclo $B $env))
      | _ => t

    def evalPair (t : Term) : Term :=
      match t with
      | (deval $env (pair $a $b)) => (dpair (deval $env $a) (deval $env $b))
      | _ => t

    def evalFst (t : Term) : Term :=
      match t with
      | (deval $env (fst $p)) => (dFst (deval $env $p))
      | _ => t

    def evalSnd (t : Term) : Term :=
      match t with
      | (deval $env (snd $p)) => (dSnd (deval $env $p))
      | _ => t

    def evalUniv (t : Term) : Term :=
      match t with
      | (deval $env (univ $l)) => (duniv (ofLevel $l))
      | _ => t

    def evalPath (t : Term) : Term :=
      match t with
      | (deval $env (path $A $a $b)) => (dpath (dtpOf (deval $env $A)) (deval $env $a) (deval $env $b))
      | _ => t

    def evalPlam (t : Term) : Term :=
      match t with
      | (deval $env (plam $body)) => (dplam (dclo $body $env))
      | _ => t

    def evalPapp (t : Term) : Term :=
      match t with
      | (deval $env (papp $p $r)) => (dPApp (deval $env $p) (dimOfExprForce $r))
      | _ => t

    def evalRefl (t : Term) : Term :=
      match t with
      | (deval $env (refl $a)) => (drefl (deval $env $a))
      | _ => t

    def evalNat (t : Term) : Term :=
      match t with
      | (deval $env (nat)) => (dnat)
      | _ => t

    def evalZero (t : Term) : Term :=
      match t with
      | (deval $env (zero)) => (dzeroN)
      | _ => t

    def evalSuc (t : Term) : Term :=
      match t with
      | (deval $env (suc $n)) => (dsucN (deval $env $n))
      | _ => t

    def evalCircle (t : Term) : Term :=
      match t with
      | (deval $env (circle)) => (dcircle)
      | _ => t

    def evalBase (t : Term) : Term :=
      match t with
      | (deval $env (base)) => (dbase)
      | _ => t

    def evalLoop (t : Term) : Term :=
      match t with
      | (deval $env (loop $r)) => (dloop (dimOfExprForce $r))
      | _ => t

  end Eval

  section Operations

    def applyLam (t : Term) : Term :=
      match t with
      | (dApply (dlam $clo) $arg) => (dCloApply $clo $arg)
      | _ => t

    def applyNeu (t : Term) : Term :=
      match t with
      | (dApply (dneu (dcut $neu $tp)) $arg) => (dneu (dcut (dneuApp $neu $arg) (dtpApply $tp $arg)))
      | _ => t

    def fstPair (t : Term) : Term :=
      match t with
      | (dFst (dpair $a $b)) => $a
      | _ => t

    def fstNeu (t : Term) : Term :=
      match t with
      | (dFst (dneu (dcut $neu $tp))) => (dneu (dcut (dneuFst $neu) (dtpFst $tp)))
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | (dSnd (dpair $a $b)) => $b
      | _ => t

    def sndNeu (t : Term) : Term :=
      match t with
      | (dSnd (dneu (dcut $neu $tp))) => (dneu (dcut (dneuSnd $neu) (dtpSnd $tp)))
      | _ => t

    def pappPlam (t : Term) : Term :=
      match t with
      | (dPApp (dplam $clo) $d) => (dCloApplyDim $clo $d)
      | _ => t

    def pappRefl (t : Term) : Term :=
      match t with
      | (dPApp (drefl $a) $d) => $a
      | _ => t

    def pappNeu (t : Term) : Term :=
      match t with
      | (dPApp (dneu (dcut $neu $tp)) $d) => (dneu (dcut (dneuPApp $neu $d) (dtpPApp $tp $d)))
      | _ => t

    -- Test: test
    -- (dApply (dlam (dclo (ix (num (number 0))) $(denvNil))) (dlit str "x"))

    -- Test: test
    -- ()

  end Operations

end Domain