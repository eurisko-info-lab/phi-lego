(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

(DImport import (modulePath Visitor) ;)

namespace Conversion

  section ConvResult

    def convOk : Parser :=
      (annotated str "ok" → convResult)

    def convFail : Parser :=
      (annotated str "fail" (special <string>) → convResult)

    def convBlocked : Parser :=
      (annotated str "blocked" (special <number>) → convResult)

    def convResultIsOk (t : Term) : Term :=
      match t with
      | (isOk (ok)) => (true)
      | _ => t

    def convResultIsOkFail (t : Term) : Term :=
      match t with
      | (isOk (fail $msg)) => (false)
      | _ => t

    def convResultIsOkBlocked (t : Term) : Term :=
      match t with
      | (isOk (blocked $n)) => (false)
      | _ => t

    def convAndThenOk (t : Term) : Term :=
      match t with
      | (andThen (ok) $k) => ($k (unit))
      | _ => t

    def convAndThenFail (t : Term) : Term :=
      match t with
      | (andThen (fail $msg) $k) => (fail $msg)
      | _ => t

    def convAndThenBlocked (t : Term) : Term :=
      match t with
      | (andThen (blocked $n) $k) => (blocked $n)
      | _ => t

  end ConvResult

  section ConvCtx

    def convCtx : Parser :=
      (annotated str "convCtx" str "size:" (special <number>) str "cof:" (special <expr>) → convCtx)

    def convCtxEmpty (t : Term) : Term :=
      match t with
      | (convCtxEmpty) => (convCtx (labeledArg size : (num (number 0))) (labeledArg cof : (cof_top)))
      | _ => t

    def convCtxExtend (t : Term) : Term :=
      match t with
      | (convCtxExtend (convCtx (labeledArg size : $s) (labeledArg cof : $φ))) => (convCtx (labeledArg size : (suc $s)) (labeledArg cof : $φ))
      | _ => t

    def convCtxAssume (t : Term) : Term :=
      match t with
      | (convCtxAssume (convCtx (labeledArg size : $s) (labeledArg cof : $φ)) $ψ) => (convCtx (labeledArg size : $s) (labeledArg cof : (cof_and $φ $ψ)))
      | _ => t

  end ConvCtx

  section WHNF

    def defaultFuel (t : Term) : Term :=
      match t with
      | (defaultFuel) => (num (number 1000))
      | _ => t

    def whnf (t : Term) : Term :=
      match t with
      | (whnf $fuel $e) => (whnfStep $fuel $e)
      | _ => t

    def whnfStep0 (t : Term) : Term :=
      match t with
      | (whnfStep (num (number 0)) $e) => $e
      | _ => t

    def whnfStep (t : Term) : Term :=
      match t with
      | (whnfStep (suc $fuel) $e) => (caseExpr ( case (tryStep $e) (arm ( some $e' ) => (whnfStep $fuel $e')) (arm none => $e) ))
      | _ => t

    def tryStepApp (t : Term) : Term :=
      match t with
      | (tryStep (app (lam $body) $arg)) => (some (subst (num (number 0)) $arg $body))
      | _ => t

    def tryStepFst (t : Term) : Term :=
      match t with
      | (tryStep (fst (pair $a $b))) => (some $a)
      | _ => t

    def tryStepSnd (t : Term) : Term :=
      match t with
      | (tryStep (snd (pair $a $b))) => (some $b)
      | _ => t

    def tryStepPapp (t : Term) : Term :=
      match t with
      | (tryStep (papp (plam $body) $r)) => (some (dimSubst (num (number 0)) $r $body))
      | _ => t

    def tryStepDefault (t : Term) : Term :=
      match t with
      | (tryStep $e) => (none)
      | _ => t

  end WHNF

  section EquateDim

    def equateDim (t : Term) : Term :=
      match t with
      | (equateDim $ctx $r1 $r2) => (letIn ( let r1' = (whnf (defaultFuel) $r1) in (letIn let r2' = (whnf (defaultFuel) $r2) in (equateDim' $ctx (r1') (r2'))) ))
      | _ => t

    def equateDim'Same (t : Term) : Term :=
      match t with
      | (equateDim' $ctx $r $r) => (ok)
      | _ => t

    def equateDim'00 (t : Term) : Term :=
      match t with
      | (equateDim' $ctx (dim0) (dim0)) => (ok)
      | _ => t

    def equateDim'11 (t : Term) : Term :=
      match t with
      | (equateDim' $ctx (dim1) (dim1)) => (ok)
      | _ => t

    def equateDim'IxEq (t : Term) : Term :=
      match t with
      | (equateDim' $ctx (ix $n) (ix $n)) => (ok)
      | _ => t

    def equateDim'IxNeq (t : Term) : Term :=
      match t with
      | (equateDim' $ctx (ix $n) (ix $m)) => (fail (concat str "dimensions differ: " $n str " vs " $m))
      | _ => t

    def equateDim'Other (t : Term) : Term :=
      match t with
      | (equateDim' $ctx $r1 $r2) => (fail (concat str "dimensions not equal: " $r1 str " vs " $r2))
      | _ => t

  end EquateDim

  section EquateCof

    def equateCof (t : Term) : Term :=
      match t with
      | (equateCof $ctx $φ1 $φ2) => (letIn ( let φ1' = (whnf (defaultFuel) $φ1) in (letIn let φ2' = (whnf (defaultFuel) $φ2) in (equateCof' $ctx (φ1') (φ2'))) ))
      | _ => t

    def equateCof'Same (t : Term) : Term :=
      match t with
      | (equateCof' $ctx $φ $φ) => (ok)
      | _ => t

    def equateCof'Top (t : Term) : Term :=
      match t with
      | (equateCof' $ctx (cof_top) (cof_top)) => (ok)
      | _ => t

    def equateCof'Bot (t : Term) : Term :=
      match t with
      | (equateCof' $ctx (cof_bot) (cof_bot)) => (ok)
      | _ => t

    def equateCof'Eq (t : Term) : Term :=
      match t with
      | (equateCof' $ctx (cof_eq $r1 $s1) (cof_eq $r2 $s2)) => (andThen (equateDim $ctx $r1 $r2) (fun (_) (=>) (equateDim $ctx $s1 $s2)))
      | _ => t

    def equateCof'And (t : Term) : Term :=
      match t with
      | (equateCof' $ctx (cof_and $φ1a $φ1b) (cof_and $φ2a $φ2b)) => (andThen (equateCof $ctx $φ1a $φ2a) (fun (_) (=>) (equateCof $ctx $φ1b $φ2b)))
      | _ => t

    def equateCof'Or (t : Term) : Term :=
      match t with
      | (equateCof' $ctx (cof_or $φ1a $φ1b) (cof_or $φ2a $φ2b)) => (andThen (equateCof $ctx $φ1a $φ2a) (fun (_) (=>) (equateCof $ctx $φ1b $φ2b)))
      | _ => t

    def equateCof'Other (t : Term) : Term :=
      match t with
      | (equateCof' $ctx $φ1 $φ2) => (fail (concat str "cofibrations not equal: " $φ1 str " vs " $φ2))
      | _ => t

  end EquateCof

  section EquateTp

    def equateTp (t : Term) : Term :=
      match t with
      | (equateTp $ctx $tp1 $tp2) => (letIn ( let tp1' = (whnf (defaultFuel) $tp1) in (letIn let tp2' = (whnf (defaultFuel) $tp2) in (equateTp' $ctx (tp1') (tp2'))) ))
      | _ => t

    def equateTp'Same (t : Term) : Term :=
      match t with
      | (equateTp' $ctx $tp $tp) => (ok)
      | _ => t

    def equateTp'Nat (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (nat) (nat)) => (ok)
      | _ => t

    def equateTp'Circle (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (circle) (circle)) => (ok)
      | _ => t

    def equateTp'Univ (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (univ $n) (univ $n)) => (ok)
      | _ => t

    def equateTp'UnivNeq (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (univ $n1) (univ $n2)) => (fail (concat str "universe levels differ: " $n1 str " vs " $n2))
      | _ => t

    def equateTp'Dim (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (lit str "𝕀") (lit str "𝕀")) => (ok)
      | _ => t

    def equateTp'Cof (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (lit str "𝔽") (lit str "𝔽")) => (ok)
      | _ => t

    def equateTp'Pi (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (pi $dom1 $cod1) (pi $dom2 $cod2)) => (andThen (equateTp $ctx $dom1 $dom2) (fun (_) (=>) (equateTp (convCtxExtend $ctx) $cod1 $cod2)))
      | _ => t

    def equateTp'Sigma (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (sigma $a1 $b1) (sigma $a2 $b2)) => (andThen (equateTp $ctx $a1 $a2) (fun (_) (=>) (equateTp (convCtxExtend $ctx) $b1 $b2)))
      | _ => t

    def equateTp'Path (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (path $a1 $l1 $r1) (path $a2 $l2 $r2)) => (andThen (equateTp $ctx $a1 $a2) (fun (_) (=>) (andThen (equateCon $ctx $a1 $l1 $l2) (fun (_) (=>) (equateCon $ctx $a1 $r1 $r2)))))
      | _ => t

    def equateTp'Sub (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (sub $a1 $φ1 $t1) (sub $a2 $φ2 $t2)) => (andThen (equateTp $ctx $a1 $a2) (fun (_) (=>) (andThen (equateCof $ctx $φ1 $φ2) (fun (_) (=>) (equateCon (convCtxAssume $ctx $φ1) $a1 $t1 $t2)))))
      | _ => t

    def equateTp'VType (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (vtype $r1 $a1 $b1 $e1) (vtype $r2 $a2 $b2 $e2)) => (andThen (equateDim $ctx $r1 $r2) (fun (_) (=>) (andThen (equateTp $ctx $a1 $a2) (fun (_) (=>) (andThen (equateTp $ctx $b1 $b2) (fun (_) (=>) (equateCon $ctx (lit str "Equiv") $e1 $e2)))))))
      | _ => t

    def equateTp'Lit (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (lit $s) (lit $s)) => (ok)
      | _ => t

    def equateTp'LitNeq (t : Term) : Term :=
      match t with
      | (equateTp' $ctx (lit $s1) (lit $s2)) => (fail (concat str "type literals differ: " $s1 str " vs " $s2))
      | _ => t

    def equateTp'Other (t : Term) : Term :=
      match t with
      | (equateTp' $ctx $tp1 $tp2) => (fail (concat str "types not equal: " $tp1 str " vs " $tp2))
      | _ => t

  end EquateTp

  section EquateCon

    def equateCon (t : Term) : Term :=
      match t with
      | (equateCon $ctx $tp $t1 $t2) => (letIn ( let t1' = (whnf (defaultFuel) $t1) in (letIn let t2' = (whnf (defaultFuel) $t2) in (caseExpr ( case (eq (t1') (t2')) (arm true => (ok)) (arm false => (equateCon' $ctx (whnf (defaultFuel) $tp) (t1') (t2'))) ))) ))
      | _ => t

    def equateCon'Pi (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (pi $dom $cod) $t1 $t2) => (letIn ( let ctx' = (convCtxExtend $ctx) in (letIn let var = (ix (num (number 0))) in (letIn let app1 = (app (shift (num (number 0)) (num (number 1)) $t1) (var)) in (letIn let app2 = (app (shift (num (number 0)) (num (number 1)) $t2) (var)) in (equateCon (ctx') $cod (app1) (app2))))) ))
      | _ => t

    def equateCon'Sigma (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (sigma $a $b) $t1 $t2) => (letIn ( let fst1 = (fst $t1) in (letIn let fst2 = (fst $t2) in (andThen (equateCon $ctx $a (fst1) (fst2)) (fun (_) (=>) (letIn ( let snd1 = (snd $t1) in (letIn let snd2 = (snd $t2) in (letIn let b' = (subst (num (number 0)) (fst1) $b) in (equateCon $ctx (b') (snd1) (snd2)))) ))))) ))
      | _ => t

    def equateCon'Path (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (path $a $l $r) $t1 $t2) => (letIn ( let ctx' = (convCtxExtend $ctx) in (letIn let var = (ix (num (number 0))) in (letIn let papp1 = (papp (shift (num (number 0)) (num (number 1)) $t1) (var)) in (letIn let papp2 = (papp (shift (num (number 0)) (num (number 1)) $t2) (var)) in (equateCon (ctx') $a (papp1) (papp2))))) ))
      | _ => t

    def equateCon'Sub (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (sub $a $φ $u) $t1 $t2) => (letIn ( let out1 = (subOut $t1) in (letIn let out2 = (subOut $t2) in (equateCon $ctx $a (out1) (out2))) ))
      | _ => t

    def equateCon'NatZero (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (nat) (zero) (zero)) => (ok)
      | _ => t

    def equateCon'NatSuc (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (nat) (suc $n1) (suc $n2)) => (equateCon $ctx (nat) $n1 $n2)
      | _ => t

    def equateCon'Nat (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (nat) $t1 $t2) => (equateNeutral $ctx $t1 $t2)
      | _ => t

    def equateCon'CircleBase (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (circle) (base) (base)) => (ok)
      | _ => t

    def equateCon'CircleLoop (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (circle) (loop $r1) (loop $r2)) => (equateDim $ctx $r1 $r2)
      | _ => t

    def equateCon'Circle (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (circle) $t1 $t2) => (equateNeutral $ctx $t1 $t2)
      | _ => t

    def equateCon'Dim (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (lit str "𝕀") $t1 $t2) => (equateDim $ctx $t1 $t2)
      | _ => t

    def equateCon'Cof (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (lit str "𝔽") $t1 $t2) => (equateCof $ctx $t1 $t2)
      | _ => t

    def equateCon'Univ (t : Term) : Term :=
      match t with
      | (equateCon' $ctx (univ $l) $t1 $t2) => (equateTp $ctx $t1 $t2)
      | _ => t

    def equateCon'Other (t : Term) : Term :=
      match t with
      | (equateCon' $ctx $tp $t1 $t2) => (equateNeutral $ctx $t1 $t2)
      | _ => t

  end EquateCon

  section EquateNeutral

    def equateNeutralIx (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (ix $n) (ix $n)) => (ok)
      | _ => t

    def equateNeutralIxNeq (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (ix $n1) (ix $n2)) => (fail (concat str "variables differ: " $n1 str " vs " $n2))
      | _ => t

    def equateNeutralApp (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (app $f1 $a1) (app $f2 $a2)) => (andThen (equateNeutral $ctx $f1 $f2) (fun (_) (=>) (equateNeutral $ctx $a1 $a2)))
      | _ => t

    def equateNeutralPapp (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (papp $p1 $r1) (papp $p2 $r2)) => (andThen (equateNeutral $ctx $p1 $p2) (fun (_) (=>) (equateDim $ctx $r1 $r2)))
      | _ => t

    def equateNeutralFst (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (fst $p1) (fst $p2)) => (equateNeutral $ctx $p1 $p2)
      | _ => t

    def equateNeutralSnd (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (snd $p1) (snd $p2)) => (equateNeutral $ctx $p1 $p2)
      | _ => t

    def equateNeutralCoe (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (coe $a1 $r1 $s1 $t1) (coe $a2 $r2 $s2 $t2)) => (andThen (equateNeutral $ctx $a1 $a2) (fun (_) (=>) (andThen (equateDim $ctx $r1 $r2) (fun (_) (=>) (andThen (equateDim $ctx $s1 $s2) (fun (_) (=>) (equateNeutral $ctx $t1 $t2)))))))
      | _ => t

    def equateNeutralHCom (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (hcom $a1 $r1 $s1 $φ1 $u1) (hcom $a2 $r2 $s2 $φ2 $u2)) => (andThen (equateNeutral $ctx $a1 $a2) (fun (_) (=>) (andThen (equateDim $ctx $r1 $r2) (fun (_) (=>) (andThen (equateDim $ctx $s1 $s2) (fun (_) (=>) (andThen (equateCof $ctx $φ1 $φ2) (fun (_) (=>) (equateNeutral $ctx $u1 $u2)))))))))
      | _ => t

    def equateNeutralLit (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (lit $s) (lit $s)) => (ok)
      | _ => t

    def equateNeutralLitNeq (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx (lit $s1) (lit $s2)) => (fail (concat str "literals differ: " $s1 str " vs " $s2))
      | _ => t

    def equateNeutralOther (t : Term) : Term :=
      match t with
      | (equateNeutral $ctx $t1 $t2) => (fail (concat str "neutral terms not equal: " $t1 str " vs " $t2))
      | _ => t

  end EquateNeutral

  section TopLevel

    def checkTpEq (t : Term) : Term :=
      match t with
      | (checkTpEq $tp1 $tp2) => (equateTp (convCtxEmpty) $tp1 $tp2)
      | _ => t

    def checkEq (t : Term) : Term :=
      match t with
      | (checkEq $tp $t1 $t2) => (equateCon (convCtxEmpty) $tp $t1 $t2)
      | _ => t

    def checkSubtype (t : Term) : Term :=
      match t with
      | (checkSubtype $tp1 $tp2) => (equateTp (convCtxEmpty) $tp1 $tp2)
      | _ => t

  end TopLevel

  section Helpers

    def convResultToBool (t : Term) : Term :=
      match t with
      | (toBool (ok)) => (true)
      | _ => t

    def convResultToBoolFail (t : Term) : Term :=
      match t with
      | (toBool (fail $msg)) => (false)
      | _ => t

    def convResultToBoolBlocked (t : Term) : Term :=
      match t with
      | (toBool (blocked $n)) => (false)
      | _ => t

    def equal (t : Term) : Term :=
      match t with
      | (equal $tp $t1 $t2) => (toBool (checkEq $tp $t1 $t2))
      | _ => t

    def equalTp (t : Term) : Term :=
      match t with
      | (equalTp $tp1 $tp2) => (toBool (checkTpEq $tp1 $tp2))
      | _ => t

  end Helpers

end Conversion