(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

(DImport import (modulePath TermBuilder) ;)

(DImport import (modulePath Visitor) ;)

namespace Semantics

  section EvalCtx

    def evalCtx : Parser :=
      (annotated str "evalCtx" str "env:" many ((special <expr>)) str "fuel:" (special <number>) → evalCtx)

    def evalCtxEmpty (t : Term) : Term :=
      match t with
      | (evalCtxEmpty) => (evalCtx (labeledArg env : (unit ( ))) (labeledArg fuel : (num (number 1000))))
      | _ => t

    def evalCtxExtend (t : Term) : Term :=
      match t with
      | (evalCtxExtend (evalCtx (labeledArg env : $env) (labeledArg fuel : $f)) $v) => (evalCtx (labeledArg env : ($env $v)) (labeledArg fuel : $f))
      | _ => t

    def evalCtxLookup (t : Term) : Term :=
      match t with
      | (evalCtxLookup (evalCtx (labeledArg env : $env) (labeledArg fuel : $f)) $ix) => (lookupAt $env (minus (length $env) (num (number 1)) $ix))
      | _ => t

    def evalCtxDecFuel (t : Term) : Term :=
      match t with
      | (evalCtxDecFuel (evalCtx (labeledArg env : $env) (labeledArg fuel : (suc $f)))) => (evalCtx (labeledArg env : $env) (labeledArg fuel : $f))
      | _ => t

    def evalCtxDecFuel0 (t : Term) : Term :=
      match t with
      | (evalCtxDecFuel (evalCtx (labeledArg env : $env) (labeledArg fuel : (num (number 0))))) => (evalCtx (labeledArg env : $env) (labeledArg fuel : (num (number 0))))
      | _ => t

  end EvalCtx

  section DispatchResult

    def dispatchDone : Parser :=
      (annotated str "done" → dispatchResult)

    def dispatchReduce : Parser :=
      (annotated str "reduce" → dispatchResult)

  end DispatchResult

  section StableCode

    def isStablePi (t : Term) : Term :=
      match t with
      | (isStableCode (pi $A $B)) => (true)
      | _ => t

    def isStableSigma (t : Term) : Term :=
      match t with
      | (isStableCode (sigma $A $B)) => (true)
      | _ => t

    def isStablePath (t : Term) : Term :=
      match t with
      | (isStableCode (path $A $l $r)) => (true)
      | _ => t

    def isStableNat (t : Term) : Term :=
      match t with
      | (isStableCode (nat)) => (true)
      | _ => t

    def isStableCircle (t : Term) : Term :=
      match t with
      | (isStableCode (circle)) => (true)
      | _ => t

    def isStableUniv (t : Term) : Term :=
      match t with
      | (isStableCode (univ $l)) => (true)
      | _ => t

    def isStableSub (t : Term) : Term :=
      match t with
      | (isStableCode (sub $A $φ $a)) => (true)
      | _ => t

    def isStableOther (t : Term) : Term :=
      match t with
      | (isStableCode $other) => (false)
      | _ => t

    def isVCode (t : Term) : Term :=
      match t with
      | (isVCode (vtype $r $A $B $equiv)) => (true)
      | _ => t

    def isVCodeOther (t : Term) : Term :=
      match t with
      | (isVCode $other) => (false)
      | _ => t

    def isHComCode (t : Term) : Term :=
      match t with
      | (isHComCode (hcom $r $s $A $φ $u)) => (true)
      | _ => t

    def isHComCodeOther (t : Term) : Term :=
      match t with
      | (isHComCode $other) => (false)
      | _ => t

  end StableCode

  section DimEq

    def dimEq00 (t : Term) : Term :=
      match t with
      | (dimEq (dim0) (dim0)) => (true)
      | _ => t

    def dimEq11 (t : Term) : Term :=
      match t with
      | (dimEq (dim1) (dim1)) => (true)
      | _ => t

    def dimEqIx (t : Term) : Term :=
      match t with
      | (dimEq (ix $n) (ix $n)) => (true)
      | _ => t

    def dimEqOther (t : Term) : Term :=
      match t with
      | (dimEq $r $s) => (false)
      | _ => t

  end DimEq

  section CofTrue

    def cofTrueTop (t : Term) : Term :=
      match t with
      | (cofTrue (cof_top)) => (true)
      | _ => t

    def cofTrueEq (t : Term) : Term :=
      match t with
      | (cofTrue (cof_eq $r $s)) => (dimEq $r $s)
      | _ => t

    def cofTrueOrL (t : Term) : Term :=
      match t with
      | (cofTrue (cof_or $φ $ψ)) => (or (cofTrue $φ) (cofTrue $ψ))
      | _ => t

    def cofTrueOther (t : Term) : Term :=
      match t with
      | (cofTrue $φ) => (false)
      | _ => t

  end CofTrue

  section Eval

    def evalNoFuel (t : Term) : Term :=
      match t with
      | (eval (evalCtx (labeledArg env : $env) (labeledArg fuel : (num (number 0)))) $e) => $e
      | _ => t

    def evalIx (t : Term) : Term :=
      match t with
      | (eval $ctx (ix $n)) => (caseExpr ( case (evalCtxLookup $ctx $n) (arm ( some $v ) => (eval (evalCtxDecFuel $ctx) $v)) (arm none => (ix $n)) ))
      | _ => t

    def evalLam (t : Term) : Term :=
      match t with
      | (eval $ctx (lam $body)) => (lam $body)
      | _ => t

    def evalApp (t : Term) : Term :=
      match t with
      | (eval $ctx (app (lam $body) $arg)) => (eval (evalCtxDecFuel $ctx) (subst (num (number 0)) (eval (evalCtxDecFuel $ctx) $arg) $body))
      | _ => t

    def evalAppNeutral (t : Term) : Term :=
      match t with
      | (eval $ctx (app $f $arg)) => (app (eval (evalCtxDecFuel $ctx) $f) (eval (evalCtxDecFuel $ctx) $arg))
      | _ => t

    def evalPair (t : Term) : Term :=
      match t with
      | (eval $ctx (pair $a $b)) => (pair (eval (evalCtxDecFuel $ctx) $a) (eval (evalCtxDecFuel $ctx) $b))
      | _ => t

    def evalFst (t : Term) : Term :=
      match t with
      | (eval $ctx (fst (pair $a $b))) => (eval (evalCtxDecFuel $ctx) $a)
      | _ => t

    def evalFstNeutral (t : Term) : Term :=
      match t with
      | (eval $ctx (fst $p)) => (fst (eval (evalCtxDecFuel $ctx) $p))
      | _ => t

    def evalSnd (t : Term) : Term :=
      match t with
      | (eval $ctx (snd (pair $a $b))) => (eval (evalCtxDecFuel $ctx) $b)
      | _ => t

    def evalSndNeutral (t : Term) : Term :=
      match t with
      | (eval $ctx (snd $p)) => (snd (eval (evalCtxDecFuel $ctx) $p))
      | _ => t

    def evalPlam (t : Term) : Term :=
      match t with
      | (eval $ctx (plam $body)) => (plam $body)
      | _ => t

    def evalPapp (t : Term) : Term :=
      match t with
      | (eval $ctx (papp (plam $body) $r)) => (eval (evalCtxDecFuel $ctx) (dimSubst (num (number 0)) $r $body))
      | _ => t

    def evalPappNeutral (t : Term) : Term :=
      match t with
      | (eval $ctx (papp $p $r)) => (papp (eval (evalCtxDecFuel $ctx) $p) $r)
      | _ => t

    def evalCoe (t : Term) : Term :=
      match t with
      | (eval $ctx (coe $line $r $s $t)) => (caseExpr ( case (dimEq $r $s) (arm true => (eval (evalCtxDecFuel $ctx) $t)) (arm false => (doRigidCoe (evalCtxDecFuel $ctx) (eval (evalCtxDecFuel $ctx) $line) $r $s (eval (evalCtxDecFuel $ctx) $t))) ))
      | _ => t

    def evalHCom (t : Term) : Term :=
      match t with
      | (eval $ctx (hcom $A $r $s $φ $u)) => (caseExpr ( case (or (dimEq $r $s) (cofTrue $φ)) (arm true => (eval (evalCtxDecFuel $ctx) (app (app $u $s) (prf)))) (arm false => (doRigidHCom (evalCtxDecFuel $ctx) (eval (evalCtxDecFuel $ctx) $A) $r $s $φ (eval (evalCtxDecFuel $ctx) $u))) ))
      | _ => t

  end Eval

  section RigidCoe

    def doRigidCoeNat (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (nat)) $r $s $con) => $con
      | _ => t

    def doRigidCoeCircle (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (circle)) $r $s $con) => $con
      | _ => t

    def doRigidCoeUniv (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (univ $l)) $r $s $con) => $con
      | _ => t

    def doRigidCoePi (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (pi $A $B)) $r $s $f) => (lam (coe (lam (app (shift (num (number 0)) (num (number 1)) $B) (coe (lam $A) $s (ix (num (number 0))) (ix (num (number 0)))))) $r $s (app $f (coe (lam $A) $s $r (ix (num (number 0)))))))
      | _ => t

    def doRigidCoeSigma (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (sigma $A $B)) $r $s (pair $a $b)) => (pair (coe (lam $A) $r $s $a) (coe (lam (app (shift (num (number 0)) (num (number 1)) $B) (coe (lam $A) $r (ix (num (number 0))) (shift (num (number 0)) (num (number 1)) $a)))) $r $s $b))
      | _ => t

    def doRigidCoePath (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx (lam (path $A $l $r)) $r' $s' $p) => (plam (com (lam $A) $r' $s' (cof_or (cof_eq (ix (num (number 0))) (dim0)) (cof_eq (ix (num (number 0))) (dim1))) (lam (lam (caseExpr ( case (ix (num (number 1))) (arm dim0 => $l) (arm dim1 => $r) )))) (papp $p (ix (num (number 0))))))
      | _ => t

    def doRigidCoeDefault (t : Term) : Term :=
      match t with
      | (doRigidCoe $ctx $line $r $s $con) => (coe $line $r $s $con)
      | _ => t

  end RigidCoe

  section RigidHCom

    def doRigidHComPi (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (pi $A $B) $r $s $φ $u) => (lam (hcom (app (shift (num (number 0)) (num (number 1)) $B) (ix (num (number 0)))) $r $s $φ (lam (lam (app (app (app (shift (num (number 0)) (num (number 2)) $u) (ix (num (number 1)))) (ix (num (number 0)))) (ix (num (number 2))))))))
      | _ => t

    def doRigidHComSigma (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (sigma $A $B) $r $s $φ $u) => (pair (hcom $A $r $s $φ (lam (lam (fst (app (app (shift (num (number 0)) (num (number 2)) $u) (ix (num (number 1)))) (ix (num (number 0)))))))) (com (lam (app (shift (num (number 0)) (num (number 1)) $B) (hcom $A $r (ix (num (number 0))) $φ (lam (lam (fst (app (app (shift (num (number 0)) (num (number 2)) $u) (ix (num (number 1)))) (ix (num (number 0)))))))))) $r $s $φ (lam (lam (snd (app (app (shift (num (number 0)) (num (number 2)) $u) (ix (num (number 1)))) (ix (num (number 0))))))) (snd (app (app $u $r) (prf)))))
      | _ => t

    def doRigidHComPath (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (path $A $l $ep) $r $s $φ $u) => (plam (hcom $A $r $s (cof_or $φ (cof_or (cof_eq (ix (num (number 0))) (dim0)) (cof_eq (ix (num (number 0))) (dim1)))) (lam (lam (caseExpr ( case (meetsCof (ix (num (number 1))) $φ) (arm true => (papp (app (app (shift (num (number 0)) (num (number 2)) $u) (ix (num (number 1)))) (ix (num (number 0)))) (ix (num (number 2))))) (arm false => (caseExpr ( case (ix (num (number 2))) (arm dim0 => $l) (arm dim1 => $ep) ))) ))))))
      | _ => t

    def doRigidHComNat (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (nat) $r $s $φ $u) => (hcom (nat) $r $s $φ $u)
      | _ => t

    def doRigidHComCircle (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (circle) $r $s $φ $u) => (hcom (circle) $r $s $φ $u)
      | _ => t

    def doRigidHComUniv (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx (univ $l) $r $s $φ $u) => (hcom (univ $l) $r $s $φ $u)
      | _ => t

    def doRigidHComDefault (t : Term) : Term :=
      match t with
      | (doRigidHCom $ctx $code $r $s $φ $u) => (hcom $code $r $s $φ $u)
      | _ => t

  end RigidHCom

  section SpliceCtx

    def spliceCtx : Parser :=
      (annotated str "spliceCtx" many ((special <binding>)) str "level:" (special <number>) → spliceCtx)

    def binding : Parser :=
      (annotated str "(" (special <symbol>) str "," (special <expr>) str ")" → binding)

    def spliceCtxEmpty (t : Term) : Term :=
      match t with
      | (spliceCtxEmpty) => (spliceCtx (unit ( )) (labeledArg level : (num (number 0))))
      | _ => t

    def spliceCtxBind (t : Term) : Term :=
      match t with
      | (spliceCtxBind (spliceCtx $bindings (labeledArg level : $l)) $name $v) => (record ( result : (spliceCtx ($bindings (tuple ( $name , $v ))) (labeledArg level : (suc $l))) (labeledArg var : (ix $l)) ))
      | _ => t

  end SpliceCtx

  section SpliceDim

    def spliceDim0 (t : Term) : Term :=
      match t with
      | (spliceDim $ctx (dim0) $k) => ($k $ctx (dim0))
      | _ => t

    def spliceDim1 (t : Term) : Term :=
      match t with
      | (spliceDim $ctx (dim1) $k) => ($k $ctx (dim1))
      | _ => t

    def spliceDimVar (t : Term) : Term :=
      match t with
      | (spliceDim $ctx $d $k) => (caseExpr ( case (spliceCtxBind $ctx str "i" $d) (arm ( result (:) $ctx' (labeledArg var : $var) ) => ($k $ctx' $var)) ))
      | _ => t

  end SpliceDim

  section SpliceCof

    def spliceCofTop (t : Term) : Term :=
      match t with
      | (spliceCof $ctx (cof_top) $k) => ($k $ctx (cof_top))
      | _ => t

    def spliceCofBot (t : Term) : Term :=
      match t with
      | (spliceCof $ctx (cof_bot) $k) => ($k $ctx (cof_bot))
      | _ => t

    def spliceCofVar (t : Term) : Term :=
      match t with
      | (spliceCof $ctx $φ $k) => (caseExpr ( case (spliceCtxBind $ctx str "φ" $φ) (arm ( result (:) $ctx' (labeledArg var : $var) ) => ($k $ctx' $var)) ))
      | _ => t

  end SpliceCof

  section SpliceCon

    def spliceCon (t : Term) : Term :=
      match t with
      | (spliceCon $ctx $con $k) => (caseExpr ( case (spliceCtxBind $ctx str "x" $con) (arm ( result (:) $ctx' (labeledArg var : $var) ) => ($k $ctx' $var)) ))
      | _ => t

  end SpliceCon

  section DoOps

    def doAp (t : Term) : Term :=
      match t with
      | (doAp $ctx $f $a) => (eval $ctx (app $f $a))
      | _ => t

    def doAp2 (t : Term) : Term :=
      match t with
      | (doAp2 $ctx $f $a $b) => (doAp $ctx (doAp $ctx $f $a) $b)
      | _ => t

    def doFst (t : Term) : Term :=
      match t with
      | (doFst $ctx $p) => (eval $ctx (fst $p))
      | _ => t

    def doSnd (t : Term) : Term :=
      match t with
      | (doSnd $ctx $p) => (eval $ctx (snd $p))
      | _ => t

    def doPApp (t : Term) : Term :=
      match t with
      | (doPApp $ctx $p $r) => (eval $ctx (papp $p $r))
      | _ => t

    def doSubOut (t : Term) : Term :=
      match t with
      | (doSubOut $ctx $t) => (eval $ctx (subOut $t))
      | _ => t

  end DoOps

  section El

    def doElNat (t : Term) : Term :=
      match t with
      | (doEl $ctx (lit str "nat-code")) => (nat)
      | _ => t

    def doElCircle (t : Term) : Term :=
      match t with
      | (doEl $ctx (lit str "circle-code")) => (circle)
      | _ => t

    def doElDefault (t : Term) : Term :=
      match t with
      | (doEl $ctx $code) => (eval $ctx $code)
      | _ => t

  end El

  section RigidCap

    def doRigidCap (t : Term) : Term :=
      match t with
      | (doRigidCap $ctx $r $s $φ $code $box) => (lit (concat str "cap(" $r str "," $s str "," $φ str "," $code str "," (eval $ctx $box) str ")"))
      | _ => t

  end RigidCap

  section RigidVProj

    def doRigidVProjVIn (t : Term) : Term :=
      match t with
      | (doRigidVProj $ctx $r $pcode $code $pequiv (vin $r' $a $base)) => $base
      | _ => t

    def doRigidVProjDefault (t : Term) : Term :=
      match t with
      | (doRigidVProj $ctx $r $pcode $code $pequiv $v) => (vproj $r $pcode $code $pequiv (eval $ctx $v))
      | _ => t

  end RigidVProj

  section TopLevel

    def evaluate (t : Term) : Term :=
      match t with
      | (evaluate $e) => (eval (evalCtxEmpty) $e)
      | _ => t

    def whnf (t : Term) : Term :=
      match t with
      | (whnf $e) => (eval (evalCtxEmpty) $e)
      | _ => t

    def whnfTp (t : Term) : Term :=
      match t with
      | (whnfTp $tp) => (whnf $tp)
      | _ => t

  end TopLevel

  section Instantiation

    def instClo (t : Term) : Term :=
      match t with
      | (instClo $ctx $body $v) => (eval $ctx (subst (num (number 0)) $v $body))
      | _ => t

    def instTpClo (t : Term) : Term :=
      match t with
      | (instTpClo $ctx $body $v) => (instClo $ctx $body $v)
      | _ => t

  end Instantiation

end Semantics