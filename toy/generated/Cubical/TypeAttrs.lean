(DImport import (modulePath Core) ;)

namespace TypeAttrs

  section ASTtoIR

    def astType (t : Term) : Term :=
      match t with
      | (ast (type)) => (univ (num (number 0)))
      | _ => t

    def astTypeLevel (t : Term) : Term :=
      match t with
      | (ast (typeLevel $n)) => (univ $n)
      | _ => t

    def astInterval (t : Term) : Term :=
      match t with
      | (ast (interval)) => (lit str "𝕀")
      | _ => t

    def astLamTyped (t : Term) : Term :=
      match t with
      | (ast (lam (binders (typedBinder $x $A)) $body)) => (lam $x $A (ast $body))
      | _ => t

    def astLamSimple (t : Term) : Term :=
      match t with
      | (ast (lam (binders (simpleBinder $x)) $body)) => (lam $x (hole) (ast $body))
      | _ => t

    def astArrow (t : Term) : Term :=
      match t with
      | (ast (Arrow $A $B)) => (pi str "_" (ast $A) (ast $B))
      | _ => t

    def astPi (t : Term) : Term :=
      match t with
      | (ast (Pi (cell $x $A) $B)) => (pi $x (ast $A) (ast $B))
      | _ => t

    def astApp (t : Term) : Term :=
      match t with
      | (ast (app $f (arg $x))) => (app (ast $f) (ast $x))
      | _ => t

    def astAppNoArg (t : Term) : Term :=
      match t with
      | (ast (app $f)) => (ast $f)
      | _ => t

    def astProd (t : Term) : Term :=
      match t with
      | (ast (Prod $A $B)) => (sigma str "_" (ast $A) (ast $B))
      | _ => t

    def astSigma (t : Term) : Term :=
      match t with
      | (ast (Sigma $x $A $B)) => (sigma $x (ast $A) (ast $B))
      | _ => t

    def astPair (t : Term) : Term :=
      match t with
      | (ast (pair $a $b)) => (pair (ast $a) (ast $b))
      | _ => t

    def astPath (t : Term) : Term :=
      match t with
      | (ast (path $A $a $b)) => (path (ast $A) (ast $a) (ast $b))
      | _ => t

    def astRefl (t : Term) : Term :=
      match t with
      | (ast (refl)) => (refl (hole))
      | _ => t

    def astPathAbs (t : Term) : Term :=
      match t with
      | (ast (pathAbs (dims $i) $body $sys)) => (plam $i (ast $body) (ast $sys))
      | _ => t

    def astPathAbsNoSys (t : Term) : Term :=
      match t with
      | (ast (pathAbs (dims $i) $body)) => (plam $i (ast $body) (sys))
      | _ => t

    def astCoe (t : Term) : Term :=
      match t with
      | (ast (coe $r $r' $A $a)) => (coe (ast $r) (ast $r') (ast $A) (ast $a))
      | _ => t

    def astHcom (t : Term) : Term :=
      match t with
      | (ast (hcom $r $r' $A $cap $sys)) => (hcom (ast $A) (ast $r) (ast $r') (cof_top (ast $sys) (ast $cap)))
      | _ => t

    def astComp (t : Term) : Term :=
      match t with
      | (ast (comp $r $r' $A $cap $sys)) => (com (ast $A) (ast $r) (ast $r') (cof_top (ast $sys) (ast $cap)))
      | _ => t

    def astLet (t : Term) : Term :=
      match t with
      | (ast (let $x $A $v $body)) => (let $x (ast $A) (ast $v) (ast $body))
      | _ => t

    def astProjFst (t : Term) : Term :=
      match t with
      | (ast (proj $e (field str "fst"))) => (fst (ast $e))
      | _ => t

    def astProjSnd (t : Term) : Term :=
      match t with
      | (ast (proj $e (field str "snd"))) => (snd (ast $e))
      | _ => t

    def astCircle (t : Term) : Term :=
      match t with
      | (ast (circle)) => (S1)
      | _ => t

    def astBase (t : Term) : Term :=
      match t with
      | (ast (base)) => (base)
      | _ => t

    def astLoop (t : Term) : Term :=
      match t with
      | (ast (loop $i)) => (loop (ast $i))
      | _ => t

    def astNat (t : Term) : Term :=
      match t with
      | (ast (nat)) => (nat)
      | _ => t

    def astZero (t : Term) : Term :=
      match t with
      | (ast (zero)) => (zero)
      | _ => t

    def astSuc (t : Term) : Term :=
      match t with
      | (ast (suc $n)) => (suc (ast $n))
      | _ => t

    def astVtype (t : Term) : Term :=
      match t with
      | (ast (Vtype $r $A $B $e)) => (vtype (ast $r) (ast $A) (ast $B) (ast $e))
      | _ => t

    def astVin (t : Term) : Term :=
      match t with
      | (ast (Vin $r $a $b)) => (vin (ast $r) (ast $a) (ast $b))
      | _ => t

    def astVproj (t : Term) : Term :=
      match t with
      | (ast (Vproj $r $v $A $B $e)) => (vproj (ast $r) (ast $A) (ast $B) (ast $e) (ast $v))
      | _ => t

    def astGlue (t : Term) : Term :=
      match t with
      | (ast (Glue $A $phi $T $e)) => (glue (ast $A) (ast $phi) (ast $T) (ast $e))
      | _ => t

    def astGlueEl (t : Term) : Term :=
      match t with
      | (ast (glue $t $a)) => (glueEl (ast $t) (ast $a))
      | _ => t

    def astUnglue (t : Term) : Term :=
      match t with
      | (ast (unglue $g)) => (unglue (ast $g))
      | _ => t

    def astDef (t : Term) : Term :=
      match t with
      | (ast (def $name $args $type $body)) => (def $name (ast $args) (ast $type) (ast $body))
      | _ => t

    def astDefInfer (t : Term) : Term :=
      match t with
      | (ast (defInfer $name $args $body)) => (def $name (ast $args) (hole) (ast $body))
      | _ => t

  end ASTtoIR

  section IRtoAST

    def irUniv0 (t : Term) : Term :=
      match t with
      | (unast (univ (num (number 0)))) => (type)
      | _ => t

    def irUnivN (t : Term) : Term :=
      match t with
      | (unast (univ $n)) => (typeLevel $n)
      | _ => t

    def irPiArrow (t : Term) : Term :=
      match t with
      | (unast (pi str "_" $A $B)) => (Arrow (unast $A) (unast $B))
      | _ => t

    def irPiDep (t : Term) : Term :=
      match t with
      | (unast (pi $x $A $B)) => (Pi (cell $x (unast $A)) (unast $B))
      | _ => t

    def irSigmaProd (t : Term) : Term :=
      match t with
      | (unast (sigma str "_" $A $B)) => (Prod (unast $A) (unast $B))
      | _ => t

    def irSigmaDep (t : Term) : Term :=
      match t with
      | (unast (sigma $x $A $B)) => (Sigma $x (unast $A) (unast $B))
      | _ => t

    def irLam (t : Term) : Term :=
      match t with
      | (unast (lam $body)) => (lam (binders (simpleBinder str "_")) (unast $body))
      | _ => t

    def irApp (t : Term) : Term :=
      match t with
      | (unast (app $f $x)) => (app (unast $f) (arg (unast $x)))
      | _ => t

    def irPair (t : Term) : Term :=
      match t with
      | (unast (pair $a $b)) => (pair (unast $a) (unast $b))
      | _ => t

    def irFst (t : Term) : Term :=
      match t with
      | (unast (fst $e)) => (proj (unast $e) (field str "fst"))
      | _ => t

    def irSnd (t : Term) : Term :=
      match t with
      | (unast (snd $e)) => (proj (unast $e) (field str "snd"))
      | _ => t

    def irPlam (t : Term) : Term :=
      match t with
      | (unast (plam $body)) => (pathAbs (dims str "_") (unast $body))
      | _ => t

    def irPapp (t : Term) : Term :=
      match t with
      | (unast (papp $p $i)) => (app (unast $p) (arg (unast $i)))
      | _ => t

    def irNat (t : Term) : Term :=
      match t with
      | (unast (nat)) => (nat)
      | _ => t

    def irZero (t : Term) : Term :=
      match t with
      | (unast (zero)) => (zero)
      | _ => t

    def irSuc (t : Term) : Term :=
      match t with
      | (unast (suc $n)) => (suc (unast $n))
      | _ => t

    def irCircle (t : Term) : Term :=
      match t with
      | (unast (S1)) => (circle)
      | _ => t

    def irBase (t : Term) : Term :=
      match t with
      | (unast (base)) => (base)
      | _ => t

    def irLoop (t : Term) : Term :=
      match t with
      | (unast (loop $i)) => (loop (unast $i))
      | _ => t

    def irDim0 (t : Term) : Term :=
      match t with
      | (unast (dim0)) => (lit str "0")
      | _ => t

    def irDim1 (t : Term) : Term :=
      match t with
      | (unast (dim1)) => (lit str "1")
      | _ => t

    def irDefault (t : Term) : Term :=
      match t with
      | (unast $e) => $e
      | _ => t

  end IRtoAST

  section TypeAttr

    def synTypeUniv (t : Term) : Term :=
      match t with
      | (synType (univ $n) $ctx) => (tacOk (univ (succ $n)))
      | _ => t

    def synTypeNat (t : Term) : Term :=
      match t with
      | (synType (nat) $ctx) => (tacOk (univ (num (number 0))))
      | _ => t

    def synTypeCircle (t : Term) : Term :=
      match t with
      | (synType (S1) $ctx) => (tacOk (univ (num (number 0))))
      | _ => t

    def synTypeVar (t : Term) : Term :=
      match t with
      | (synType (ix $n) $ctx) => (tpCtxLookup $ctx $n)
      | _ => t

    def synTypePi (t : Term) : Term :=
      match t with
      | (synType (pi $dom $cod) $ctx) => (tacResultBind (synType $dom $ctx) (lam (letIn ( let $ l1 = (univLevel (ix (num (number 0)))) in (tacResultBind (synType $cod (tpCtxExtend $ctx $dom)) (lam (letIn ( let $ l2 = (univLevel (ix (num (number 0)))) in (tacOk (univ (max $l1 $l2))) )))) ))))
      | _ => t

    def synTypeSigma (t : Term) : Term :=
      match t with
      | (synType (sigma $base $fam) $ctx) => (tacResultBind (synType $base $ctx) (lam (letIn ( let $ l1 = (univLevel (ix (num (number 0)))) in (tacResultBind (synType $fam (tpCtxExtend $ctx $base)) (lam (letIn ( let $ l2 = (univLevel (ix (num (number 0)))) in (tacOk (univ (max $l1 $l2))) )))) ))))
      | _ => t

    def synTypeLam (t : Term) : Term :=
      match t with
      | (synType (lam $body) $ctx) => (tacError str "cannot synthesize type of lambda")
      | _ => t

    def synTypeApp (t : Term) : Term :=
      match t with
      | (synType (app $f $x) $ctx) => (tacResultBind (synType $f $ctx) (lam (caseExpr ( case (ix (num (number 0))) (arm ( pi $dom $cod ) => (tacOk (subst (num (number 0)) $x $cod))) (arm _ => (tacError str "expected function type")) ))))
      | _ => t

    def synTypeFst (t : Term) : Term :=
      match t with
      | (synType (fst $e) $ctx) => (tacResultBind (synType $e $ctx) (lam (caseExpr ( case (ix (num (number 0))) (arm ( sigma $base $fam ) => (tacOk $base)) (arm _ => (tacError str "expected sigma type")) ))))
      | _ => t

    def synTypeSnd (t : Term) : Term :=
      match t with
      | (synType (snd $e) $ctx) => (tacResultBind (synType $e $ctx) (lam (caseExpr ( case (ix (num (number 0))) (arm ( sigma $base $fam ) => (tacOk (subst (num (number 0)) (fst $e) $fam))) (arm _ => (tacError str "expected sigma type")) ))))
      | _ => t

    def synTypeZero (t : Term) : Term :=
      match t with
      | (synType (zero) $ctx) => (tacOk (nat))
      | _ => t

    def synTypeSuc (t : Term) : Term :=
      match t with
      | (synType (suc $n) $ctx) => (tacResultBind (synType $n $ctx) (lam (caseExpr ( case (ix (num (number 0))) (arm nat => (tacOk (nat))) (arm _ => (tacError str "expected nat")) ))))
      | _ => t

    def synTypeBase (t : Term) : Term :=
      match t with
      | (synType (base) $ctx) => (tacOk (S1))
      | _ => t

    def synTypeLoop (t : Term) : Term :=
      match t with
      | (synType (loop $i) $ctx) => (tacOk (S1))
      | _ => t

    def univLevel (t : Term) : Term :=
      match t with
      | (univLevel (univ $n)) => $n
      | _ => t

    def univLevelDefault (t : Term) : Term :=
      match t with
      | (univLevel $e) => (num (number 0))
      | _ => t

  end TypeAttr

  section CtxAttr

    def inhCtxLam (t : Term) : Term :=
      match t with
      | (inhCtx (lam $body) (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs)) $expectedTy) => (caseExpr ( case $expectedTy (arm ( pi $dom $cod ) => (inhCtx $body (tpCtx (labeledArg types : ($dom $ts)) (labeledArg cofs : $cs)) $cod)) (arm _ => (tacError str "expected pi type for lambda")) ))
      | _ => t

    def inhCtxPlam (t : Term) : Term :=
      match t with
      | (inhCtx (plam $body) (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs)) $expectedTy) => (inhCtx $body (tpCtx (labeledArg types : ((( (lit) str "𝕀" )) $ts)) (labeledArg cofs : $cs)) $expectedTy)
      | _ => t

    def inhCtxPair (t : Term) : Term :=
      match t with
      | (inhCtx (pair $a $b) $ctx $expectedTy) => (caseExpr ( case $expectedTy (arm ( sigma $base $fam ) => (letIn ( let $ ctxA = (inhCtx $a $ctx $base) in (letIn ( let $ famSubst = (subst (num (number 0)) $a $fam) in (inhCtx $b $ctx $famSubst) )) ))) (arm _ => (tacError str "expected sigma type for pair")) ))
      | _ => t

  end CtxAttr

  section ElabAttr

    def elabTerm (t : Term) : Term :=
      match t with
      | (elab $term $ctx) => (tacResultBind (synType $term $ctx) (lam (tacOk (tuple ( $term , (ix (num (number 0))) )))))
      | _ => t

    def elabCheck (t : Term) : Term :=
      match t with
      | (elabCheck $term $ctx $expectedTy) => (tacOk $term)
      | _ => t

    def elabInfer (t : Term) : Term :=
      match t with
      | (elabInfer $term $ctx) => (synType $term $ctx)
      | _ => t

  end ElabAttr

  section BiDirect

    def biCheck (t : Term) : Term :=
      match t with
      | (biCheck $term $ctx $expectedTy) => (tacResultBind (synType $term $ctx) (lam (if (conv (ix (num (number 0))) $expectedTy) (then (tacOk $term) else) (tacError str "type mismatch"))))
      | _ => t

    def biInfer (t : Term) : Term :=
      match t with
      | (biInfer $term $ctx) => (tacResultBind (synType $term $ctx) (lam (tacOk (tuple ( $term , (ix (num (number 0))) )))))
      | _ => t

    def biSynth (t : Term) : Term :=
      match t with
      | (biSynth (lam $body) $ctx) => (tacError str "cannot synthesize lambda")
      | _ => t

    def biSynthApp (t : Term) : Term :=
      match t with
      | (biSynth (app $f $x) $ctx) => (tacResultBind (biInfer $f $ctx) (lam (caseExpr ( case (snd (ix (num (number 0)))) (arm ( pi $dom $cod ) => (tacResultBind (biCheck $x $ctx $dom) (lam (tacOk (tuple ( (app (fst (ix (num (number 1)))) (ix (num (number 0)))) , (subst (num (number 0)) $x $cod) )))))) (arm _ => (tacError str "expected function type")) ))))
      | _ => t

  end BiDirect

end TypeAttrs