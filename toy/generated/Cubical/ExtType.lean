(DImport import (modulePath Core) ;)

namespace ExtType

  section ExtInfo

    def extInfo : Parser :=
      (annotated str "extInfo" str "arity:" (special <number>) str "family:" (special <expr>) str "cof:" (special <expr>) str "boundary:" (special <expr>) → extInfo)

    def extInfoArity (t : Term) : Term :=
      match t with
      | (extInfoArity (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => $n
      | _ => t

    def extInfoFamily (t : Term) : Term :=
      match t with
      | (extInfoFamily (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => $f
      | _ => t

    def extInfoCof (t : Term) : Term :=
      match t with
      | (extInfoCof (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => $c
      | _ => t

    def extInfoBoundary (t : Term) : Term :=
      match t with
      | (extInfoBoundary (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => $b
      | _ => t

    def extInfoFromExpr (t : Term) : Term :=
      match t with
      | (extInfoFromExpr (ext $n $fam $cof $bdry)) => (some (extInfo (labeledArg arity : $n) (labeledArg family : $fam) (labeledArg cof : $cof) (labeledArg boundary : $bdry)))
      | _ => t

    def extInfoFromExprOther (t : Term) : Term :=
      match t with
      | (extInfoFromExpr $e) => (none)
      | _ => t

    def extInfoToExpr (t : Term) : Term :=
      match t with
      | (extInfoToExpr (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => (ext $n $f $c $b)
      | _ => t

    def extInfoIsNullary (t : Term) : Term :=
      match t with
      | (extInfoIsNullary (extInfo (labeledArg arity : (num (number 0))) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => (true)
      | _ => t

    def extInfoIsNullaryN (t : Term) : Term :=
      match t with
      | (extInfoIsNullary (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => (false)
      | _ => t

    def extInfoHasTrivialBoundary (t : Term) : Term :=
      match t with
      | (extInfoHasTrivialBoundary (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : (cof_bot)) (labeledArg boundary : $b))) => (true)
      | _ => t

    def extInfoHasTrivialBoundaryOther (t : Term) : Term :=
      match t with
      | (extInfoHasTrivialBoundary (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b))) => (false)
      | _ => t

  end ExtInfo

  section ApplyDims

    def applyFamily (t : Term) : Term :=
      match t with
      | (applyFamily (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b)) $dims) => (caseExpr ( case (eq (length $dims) $n) (arm true => (foldr (fun (dim) (acc) (=>) (subst (num (number 0)) (dim) (acc))) $f $dims)) (arm false => $f) ))
      | _ => t

    def applyCof (t : Term) : Term :=
      match t with
      | (applyCof (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b)) $dims) => (caseExpr ( case (eq (length $dims) $n) (arm true => (foldr (fun (dim) (acc) (=>) (subst (num (number 0)) (dim) (acc))) $c $dims)) (arm false => $c) ))
      | _ => t

    def applyBoundary (t : Term) : Term :=
      match t with
      | (applyBoundary (extInfo (labeledArg arity : $n) (labeledArg family : $f) (labeledArg cof : $c) (labeledArg boundary : $b)) $dims) => (caseExpr ( case (eq (length $dims) $n) (arm true => (foldr (fun (dim) (acc) (=>) (subst (num (number 0)) (dim) (acc))) $b $dims)) (arm false => $b) ))
      | _ => t

  end ApplyDims

  section MkExt

    def mkExt (t : Term) : Term :=
      match t with
      | (mkExt $arity $fam $cof $bdry) => (caseExpr ( case $cof (arm cof_bot => (ext $arity $fam (cof_bot) $bdry)) (arm cof_top => (ext $arity $fam (cof_top) $bdry)) (arm _ => (ext $arity $fam $cof $bdry)) ))
      | _ => t

  end MkExt

  section MkExtLam

    def mkExtLam (t : Term) : Term :=
      match t with
      | (mkExtLam $arity $body) => (extLam $arity $body)
      | _ => t

  end MkExtLam

  section MkExtApp

    def mkExtApp (t : Term) : Term :=
      match t with
      | (mkExtApp (extLam $n $body) $dims) => (caseExpr ( case (eq (length $dims) $n) (arm true => (foldr (fun (dim) (acc) (=>) (subst (num (number 0)) (dim) (acc))) $body $dims)) (arm false => (extApp (extLam $n $body) $dims)) ))
      | _ => t

    def mkExtAppOther (t : Term) : Term :=
      match t with
      | (mkExtApp $e $dims) => (extApp $e $dims)
      | _ => t

  end MkExtApp

  section ReduceExt

    def reduceExtExpr (t : Term) : Term :=
      match t with
      | (reduceExtExpr (extApp (extLam $n $body) $dims)) => (caseExpr ( case (eq (length $dims) $n) (arm true => (some (foldr (fun (dim) (acc) (=>) (subst (num (number 0)) (dim) (acc))) $body $dims))) (arm false => (none)) ))
      | _ => t

    def reduceExtExprOther (t : Term) : Term :=
      match t with
      | (reduceExtExpr $e) => (none)
      | _ => t

    def normalizeExt (t : Term) : Term :=
      match t with
      | (normalizeExt $fuel $e) => (normalizeExt' $fuel $e)
      | _ => t

    def normalizeExt'0 (t : Term) : Term :=
      match t with
      | (normalizeExt' (num (number 0)) $e) => $e
      | _ => t

    def normalizeExt' (t : Term) : Term :=
      match t with
      | (normalizeExt' (suc $fuel) $e) => (caseExpr ( case (reduceExtExpr $e) (arm ( some $e' ) => (normalizeExt' $fuel $e')) (arm none => $e) ))
      | _ => t

  end ReduceExt

  section PathAsExt

    def pathToExt (t : Term) : Term :=
      match t with
      | (pathToExt (path $A $a $b)) => (ext (num (number 1)) (lam $A) (cof_or (cof_eq (ix (num (number 0))) (dim0)) (cof_eq (ix (num (number 0))) (dim1))) (lam (caseExpr ( case (ix (num (number 0))) (arm dim0 => (shift (num (number 0)) (num (number 1)) $a)) (arm dim1 => (shift (num (number 0)) (num (number 1)) $b)) ))))
      | _ => t

    def extToPath (t : Term) : Term :=
      match t with
      | (extToPath (ext (num (number 1)) (lam $A) $cof $bdry)) => (some (path $A (evalAtDim0 $bdry) (evalAtDim1 $bdry)))
      | _ => t

    def extToPathOther (t : Term) : Term :=
      match t with
      | (extToPath $e) => (none)
      | _ => t

    def evalAtDim0 (t : Term) : Term :=
      match t with
      | (evalAtDim0 (lam $body)) => (subst (num (number 0)) (dim0) $body)
      | _ => t

    def evalAtDim1 (t : Term) : Term :=
      match t with
      | (evalAtDim1 (lam $body)) => (subst (num (number 0)) (dim1) $body)
      | _ => t

  end PathAsExt

  section HComExt

    def hcomExt (t : Term) : Term :=
      match t with
      | (hcomExt $r $r' (ext $n $fam $cof $bdry) $φ $tubes $cap) => (extLam $n (hcom (mkExtApp $fam (dimVarsN $n)) $r $r' (cof_or $φ (mkExtApp $cof (dimVarsN $n))) (lam (lam (caseExpr ( case (meetsCof (ix (num (number 1))) $φ) (arm true => (mkExtApp (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0)))) (dimVarsN $n))) (arm false => (mkExtApp (shift (num (number 0)) (num (number 2)) $bdry) (dimVarsN $n))) )))) (mkExtApp $cap (dimVarsN $n))))
      | _ => t

    def dimVarsN (t : Term) : Term :=
      match t with
      | (dimVarsN $n) => (dimVarsN' $n (unit ( )))
      | _ => t

    def dimVarsN'0 (t : Term) : Term :=
      match t with
      | (dimVarsN' (num (number 0)) $acc) => $acc
      | _ => t

    def dimVarsN' (t : Term) : Term :=
      match t with
      | (dimVarsN' (suc $n) $acc) => (dimVarsN' $n ((( (ix) $n )) $acc))
      | _ => t

  end HComExt

  section CoeExt

    def coeExt (t : Term) : Term :=
      match t with
      | (coeExt $r $r' (lam (ext $n $fam $cof $bdry)) $e) => (extLam $n (com (lam (mkExtApp $fam (dimVarsN $n))) $r $r' (mkExtApp $cof (dimVarsN $n)) (lam (lam (mkExtApp (shift (num (number 0)) (num (number 2)) $bdry) (dimVarsN $n)))) (mkExtApp $e (dimVarsN $n))))
      | _ => t

  end CoeExt

  section ExtCurry

    def extCurry (t : Term) : Term :=
      match t with
      | (extCurry $n $m $e) => (extLam $n (extLam $m (mkExtApp $e (append (dimVarsN $n) (dimVarsN $m)))))
      | _ => t

    def extUncurry (t : Term) : Term :=
      match t with
      | (extUncurry $n $m $e) => (extLam (plus $n $m) (mkExtApp (mkExtApp $e (takeN $n (dimVarsN (plus $n $m)))) (dropN $n (dimVarsN (plus $n $m)))))
      | _ => t

  end ExtCurry

  section ExtRestrict

    def extRestrict (t : Term) : Term :=
      match t with
      | (extRestrict (ext $n $fam $cof $bdry) $dim $val) => (ext (minus $n (num (number 1))) (lam (subst $dim $val $fam)) (subst $dim $val $cof) (lam (subst $dim $val $bdry)))
      | _ => t

  end ExtRestrict

end ExtType