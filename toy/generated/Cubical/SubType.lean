(DImport import (modulePath Core) ;)

namespace SubType

  section SubInfo

    def subInfo : Parser :=
      (annotated str "subInfo" str "base:" (special <expr>) str "cof:" (special <expr>) str "bdry:" (special <expr>) → subInfo)

    def subInfoBase (t : Term) : Term :=
      match t with
      | (subInfoBase (subInfo (labeledArg base : $b) (labeledArg cof : $c) (labeledArg bdry : $d))) => $b
      | _ => t

    def subInfoCof (t : Term) : Term :=
      match t with
      | (subInfoCof (subInfo (labeledArg base : $b) (labeledArg cof : $c) (labeledArg bdry : $d))) => $c
      | _ => t

    def subInfoBdry (t : Term) : Term :=
      match t with
      | (subInfoBdry (subInfo (labeledArg base : $b) (labeledArg cof : $c) (labeledArg bdry : $d))) => $d
      | _ => t

    def subInfoFromExpr (t : Term) : Term :=
      match t with
      | (subInfoFromExpr (sub $ty $cof $bdry)) => (some (subInfo (labeledArg base : $ty) (labeledArg cof : $cof) (labeledArg bdry : $bdry)))
      | _ => t

    def subInfoFromExprOther (t : Term) : Term :=
      match t with
      | (subInfoFromExpr $e) => (none)
      | _ => t

    def subInfoToExpr (t : Term) : Term :=
      match t with
      | (subInfoToExpr (subInfo (labeledArg base : $b) (labeledArg cof : $c) (labeledArg bdry : $d))) => (sub $b $c $d)
      | _ => t

    def subInfoIsTrivial (t : Term) : Term :=
      match t with
      | (subInfoIsTrivial (subInfo (labeledArg base : $b) (labeledArg cof : (cof_top)) (labeledArg bdry : $d))) => (true)
      | _ => t

    def subInfoIsTrivialOther (t : Term) : Term :=
      match t with
      | (subInfoIsTrivial $info) => (false)
      | _ => t

    def subInfoIsImpossible (t : Term) : Term :=
      match t with
      | (subInfoIsImpossible (subInfo (labeledArg base : $b) (labeledArg cof : (cof_bot)) (labeledArg bdry : $d))) => (true)
      | _ => t

    def subInfoIsImpossibleOther (t : Term) : Term :=
      match t with
      | (subInfoIsImpossible $info) => (false)
      | _ => t

    def subInfoGetBase (t : Term) : Term :=
      match t with
      | (subInfoGetBase $info) => (subInfoBase $info)
      | _ => t

    def subInfoEvalBoundary (t : Term) : Term :=
      match t with
      | (subInfoEvalBoundary (subInfo (labeledArg base : $b) (labeledArg cof : $c) (labeledArg bdry : $d)) $prf) => (subst (num (number 0)) $prf $d)
      | _ => t

  end SubInfo

  section MkSub

    def mkSub (t : Term) : Term :=
      match t with
      | (mkSub $baseType $cof $boundary) => (sub $baseType $cof $boundary)
      | _ => t

    def mkSubTrivial (t : Term) : Term :=
      match t with
      | (mkSubTrivial $baseType (lam (ix (num (number 0))))) => $baseType
      | _ => t

    def mkSubTrivialOther (t : Term) : Term :=
      match t with
      | (mkSubTrivial $baseType $boundary) => (sub $baseType (cof_top) $boundary)
      | _ => t

  end MkSub

  section MkSubIn

    def mkSubIn (t : Term) : Term :=
      match t with
      | (mkSubIn $e) => (subIn $e)
      | _ => t

    def mkSubInOut (t : Term) : Term :=
      match t with
      | (mkSubInOut (subOut $e)) => $e
      | _ => t

    def mkSubInOutOther (t : Term) : Term :=
      match t with
      | (mkSubInOutOther $e) => (subIn $e)
      | _ => t

  end MkSubIn

  section MkSubOut

    def mkSubOut (t : Term) : Term :=
      match t with
      | (mkSubOut (subIn $inner)) => $inner
      | _ => t

    def mkSubOutOther (t : Term) : Term :=
      match t with
      | (mkSubOut $e) => (subOut $e)
      | _ => t

  end MkSubOut

  section ReduceSub

    def reduceSubOut (t : Term) : Term :=
      match t with
      | (reduceSubOut (subOut (subIn $e))) => (some $e)
      | _ => t

    def reduceSubOutOther (t : Term) : Term :=
      match t with
      | (reduceSubOut $e) => (none)
      | _ => t

    def reduceSubExpr (t : Term) : Term :=
      match t with
      | (reduceSubExpr (subOut $e)) => (caseExpr ( case $e (arm ( subIn $inner ) => (some $inner)) (arm _ => (none)) ))
      | _ => t

    def reduceSubExprOther (t : Term) : Term :=
      match t with
      | (reduceSubExpr $e) => (none)
      | _ => t

  end ReduceSub

  section NormalizeSub

    def normalizeSub (t : Term) : Term :=
      match t with
      | (normalizeSub (num (number 0)) $e) => $e
      | _ => t

    def normalizeSubStep (t : Term) : Term :=
      match t with
      | (normalizeSub (succ $fuel) $e) => (caseExpr ( case (reduceSubExpr $e) (arm ( some $e' ) => (normalizeSub $fuel $e')) (arm none => (normalizeSubRec $fuel $e)) ))
      | _ => t

    def normalizeSubRec (t : Term) : Term :=
      match t with
      | (normalizeSubRec $fuel (sub $ty $cof $bdry)) => (sub (normalizeSub $fuel $ty) (normalizeSub $fuel $cof) (normalizeSub $fuel $bdry))
      | _ => t

    def normalizeSubRecIn (t : Term) : Term :=
      match t with
      | (normalizeSubRec $fuel (subIn $inner)) => (subIn (normalizeSub $fuel $inner))
      | _ => t

    def normalizeSubRecOut (t : Term) : Term :=
      match t with
      | (normalizeSubRec $fuel (subOut $inner)) => (letIn ( let $ inner' = (normalizeSub $fuel $inner) in (caseExpr ( case $inner' (arm ( subIn $x ) => $x) (arm _ => (subOut $inner')) )) ))
      | _ => t

    def normalizeSubRecOther (t : Term) : Term :=
      match t with
      | (normalizeSubRec $fuel $e) => $e
      | _ => t

  end NormalizeSub

  section TrivialSub

    def trivialSubEquiv (t : Term) : Term :=
      match t with
      | (trivialSubEquiv $ty) => (mkSub $ty (cof_top (paren ( (lam (ix (num (number 0)))) ))))
      | _ => t

  end TrivialSub

  section ImpossibleSub

    def impossibleSub (t : Term) : Term :=
      match t with
      | (impossibleSub $ty) => (mkSub $ty (cof_bot (paren ( (lam (lit str "⊥-elim")) ))))
      | _ => t

  end ImpossibleSub

  section SubTypeEquiv

    def subTypeEquiv (t : Term) : Term :=
      match t with
      | (subTypeEquiv $s1 $s2) => (and (conv (subInfoBase $s1) (subInfoBase $s2)) (and (conv (subInfoCof $s1) (subInfoCof $s2)) (conv (subInfoBdry $s1) (subInfoBdry $s2))))
      | _ => t

  end SubTypeEquiv

  section SubKan

    def coeSub (t : Term) : Term :=
      match t with
      | (coeSub $r $r' (lam (sub $A $φ $t)) (subIn $v)) => (subIn (coe $r $r' (lam $A) $v))
      | _ => t

    def coeSubStuck (t : Term) : Term :=
      match t with
      | (coeSub $r $r' $line $v) => (coe $r $r' $line $v)
      | _ => t

    def hcomSub (t : Term) : Term :=
      match t with
      | (hcomSub (sub $A $φ $t) $r $r' $ψ $tubes (subIn $cap)) => (subIn (hcom $A $r $r' $ψ (mapSubOut $tubes) $cap))
      | _ => t

    def hcomSubStuck (t : Term) : Term :=
      match t with
      | (hcomSub $subTy $r $r' $ψ $tubes $cap) => (hcom $subTy $r $r' $ψ $tubes $cap)
      | _ => t

    def mapSubOut (t : Term) : Term :=
      match t with
      | (mapSubOut (lam (lam $body))) => (lam (lam (subOut $body)))
      | _ => t

  end SubKan

  section SubBoundaryCheck

    def checkSubBoundary (t : Term) : Term :=
      match t with
      | (checkSubBoundary $e (subInfo (labeledArg base : $A) (labeledArg cof : $φ) (labeledArg bdry : $t))) => (caseExpr ( case $φ (arm cof_bot => (true)) (arm cof_top => (conv $e (subst (num (number 0)) (lit str "trivial") $t))) (arm _ => (checkSubBoundaryGeneral $e $φ $t)) ))
      | _ => t

    def checkSubBoundaryGeneral (t : Term) : Term :=
      match t with
      | (checkSubBoundaryGeneral $e $φ $t) => (true)
      | _ => t

  end SubBoundaryCheck

  section SubPartial

    def partialToSub (t : Term) : Term :=
      match t with
      | (partialToSub $A $φ $partial) => (sub $A $φ $partial)
      | _ => t

    def subToPartial (t : Term) : Term :=
      match t with
      | (subToPartial (sub $A $φ $bdry)) => $bdry
      | _ => t

  end SubPartial

  section ExtIntegration

    def extAsSub (t : Term) : Term :=
      match t with
      | (extAsSub $dim $A $φ $bdry) => (pi $dim (sub (app (shift (num (number 0)) (num (number 1)) $A) (ix (num (number 0)))) (app (shift (num (number 0)) (num (number 1)) $φ) (ix (num (number 0)))) (app (shift (num (number 0)) (num (number 1)) $bdry) (ix (num (number 0))))))
      | _ => t

  end ExtIntegration

end SubType