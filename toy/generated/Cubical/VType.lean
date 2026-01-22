(DImport import (modulePath Core) ;)

(DImport import (modulePath Quote) ;)

(DImport import (modulePath Kan) ;)

(DImport import (modulePath Visitor) ;)

namespace VType

  section VTypeInfo

    def vtypeInfo : Parser :=
      (annotated str "vtypeInfo" str "dim:" (special <expr>) str "ty0:" (special <expr>) str "ty1:" (special <expr>) str "equiv:" (special <expr>) → vtypeInfo)

    def vtypeInfoDim (t : Term) : Term :=
      match t with
      | (vtypeInfoDim (vtypeInfo (labeledArg dim : $d) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => $d
      | _ => t

    def vtypeInfoTy0 (t : Term) : Term :=
      match t with
      | (vtypeInfoTy0 (vtypeInfo (labeledArg dim : $d) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => $a
      | _ => t

    def vtypeInfoTy1 (t : Term) : Term :=
      match t with
      | (vtypeInfoTy1 (vtypeInfo (labeledArg dim : $d) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => $b
      | _ => t

    def vtypeInfoEquiv (t : Term) : Term :=
      match t with
      | (vtypeInfoEquiv (vtypeInfo (labeledArg dim : $d) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => $e
      | _ => t

    def vtypeInfoAtDim0 (t : Term) : Term :=
      match t with
      | (vtypeInfoAtDim0 (vtypeInfo (labeledArg dim : (dim0)) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => (true)
      | _ => t

    def vtypeInfoAtDim0Other (t : Term) : Term :=
      match t with
      | (vtypeInfoAtDim0 $info) => (false)
      | _ => t

    def vtypeInfoAtDim1 (t : Term) : Term :=
      match t with
      | (vtypeInfoAtDim1 (vtypeInfo (labeledArg dim : (dim1)) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => (true)
      | _ => t

    def vtypeInfoAtDim1Other (t : Term) : Term :=
      match t with
      | (vtypeInfoAtDim1 $info) => (false)
      | _ => t

    def vtypeInfoReduce (t : Term) : Term :=
      match t with
      | (vtypeInfoReduce (vtypeInfo (labeledArg dim : (dim0)) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => (some $a)
      | _ => t

    def vtypeInfoReduce1 (t : Term) : Term :=
      match t with
      | (vtypeInfoReduce (vtypeInfo (labeledArg dim : (dim1)) (labeledArg ty0 : $a) (labeledArg ty1 : $b) (labeledArg equiv : $e))) => (some $b)
      | _ => t

    def vtypeInfoReduceOther (t : Term) : Term :=
      match t with
      | (vtypeInfoReduce $info) => (none)
      | _ => t

  end VTypeInfo

  section VInInfo

    def vinInfo : Parser :=
      (annotated str "vinInfo" str "dim:" (special <expr>) str "tm0:" (special <expr>) str "tm1:" (special <expr>) → vinInfo)

    def vinInfoDim (t : Term) : Term :=
      match t with
      | (vinInfoDim (vinInfo (labeledArg dim : $d) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => $d
      | _ => t

    def vinInfoTm0 (t : Term) : Term :=
      match t with
      | (vinInfoTm0 (vinInfo (labeledArg dim : $d) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => $a
      | _ => t

    def vinInfoTm1 (t : Term) : Term :=
      match t with
      | (vinInfoTm1 (vinInfo (labeledArg dim : $d) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => $b
      | _ => t

    def vinInfoAtDim0 (t : Term) : Term :=
      match t with
      | (vinInfoAtDim0 (vinInfo (labeledArg dim : (dim0)) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => (true)
      | _ => t

    def vinInfoAtDim0Other (t : Term) : Term :=
      match t with
      | (vinInfoAtDim0 $info) => (false)
      | _ => t

    def vinInfoAtDim1 (t : Term) : Term :=
      match t with
      | (vinInfoAtDim1 (vinInfo (labeledArg dim : (dim1)) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => (true)
      | _ => t

    def vinInfoAtDim1Other (t : Term) : Term :=
      match t with
      | (vinInfoAtDim1 $info) => (false)
      | _ => t

    def vinInfoReduce (t : Term) : Term :=
      match t with
      | (vinInfoReduce (vinInfo (labeledArg dim : (dim0)) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => (some $a)
      | _ => t

    def vinInfoReduce1 (t : Term) : Term :=
      match t with
      | (vinInfoReduce (vinInfo (labeledArg dim : (dim1)) (labeledArg tm0 : $a) (labeledArg tm1 : $b))) => (some $b)
      | _ => t

    def vinInfoReduceOther (t : Term) : Term :=
      match t with
      | (vinInfoReduce $info) => (none)
      | _ => t

  end VInInfo

  section Equivalence

    def equivFunc (t : Term) : Term :=
      match t with
      | (equivFunc $e) => (fst $e)
      | _ => t

    def equivInv (t : Term) : Term :=
      match t with
      | (equivInv $e) => (fst (snd $e))
      | _ => t

    def isEquiv (t : Term) : Term :=
      match t with
      | (isEquiv (pair $f (pair $g $proofs))) => (true)
      | _ => t

    def isEquivOther (t : Term) : Term :=
      match t with
      | (isEquiv $e) => (false)
      | _ => t

  end Equivalence

  section MkVType

    def mkVType (t : Term) : Term :=
      match t with
      | (mkVType (dim0) $A $B $e) => $A
      | _ => t

    def mkVType1 (t : Term) : Term :=
      match t with
      | (mkVType (dim1) $A $B $e) => $B
      | _ => t

    def mkVTypeOther (t : Term) : Term :=
      match t with
      | (mkVType $r $A $B $e) => (vtype $r $A $B $e)
      | _ => t

  end MkVType

  section MkVIn

    def mkVIn (t : Term) : Term :=
      match t with
      | (mkVIn (dim0) $a $b) => $a
      | _ => t

    def mkVIn1 (t : Term) : Term :=
      match t with
      | (mkVIn (dim1) $a $b) => $b
      | _ => t

    def mkVInOther (t : Term) : Term :=
      match t with
      | (mkVIn $r $a $b) => (vin $r $a $b)
      | _ => t

  end MkVIn

  section ReduceVProj

    def reduceVProj0 (t : Term) : Term :=
      match t with
      | (reduceVProj (dim0) $ty0 $ty1 $equiv $el) => (app (equivFunc $equiv) $el)
      | _ => t

    def reduceVProj1 (t : Term) : Term :=
      match t with
      | (reduceVProj (dim1) $ty0 $ty1 $equiv $el) => $el
      | _ => t

    def reduceVProjVin (t : Term) : Term :=
      match t with
      | (reduceVProj $r $ty0 $ty1 $equiv (vin $r' $a $b)) => (caseExpr ( case (eq $r $r') (arm true => $b) (arm false => (vproj $r $ty0 $ty1 $equiv (vin $r' $a $b))) ))
      | _ => t

    def reduceVProjOther (t : Term) : Term :=
      match t with
      | (reduceVProj $r $ty0 $ty1 $equiv $el) => (vproj $r $ty0 $ty1 $equiv $el)
      | _ => t

  end ReduceVProj

  section CoeV

    def coeV (t : Term) : Term :=
      match t with
      | (coeV $dir (vtypeInfo (labeledArg dim : $d) (labeledArg ty0 : $A) (labeledArg ty1 : $B) (labeledArg equiv : $e)) $el) => (caseExpr ( case (dirIsDegenerate $dir) (arm true => $el) (arm false => (coeVBody $dir $d $A $B $e $el)) ))
      | _ => t

    def dirIsDegenerate (t : Term) : Term :=
      match t with
      | (dirIsDegenerate (dir $r $r)) => (true)
      | _ => t

    def dirIsDegenerateOther (t : Term) : Term :=
      match t with
      | (dirIsDegenerate $dir) => (false)
      | _ => t

    def coeVBody (t : Term) : Term :=
      match t with
      | (coeVBody (dir $r $r') $d $A $B $e $el) => (mkVIn $r' (coe $r $r' (lam $A) (caseExpr ( case $el (arm ( vin $_ $a $_ ) => $a) (arm _ => $el) ))) (coe $r $r' (lam $B) (caseExpr ( case $el (arm ( vin $_ $_ $b ) => $b) (arm _ => (app (equivFunc $e) $el)) ))))
      | _ => t

  end CoeV

  section HComV

    def hcomV (t : Term) : Term :=
      match t with
      | (hcomV (vtype $d $A $B $e) $r $r' $φ $tubes $cap) => (mkVIn $d (hcom $A $r $r' $φ (lam (lam (vinProj0 (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0))))))) (vinProj0 $cap)) (hcom $B $r $r' (cof_disj $φ (cof_eq $d (dim0))) (lam (lam (caseCof (ix (num (number 1))) ($φ (=>) (vinProj1 (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0)))))) ((( (cof_eq) $d (dim0) )) (=>) (app (equivFunc $e) (vinProj0 (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0)))))))))) (vinProj1 $cap)))
      | _ => t

    def vinProj0 (t : Term) : Term :=
      match t with
      | (vinProj0 (vin $d $a $b)) => $a
      | _ => t

    def vinProj0Other (t : Term) : Term :=
      match t with
      | (vinProj0 $e) => $e
      | _ => t

    def vinProj1 (t : Term) : Term :=
      match t with
      | (vinProj1 (vin $d $a $b)) => $b
      | _ => t

    def vinProj1Other (t : Term) : Term :=
      match t with
      | (vinProj1 $e) => $e
      | _ => t

  end HComV

  section Univalence

    def ua (t : Term) : Term :=
      match t with
      | (ua $A $B $e) => (plam (lit str "i") (vtype (ix (num (number 0))) (shift (num (number 0)) (num (number 1)) $A) (shift (num (number 0)) (num (number 1)) $B) (shift (num (number 0)) (num (number 1)) $e)))
      | _ => t

    def idEquiv (t : Term) : Term :=
      match t with
      | (idEquiv $A) => (pair (lam (ix (num (number 0)))) (pair (lam (ix (num (number 0)))) (pair (lam (refl)) (pair (lam (refl)) (lit str "contractible-fibers")))))
      | _ => t

    def uaβ (t : Term) : Term :=
      match t with
      | (uaβ $e $a) => (coe (dim0) (dim1 (ua (typeOf $a) (codomain $e) $e)) $a)
      | _ => t

    def uaη (t : Term) : Term :=
      match t with
      | (uaη $A) => (plam (lit str "_") $A)
      | _ => t

  end Univalence

  section VTypeQuote

    def quoteVType (t : Term) : Term :=
      match t with
      | (quoteVType (vtype $r $A $B $e)) => (surface ((string "V") (quoteDim $r) (quote $A) (quote $B) (quote $e)))
      | _ => t

    def quoteVIn (t : Term) : Term :=
      match t with
      | (quoteVIn (vin $r $a $b)) => (surface ((string "vin") (quoteDim $r) (quote $a) (quote $b)))
      | _ => t

    def quoteVProj (t : Term) : Term :=
      match t with
      | (quoteVProj (vproj $r $A $B $e $v)) => (surface ((string "vproj") (quoteDim $r) (quote $v)))
      | _ => t

  end VTypeQuote

  section VTypeNormalize

    def normalizeVType (t : Term) : Term :=
      match t with
      | (normalizeVType (vtype (dim0) $A $B $e)) => $A
      | _ => t

    def normalizeVType1 (t : Term) : Term :=
      match t with
      | (normalizeVType (vtype (dim1) $A $B $e)) => $B
      | _ => t

    def normalizeVTypeOther (t : Term) : Term :=
      match t with
      | (normalizeVType (vtype $r $A $B $e)) => (vtype (normalizeDim $r) (normalize $A) (normalize $B) (normalize $e))
      | _ => t

    def normalizeVIn (t : Term) : Term :=
      match t with
      | (normalizeVIn (vin (dim0) $a $b)) => $a
      | _ => t

    def normalizeVIn1 (t : Term) : Term :=
      match t with
      | (normalizeVIn (vin (dim1) $a $b)) => $b
      | _ => t

    def normalizeVInOther (t : Term) : Term :=
      match t with
      | (normalizeVIn (vin $r $a $b)) => (vin (normalizeDim $r) (normalize $a) (normalize $b))
      | _ => t

    def normalizeVProj (t : Term) : Term :=
      match t with
      | (normalizeVProj (vproj (dim0) $A $B $e $v)) => (app (equivFunc $e) $v)
      | _ => t

    def normalizeVProj1 (t : Term) : Term :=
      match t with
      | (normalizeVProj (vproj (dim1) $A $B $e $v)) => $v
      | _ => t

    def normalizeVProjVin (t : Term) : Term :=
      match t with
      | (normalizeVProj (vproj $r $A $B $e (vin $r $a $b))) => $b
      | _ => t

    def normalizeVProjOther (t : Term) : Term :=
      match t with
      | (normalizeVProj (vproj $r $A $B $e $v)) => (vproj (normalizeDim $r) (normalize $A) (normalize $B) (normalize $e) (normalize $v))
      | _ => t

  end VTypeNormalize

end VType