(DImport import (modulePath Core) ;)

(DImport import (modulePath Kan) ;)

namespace FHCom

  section FHComInfo

    def fhcomInfo : Parser :=
      (annotated str "fhcomInfo" str "r:" (special <expr>) str "r':" (special <expr>) str "cap:" (special <expr>) str "sys:" many ((special <sysEntry>)) → fhcomInfo)

    def sysEntry : Parser :=
      (annotated str "[" (special <expr>) str "↦" (special <expr>) str "]" → sysEntry)

    def fhcomInfoR (t : Term) : Term :=
      match t with
      | (fhcomInfoR (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $r
      | _ => t

    def fhcomInfoR' (t : Term) : Term :=
      match t with
      | (fhcomInfoR' (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $r'
      | _ => t

    def fhcomInfoCap (t : Term) : Term :=
      match t with
      | (fhcomInfoCap (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $c
      | _ => t

    def fhcomInfoSys (t : Term) : Term :=
      match t with
      | (fhcomInfoSys (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $s
      | _ => t

    def fhcomInfoIsDegenerate (t : Term) : Term :=
      match t with
      | (fhcomInfoIsDegenerate (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => (eq $r $r')
      | _ => t

    def fhcomInfoAtR (t : Term) : Term :=
      match t with
      | (fhcomInfoAtR (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $c
      | _ => t

    def fhcomInfoAtR' (t : Term) : Term :=
      match t with
      | (fhcomInfoAtR' (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => (caseExpr ( case (eq $r $r') (arm true => $c) (arm false => $c) ))
      | _ => t

    def fhcomInfoReduce (t : Term) : Term :=
      match t with
      | (fhcomInfoReduce (fhcomInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => (caseExpr ( case (eq $r $r') (arm true => (some $c)) (arm false => (none)) ))
      | _ => t

  end FHComInfo

  section MkFHCom

    def mkFHCom (t : Term) : Term :=
      match t with
      | (mkFHCom $r $r' $cap $sys) => (caseExpr ( case (eq $r $r') (arm true => $cap) (arm false => (fhcom $r $r' $cap $sys)) ))
      | _ => t

  end MkFHCom

  section BoxInfo

    def boxInfo : Parser :=
      (annotated str "boxInfo" str "r:" (special <expr>) str "r':" (special <expr>) str "cap:" (special <expr>) str "sys:" many ((special <sysEntry>)) → boxInfo)

    def boxInfoR (t : Term) : Term :=
      match t with
      | (boxInfoR (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $r
      | _ => t

    def boxInfoR' (t : Term) : Term :=
      match t with
      | (boxInfoR' (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $r'
      | _ => t

    def boxInfoCap (t : Term) : Term :=
      match t with
      | (boxInfoCap (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $c
      | _ => t

    def boxInfoSys (t : Term) : Term :=
      match t with
      | (boxInfoSys (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $s
      | _ => t

    def boxInfoIsDegenerate (t : Term) : Term :=
      match t with
      | (boxInfoIsDegenerate (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => (eq $r $r')
      | _ => t

    def boxInfoGetCap (t : Term) : Term :=
      match t with
      | (boxInfoGetCap (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => $c
      | _ => t

    def boxInfoReduce (t : Term) : Term :=
      match t with
      | (boxInfoReduce (boxInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg cap : $c) (labeledArg sys : $s))) => (caseExpr ( case (eq $r $r') (arm true => (some $c)) (arm false => (none)) ))
      | _ => t

  end BoxInfo

  section MkBox

    def mkBox (t : Term) : Term :=
      match t with
      | (mkBox $r $r' $cap $sys) => (caseExpr ( case (eq $r $r') (arm true => $cap) (arm false => (box $r $r' $cap $sys)) ))
      | _ => t

  end MkBox

  section CapInfo

    def capInfo : Parser :=
      (annotated str "capInfo" str "r:" (special <expr>) str "r':" (special <expr>) str "ty:" (special <expr>) str "sys:" many ((special <sysEntry>)) str "el:" (special <expr>) → capInfo)

    def capInfoR (t : Term) : Term :=
      match t with
      | (capInfoR (capInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg ty : $t) (labeledArg sys : $s) (labeledArg el : $e))) => $r
      | _ => t

    def capInfoR' (t : Term) : Term :=
      match t with
      | (capInfoR' (capInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg ty : $t) (labeledArg sys : $s) (labeledArg el : $e))) => $r'
      | _ => t

    def capInfoTy (t : Term) : Term :=
      match t with
      | (capInfoTy (capInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg ty : $t) (labeledArg sys : $s) (labeledArg el : $e))) => $t
      | _ => t

    def capInfoSys (t : Term) : Term :=
      match t with
      | (capInfoSys (capInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg ty : $t) (labeledArg sys : $s) (labeledArg el : $e))) => $s
      | _ => t

    def capInfoEl (t : Term) : Term :=
      match t with
      | (capInfoEl (capInfo (labeledArg r : $r) (labeledArg r' : $r') (labeledArg ty : $t) (labeledArg sys : $s) (labeledArg el : $e))) => $e
      | _ => t

  end CapInfo

  section MkCap

    def mkCapBox (t : Term) : Term :=
      match t with
      | (mkCap $r $r' $ty $sys (box $r $r' $cap $sysBx)) => $cap
      | _ => t

    def mkCapDegenerate (t : Term) : Term :=
      match t with
      | (mkCap $r $r $ty $sys $v) => $v
      | _ => t

    def mkCapOther (t : Term) : Term :=
      match t with
      | (mkCap $r $r' $ty $sys $v) => (cap $r $r' $ty $sys $v)
      | _ => t

  end MkCap

  section ReduceFHCom

    def reduceFHComDegenerate (t : Term) : Term :=
      match t with
      | (reduceFHCom (fhcom $r $r $cap $sys)) => (some $cap)
      | _ => t

    def reduceFHComOther (t : Term) : Term :=
      match t with
      | (reduceFHCom $e) => (none)
      | _ => t

    def reduceBoxDegenerate (t : Term) : Term :=
      match t with
      | (reduceBox (box $r $r $cap $sys)) => (some $cap)
      | _ => t

    def reduceBoxOther (t : Term) : Term :=
      match t with
      | (reduceBox $e) => (none)
      | _ => t

    def reduceCapBeta (t : Term) : Term :=
      match t with
      | (reduceCap (cap $r $r' $ty $sys (box $r $r' $cap $sysBx))) => (some $cap)
      | _ => t

    def reduceCapDegenerate (t : Term) : Term :=
      match t with
      | (reduceCap (cap $r $r $ty $sys $v)) => (some $v)
      | _ => t

    def reduceCapOther (t : Term) : Term :=
      match t with
      | (reduceCap $e) => (none)
      | _ => t

  end ReduceFHCom

  section HComFHCom

    def hcomFHCom (t : Term) : Term :=
      match t with
      | (hcomFHCom $r $r' (fhcom $rTy $r'Ty $capTy $sysTy) $φ $tubes $cap) => (mkBox $r $r' (hcom $capTy $r $r' $φ (lam (lam (mkCap $rTy $r'Ty $capTy $sysTy (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0))))))) (mkCap $rTy $r'Ty $capTy $sysTy $cap)) (hcomSys $sysTy $φ $tubes $cap $r $r'))
      | _ => t

    def hcomSys (t : Term) : Term :=
      match t with
      | (hcomSys (unit ( )) $φ $tubes $cap $r $r') => (unit ( ))
      | _ => t

    def hcomSysCons (t : Term) : Term :=
      match t with
      | (hcomSys (( ( [ $φSys (↦) $tube ] ) $rest )) $φ $tubes $cap $r $r') => ((( (bracket [ $φSys (↦) (lam (lam (getSide (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0)))) $φSys))) ]) )) (hcomSys $rest $φ $tubes $cap $r $r'))
      | _ => t

    def getSide (t : Term) : Term :=
      match t with
      | (getSide (box $r $r' $cap $sys) $φ) => (lookupSys $sys $φ)
      | _ => t

    def getSideOther (t : Term) : Term :=
      match t with
      | (getSide $e $φ) => $e
      | _ => t

    def lookupSysNil (t : Term) : Term :=
      match t with
      | (lookupSys (unit ( )) $φ) => (lit str "side-not-found")
      | _ => t

    def lookupSysMatch (t : Term) : Term :=
      match t with
      | (lookupSys (( ( [ $φ (↦) $side ] ) $rest )) $φ) => $side
      | _ => t

    def lookupSysMiss (t : Term) : Term :=
      match t with
      | (lookupSys (( ( $entry ) $rest )) $φ) => (lookupSys $rest $φ)
      | _ => t

  end HComFHCom

  section CoeFHCom

    def coeFHCom (t : Term) : Term :=
      match t with
      | (coeFHCom $r $r' (lam (fhcom $rTy $r'Ty $capTy $sysTy)) $v) => (mkBox $r $r' (com (lam $capTy) $r $r' (cof_bot (paren ( (lam (paren ( (lam (lit str "no-tube")) ))) )) (mkCap $rTy $r'Ty (subst (num (number 0)) $r $capTy) $sysTy $v))) (unit ( )))
      | _ => t

  end CoeFHCom

  section VProjFHCom

    def vprojFHCom (t : Term) : Term :=
      match t with
      | (vprojFHCom $r (fhcom $rTy $r'Ty $A $sys) $B $equiv $v) => (mkCap $rTy $r'Ty $A $sys (vproj $r $A $B $equiv $v))
      | _ => t

  end VProjFHCom

  section UnfoldFHCom

    def unfoldFHComAt0 (t : Term) : Term :=
      match t with
      | (unfoldFHComAt (fhcom (dim0) $r' $cap $sys) (dim0)) => $cap
      | _ => t

    def unfoldFHComAt1 (t : Term) : Term :=
      match t with
      | (unfoldFHComAt (fhcom (dim1) $r' $cap $sys) (dim1)) => $cap
      | _ => t

    def unfoldFHComAtOther (t : Term) : Term :=
      match t with
      | (unfoldFHComAt $fh $r) => $fh
      | _ => t

    def unfoldBoxAt0 (t : Term) : Term :=
      match t with
      | (unfoldBoxAt (box (dim0) $r' $cap $sys) (dim0)) => $cap
      | _ => t

    def unfoldBoxAt1 (t : Term) : Term :=
      match t with
      | (unfoldBoxAt (box (dim1) $r' $cap $sys) (dim1)) => $cap
      | _ => t

    def unfoldBoxAtOther (t : Term) : Term :=
      match t with
      | (unfoldBoxAt $bx $r) => $bx
      | _ => t

  end UnfoldFHCom

end FHCom