(DImport import (modulePath Core) ;)

namespace TermBuilder

  section BuildCtx

    def bctx : Parser :=
      (annotated str "bctx" (special <number>) → bctx)

    def bctxEmpty (t : Term) : Term :=
      match t with
      | (bctxEmpty) => (bctx (num (number 0)))
      | _ => t

    def bctxLevel (t : Term) : Term :=
      match t with
      | (bctxLevel (bctx $l)) => $l
      | _ => t

    def bctxNext (t : Term) : Term :=
      match t with
      | (bctxNext (bctx $l)) => (bctx (suc $l))
      | _ => t

    def bctxFreshVar (t : Term) : Term :=
      match t with
      | (bctxFreshVar (bctx $l)) => (ix $l)
      | _ => t

  end BuildCtx

  section BuildM

    def runBuild (t : Term) : Term :=
      match t with
      | (runBuild $ma) => ($ma (bctxEmpty))
      | _ => t

    def getCtx (t : Term) : Term :=
      match t with
      | (getCtx $ctx) => $ctx
      | _ => t

    def getLevel (t : Term) : Term :=
      match t with
      | (getLevel $ctx) => (bctxLevel $ctx)
      | _ => t

    def withBinder (t : Term) : Term :=
      match t with
      | (withBinder $k $ctx) => ($k (bctxFreshVar $ctx) (bctxNext $ctx))
      | _ => t

  end BuildM

  section LamBuilder

    def buildLam (t : Term) : Term :=
      match t with
      | (buildLam $k $ctx) => (lam ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

    -- Test: test
    -- ()

  end LamBuilder

  section PiBuilder

    def buildPi (t : Term) : Term :=
      match t with
      | (buildPi $dom $k $ctx) => (pi ($dom $ctx) ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

    def buildArrow (t : Term) : Term :=
      match t with
      | (buildArrow $dom $cod $ctx) => (pi ($dom $ctx) (shift (num (number 0)) (num (number 1)) ($cod $ctx)))
      | _ => t

  end PiBuilder

  section SigmaBuilder

    def buildSigma (t : Term) : Term :=
      match t with
      | (buildSigma $fst $k $ctx) => (sigma ($fst $ctx) ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

    def buildProd (t : Term) : Term :=
      match t with
      | (buildProd $A $B $ctx) => (sigma ($A $ctx) (shift (num (number 0)) (num (number 1)) ($B $ctx)))
      | _ => t

  end SigmaBuilder

  section PairBuilder

    def buildPair (t : Term) : Term :=
      match t with
      | (buildPair $a $b $ctx) => (pair ($a $ctx) ($b $ctx))
      | _ => t

    def buildFst (t : Term) : Term :=
      match t with
      | (buildFst $p $ctx) => (fst ($p $ctx))
      | _ => t

    def buildSnd (t : Term) : Term :=
      match t with
      | (buildSnd $p $ctx) => (snd ($p $ctx))
      | _ => t

  end PairBuilder

  section PathBuilder

    def buildPath (t : Term) : Term :=
      match t with
      | (buildPath $tp $l $r $ctx) => (path ($tp $ctx) ($l $ctx) ($r $ctx))
      | _ => t

    def buildPlam (t : Term) : Term :=
      match t with
      | (buildPlam $k $ctx) => (plam ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

    def buildPapp (t : Term) : Term :=
      match t with
      | (buildPapp $p $dim $ctx) => (papp ($p $ctx) $dim)
      | _ => t

    def buildRefl (t : Term) : Term :=
      match t with
      | (buildRefl $a $ctx) => (refl ($a $ctx))
      | _ => t

  end PathBuilder

  section SubBuilder

    def buildSub (t : Term) : Term :=
      match t with
      | (buildSub $tp $φ $k $ctx) => (sub ($tp $ctx) ($φ $ctx) ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

    def buildSubIn (t : Term) : Term :=
      match t with
      | (buildSubIn $e $ctx) => (subIn ($e $ctx))
      | _ => t

    def buildSubOut (t : Term) : Term :=
      match t with
      | (buildSubOut $e $ctx) => (subOut ($e $ctx))
      | _ => t

  end SubBuilder

  section CoeBuilder

    def buildCoe (t : Term) : Term :=
      match t with
      | (buildCoe $r $r' $line $a $ctx) => (coe $r $r' (plam ($line (bctxFreshVar $ctx) (bctxNext $ctx))) ($a $ctx))
      | _ => t

    def buildCoeSimple (t : Term) : Term :=
      match t with
      | (buildCoeSimple $r $r' $line $a $ctx) => (coe $r $r' ($line $ctx) ($a $ctx))
      | _ => t

  end CoeBuilder

  section HComBuilder

    def buildHCom (t : Term) : Term :=
      match t with
      | (buildHCom $r $r' $A $φ $tube $cap $ctx) => (hcom $r $r' ($A $ctx) ($φ $ctx) ($tube $ctx) ($cap $ctx))
      | _ => t

  end HComBuilder

  section ComBuilder

    def buildCom (t : Term) : Term :=
      match t with
      | (buildCom $r $r' $line $φ $tube $cap $ctx) => (com $r $r' (plam ($line (bctxFreshVar $ctx) (bctxNext $ctx))) ($φ $ctx) ($tube $ctx) ($cap $ctx))
      | _ => t

  end ComBuilder

  section ExtBuilder

    def buildExt (t : Term) : Term :=
      match t with
      | (buildExt $n $fam $cof $bdry $ctx) => (ext $n ($fam $ctx) ($cof $ctx) ($bdry $ctx))
      | _ => t

    def buildExtLam (t : Term) : Term :=
      match t with
      | (buildExtLam $n $body $ctx) => (extLam $n ($body $ctx))
      | _ => t

    def buildExtApp (t : Term) : Term :=
      match t with
      | (buildExtApp $e $dims $ctx) => (extApp ($e $ctx) $dims)
      | _ => t

  end ExtBuilder

  section NatBuilder

    def buildNat (t : Term) : Term :=
      match t with
      | (buildNat $ctx) => (nat)
      | _ => t

    def buildZero (t : Term) : Term :=
      match t with
      | (buildZero $ctx) => (zero)
      | _ => t

    def buildSuc (t : Term) : Term :=
      match t with
      | (buildSuc $n $ctx) => (suc ($n $ctx))
      | _ => t

    def buildNatElim (t : Term) : Term :=
      match t with
      | (buildNatElim $P $z $s $n $ctx) => (natElim ($P $ctx) ($z $ctx) ($s $ctx) ($n $ctx))
      | _ => t

  end NatBuilder

  section CircleBuilder

    def buildCircle (t : Term) : Term :=
      match t with
      | (buildCircle $ctx) => (circle)
      | _ => t

    def buildBase (t : Term) : Term :=
      match t with
      | (buildBase $ctx) => (base)
      | _ => t

    def buildLoop (t : Term) : Term :=
      match t with
      | (buildLoop $r $ctx) => (loop $r)
      | _ => t

    def buildCircleElim (t : Term) : Term :=
      match t with
      | (buildCircleElim $P $b $l $x $ctx) => (circleElim ($P $ctx) ($b $ctx) ($l $ctx) ($x $ctx))
      | _ => t

  end CircleBuilder

  section UnivBuilder

    def buildUniv (t : Term) : Term :=
      match t with
      | (buildUniv $l $ctx) => (univ $l)
      | _ => t

    def buildType (t : Term) : Term :=
      match t with
      | (buildType $ctx) => (univ (lzero))
      | _ => t

    def buildTypeAt (t : Term) : Term :=
      match t with
      | (buildTypeAt $n $ctx) => (univ (levelOfNat $n))
      | _ => t

    def levelOfNat0 (t : Term) : Term :=
      match t with
      | (levelOfNat (num (number 0))) => (lzero)
      | _ => t

    def levelOfNatS (t : Term) : Term :=
      match t with
      | (levelOfNat (suc $n)) => (lsuc (levelOfNat $n))
      | _ => t

  end UnivBuilder

  section VTypeBuilder

    def buildVType (t : Term) : Term :=
      match t with
      | (buildVType $r $A $B $equiv $ctx) => (vtype $r ($A $ctx) ($B $ctx) ($equiv $ctx))
      | _ => t

    def buildVIn (t : Term) : Term :=
      match t with
      | (buildVIn $r $a $b $ctx) => (vin $r ($a $ctx) ($b $ctx))
      | _ => t

    def buildVProj (t : Term) : Term :=
      match t with
      | (buildVProj $r $A $B $equiv $v $ctx) => (vproj $r ($A $ctx) ($B $ctx) ($equiv $ctx) ($v $ctx))
      | _ => t

  end VTypeBuilder

  section AppBuilder

    def buildApp (t : Term) : Term :=
      match t with
      | (buildApp $f $a $ctx) => (app ($f $ctx) ($a $ctx))
      | _ => t

    def buildApps0 (t : Term) : Term :=
      match t with
      | (buildApps $f (unit ( )) $ctx) => ($f $ctx)
      | _ => t

    def buildApps1 (t : Term) : Term :=
      match t with
      | (buildApps $f ($a $rest) $ctx) => (buildApps (fun (c) (=>) (app ($f (c)) ($a (c)))) $rest $ctx)
      | _ => t

  end AppBuilder

  section LetBuilder

    def buildLet (t : Term) : Term :=
      match t with
      | (buildLet $ty $val $k $ctx) => (letE ($ty $ctx) ($val $ctx) ($k (bctxFreshVar $ctx) (bctxNext $ctx)))
      | _ => t

  end LetBuilder

end TermBuilder