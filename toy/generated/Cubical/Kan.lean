(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

namespace Kan

  section Dir

    def dir : Parser :=
      (annotated str "dir" dim dim → dir)

    def isDegenerate (t : Term) : Term :=
      match t with
      | (dirIsDegenerate (dir $src $tgt)) => (dimEqD $src $tgt)
      | _ => t

    def dirOfExpr (t : Term) : Term :=
      match t with
      | (dirOfExpr $r $r') => (dir (dimOfExprForce $r) (dimOfExprForce $r'))
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Dir

  section EvalCof

    def evalCofTop (t : Term) : Term :=
      match t with
      | (evalCof $subst (cof_top)) => (true)
      | _ => t

    def evalCofBot (t : Term) : Term :=
      match t with
      | (evalCof $subst (cof_bot)) => (false)
      | _ => t

    def evalCofEq (t : Term) : Term :=
      match t with
      | (evalCof $subst (cof_eq $r $s)) => (dimEqSubst $subst $r $s)
      | _ => t

    def evalCofAnd (t : Term) : Term :=
      match t with
      | (evalCof $subst (cof_and $φ $ψ)) => (and (evalCof $subst $φ) (evalCof $subst $ψ))
      | _ => t

    def evalCofOr (t : Term) : Term :=
      match t with
      | (evalCof $subst (cof_or $φ $ψ)) => (or (evalCof $subst $φ) (evalCof $subst $ψ))
      | _ => t

  end EvalCof

  section SubstDim0

    def substDim0Ix (t : Term) : Term :=
      match t with
      | (substDim0' $d (ix $n)) => (ix $n)
      | _ => t

    def substDim0Dim0 (t : Term) : Term :=
      match t with
      | (substDim0' $d (dim0)) => (dim0)
      | _ => t

    def substDim0Dim1 (t : Term) : Term :=
      match t with
      | (substDim0' $d (dim1)) => (dim1)
      | _ => t

    def substDim0DimVar0 (t : Term) : Term :=
      match t with
      | (substDim0' $d (dimVar (num (number 0)))) => $d
      | _ => t

    def substDim0DimVarS (t : Term) : Term :=
      match t with
      | (substDim0' $d (dimVar (suc $n))) => (dimVar $n)
      | _ => t

    def substDim0Lam (t : Term) : Term :=
      match t with
      | (substDim0' $d (lam $body)) => (lam (substDim0' $d $body))
      | _ => t

    def substDim0Plam (t : Term) : Term :=
      match t with
      | (substDim0' $d (plam $body)) => (plam (substDim0' (shift (num (number 0)) (num (number 1)) $d) $body))
      | _ => t

    def substDim0App (t : Term) : Term :=
      match t with
      | (substDim0' $d (app $f $a)) => (app (substDim0' $d $f) (substDim0' $d $a))
      | _ => t

    def substDim0Pi (t : Term) : Term :=
      match t with
      | (substDim0' $d (pi $A $B)) => (pi (substDim0' $d $A) (substDim0' $d $B))
      | _ => t

  end SubstDim0

  section Coe

    def coeRefl (t : Term) : Term :=
      match t with
      | (coe $r $r $ty $a) => $a
      | _ => t

    def coeUniv (t : Term) : Term :=
      match t with
      | (coe $r $r' (plam (univ $l)) $a) => $a
      | _ => t

    def coePi (t : Term) : Term :=
      match t with
      | (coe $r $r' (plam (pi $dom $cod)) $f) => (lam (coe $r $r' (plamSubst (num (number 0)) (coe $r' $r (plamInv $dom) (ix (num (number 0)))) $cod) (app $f (coe $r' $r $dom (ix (num (number 0)))))))
      | _ => t

    def coeSigma (t : Term) : Term :=
      match t with
      | (coe $r $r' (plam (sigma $dom $cod)) $p) => (pair (coe $r $r' $dom (fst $p)) (coe $r $r' (plamSubst (num (number 0)) (coe $r $r' $dom (fst $p)) $cod) (snd $p)))
      | _ => t

    def coePath (t : Term) : Term :=
      match t with
      | (coe $r $r' (plam (path $A $a $b)) $p) => (plam (coe $r $r' $A (papp $p (dimVar (num (number 0))))))
      | _ => t

    -- Test: test
    -- (coe $(dim0) $(dim0) (plam (univ $(lzero))) (lit str "A"))

    -- Test: test
    -- (coe $(dim0) $(dim1) (plam (univ $(lzero))) (lit str "A"))

  end Coe

  section HCom

    def hcomRefl (t : Term) : Term :=
      match t with
      | (hcom $r $r $ty $phi $cap) => $cap
      | _ => t

    def hcomTrue (t : Term) : Term :=
      match t with
      | (hcom $r $r' $ty (cof_top) $tube $cap) => (app (app $tube $r') (lit str "prf"))
      | _ => t

    def hcomFalse (t : Term) : Term :=
      match t with
      | (hcom $r $r' $ty (cof_bot) $tube $cap) => $cap
      | _ => t

    def hcomPi (t : Term) : Term :=
      match t with
      | (hcom $r $r' (pi $A $B) $phi $tube $cap) => (lam (hcom $r $r' (substBody (num (number 0)) (ix (num (number 0))) $B) $phi (lam (lam (app (app (app $tube (ix (num (number 1)))) (ix (num (number 0)))) (ix (num (number 2)))))) (app $cap (ix (num (number 0))))))
      | _ => t

    def hcomSigma (t : Term) : Term :=
      match t with
      | (hcom $r $r' (sigma $A $B) $phi $tube $cap) => (pair (hcom $r $r' $A $phi (lam (lam (fst (app (app $tube (ix (num (number 1)))) (ix (num (number 0))))))) (fst $cap)) (com $r $r' (plam (substBody (num (number 0)) (hcom $r (dimVar (num (number 0))) $A $phi (lam (lam (fst (app (app $tube (ix (num (number 1)))) (ix (num (number 0))))))) (fst $cap)) $B)) $phi (lam (lam (snd (app (app $tube (ix (num (number 1)))) (ix (num (number 0))))))) (snd $cap)))
      | _ => t

    def hcomPath (t : Term) : Term :=
      match t with
      | (hcom $r $r' (path $A $a $b) $phi $tube $cap) => (plam (hcom $r $r' $A (cof_or $phi (cof_or (cof_eq (dimVar (num (number 0))) (dim0)) (cof_eq (dimVar (num (number 0))) (dim1)))) (mkTube $tube (dimVar (num (number 0))) $a $b) (papp $cap (dimVar (num (number 0))))))
      | _ => t

    -- Test: test
    -- (hcom $(dim0) $(dim0) (univ $(lzero)) $(cof_bot) (lit str "tube") (lit str "cap"))

    -- Test: test
    -- (hcom $(dim0) $(dim1) (univ $(lzero)) $(cof_bot) (lit str "tube") (lit str "cap"))

  end HCom

  section Com

    def comRefl (t : Term) : Term :=
      match t with
      | (com $r $r $line $phi $tube $cap) => $cap
      | _ => t

    def comGen (t : Term) : Term :=
      match t with
      | (com $r $r' $line $phi $tube $cap) => (hcom $r $r' (substDim0' $r' (plamBody $line)) $phi (lam (lam (coe (ix (num (number 1))) $r' $line (app (app $tube (ix (num (number 1)))) (ix (num (number 0))))))) (coe $r $r' $line $cap))
      | _ => t

    -- Test: test
    -- (com $(dim0) $(dim0) (plam (univ $(lzero))) $(cof_bot) (lit str "tube") (lit str "cap"))

  end Com

  section GHCom

    def ghcomRefl (t : Term) : Term :=
      match t with
      | (ghcom $r $r $A $sys $cap) => $cap
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | (ghcom $r $r' $A (sysCons (tuple ( $phi , $tube )) $rest) $cap) => (substDim0' $r' $tube)
      | _ => t

  end GHCom

  section GCom

    def gcomRefl (t : Term) : Term :=
      match t with
      | (gcom $r $r $line $sys $cap) => $cap
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | (gcom $r $r' $line (sysCons (tuple ( $phi , $tube )) $rest) $cap) => (substDim0' $r' $tube)
      | _ => t

  end GCom

end Kan