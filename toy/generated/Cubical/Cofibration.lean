(DImport import (modulePath Core) ;)

namespace Cofibration

  section DimOps

    def isDim0_0 (t : Term) : Term :=
      match t with
      | (isDim0 (dim0)) => (true)
      | _ => t

    def isDim0_1 (t : Term) : Term :=
      match t with
      | (isDim0 (dim1)) => (false)
      | _ => t

    def isDim0_var (t : Term) : Term :=
      match t with
      | (isDim0 (dimVar $n)) => (false)
      | _ => t

    def isDim1_0 (t : Term) : Term :=
      match t with
      | (isDim1 (dim0)) => (false)
      | _ => t

    def isDim1_1 (t : Term) : Term :=
      match t with
      | (isDim1 (dim1)) => (true)
      | _ => t

    def isDim1_var (t : Term) : Term :=
      match t with
      | (isDim1 (dimVar $n)) => (false)
      | _ => t

    def dimEq00 (t : Term) : Term :=
      match t with
      | (dimEq (dim0) (dim0)) => (true)
      | _ => t

    def dimEq11 (t : Term) : Term :=
      match t with
      | (dimEq (dim1) (dim1)) => (true)
      | _ => t

    def dimEqVar (t : Term) : Term :=
      match t with
      | (dimEq (dimVar $n) (dimVar $m)) => (eq $n $m)
      | _ => t

    def dimEqMixed (t : Term) : Term :=
      match t with
      | (dimEq $r $s) => (false)
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

    -- Test: test
    -- (dimEq $(dim0) $(dim0))

  end DimOps

  section CofConstructors

    def top (t : Term) : Term :=
      match t with
      | (top) => (cof_top)
      | _ => t

    def bot (t : Term) : Term :=
      match t with
      | (bot) => (cof_bot)
      | _ => t

    def eqSame (t : Term) : Term :=
      match t with
      | (cofEq $r $r) => (cof_top)
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | (cofEq (dim0) (dim1)) => (cof_bot)
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | (cofEq (dim1) (dim0)) => (cof_bot)
      | _ => t

    def eqGen (t : Term) : Term :=
      match t with
      | (cofEq $r $s) => (cof_eq $r $s)
      | _ => t

    def le (t : Term) : Term :=
      match t with
      | (cofLe $r $s) => (cof_or (cof_eq $r (dim0)) (cof_eq $s (dim1)))
      | _ => t

    def boundary (t : Term) : Term :=
      match t with
      | (boundary $r) => (cof_or (cof_eq $r (dim0)) (cof_eq $r (dim1)))
      | _ => t

    -- Test: test
    -- (cofEq $(dim0) $(dim0))

    -- Test: test
    -- (cofEq $(dim0) $(dim1))

    -- Test: test
    -- (cof_or (cof_eq (dimVar (num (number 0))) $(dim0)) (cof_eq (dimVar (num (number 0))) $(dim1)))

  end CofConstructors

  section Meet

    def meetTopL (t : Term) : Term :=
      match t with
      | (cof_and (cof_top) $φ) => $φ
      | _ => t

    def meetTopR (t : Term) : Term :=
      match t with
      | (cof_and $φ (cof_top)) => $φ
      | _ => t

    def meetBotL (t : Term) : Term :=
      match t with
      | (cof_and (cof_bot) $φ) => (cof_bot)
      | _ => t

    def meetBotR (t : Term) : Term :=
      match t with
      | (cof_and $φ (cof_bot)) => (cof_bot)
      | _ => t

    def meetIdem (t : Term) : Term :=
      match t with
      | (cof_and $φ $φ) => $φ
      | _ => t

    -- Test: test
    -- (cof_and $(cof_top) (cof_eq $(dim0) $(dim0)))

    -- Test: test
    -- (cof_and $(cof_bot) $(cof_top))

    -- Test: test
    -- (cof_and (cof_eq $(dim0) $(dim1)) (cof_eq $(dim0) $(dim1)))

  end Meet

  section Join

    def joinBotL (t : Term) : Term :=
      match t with
      | (cof_or (cof_bot) $φ) => $φ
      | _ => t

    def joinBotR (t : Term) : Term :=
      match t with
      | (cof_or $φ (cof_bot)) => $φ
      | _ => t

    def joinTopL (t : Term) : Term :=
      match t with
      | (cof_or (cof_top) $φ) => (cof_top)
      | _ => t

    def joinTopR (t : Term) : Term :=
      match t with
      | (cof_or $φ (cof_top)) => (cof_top)
      | _ => t

    def joinIdem (t : Term) : Term :=
      match t with
      | (cof_or $φ $φ) => $φ
      | _ => t

    -- Test: test
    -- (cof_or $(cof_bot) (cof_eq $(dim0) $(dim0)))

    -- Test: test
    -- (cof_or $(cof_top) (cof_eq $(dim0) $(dim1)))

    -- Test: test
    -- (cof_or (cof_eq $(dim0) $(dim1)) (cof_eq $(dim0) $(dim1)))

  end Join

  section Normalize

    def normTop (t : Term) : Term :=
      match t with
      | (normCof (cof_top)) => (cof_top)
      | _ => t

    def normBot (t : Term) : Term :=
      match t with
      | (normCof (cof_bot)) => (cof_bot)
      | _ => t

    def normEq (t : Term) : Term :=
      match t with
      | (normCof (cof_eq $r $s)) => (cofEq $r $s)
      | _ => t

    def normAnd (t : Term) : Term :=
      match t with
      | (normCof (cof_and $φ $ψ)) => (cof_and (normCof $φ) (normCof $ψ))
      | _ => t

    def normOr (t : Term) : Term :=
      match t with
      | (normCof (cof_or $φ $ψ)) => (cof_or (normCof $φ) (normCof $ψ))
      | _ => t

  end Normalize

  section Decide

    def cofTrueTop (t : Term) : Term :=
      match t with
      | (cofTrue (cof_top)) => (true)
      | _ => t

    def cofTrueBot (t : Term) : Term :=
      match t with
      | (cofTrue (cof_bot)) => (false)
      | _ => t

    def cofTrueEq (t : Term) : Term :=
      match t with
      | (cofTrue (cof_eq $r $s)) => (dimEq $r $s)
      | _ => t

    def cofTrueAnd (t : Term) : Term :=
      match t with
      | (cofTrue (cof_and $φ $ψ)) => (and (cofTrue $φ) (cofTrue $ψ))
      | _ => t

    def cofTrueOr (t : Term) : Term :=
      match t with
      | (cofTrue (cof_or $φ $ψ)) => (or (cofTrue $φ) (cofTrue $ψ))
      | _ => t

    def cofFalse (t : Term) : Term :=
      match t with
      | (cofFalse $φ) => (not (cofTrue $φ))
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Decide

  section Sequent

    def entails (t : Term) : Term :=
      match t with
      | (entails $φ $ψ) => (cofTrue (cof_or (cof_not $φ) $ψ))
      | _ => t

    def notTop (t : Term) : Term :=
      match t with
      | (cof_not (cof_top)) => (cof_bot)
      | _ => t

    def notBot (t : Term) : Term :=
      match t with
      | (cof_not (cof_bot)) => (cof_top)
      | _ => t

  end Sequent

  section DimSubst

    def substCofTop (t : Term) : Term :=
      match t with
      | (substCof $n $r (cof_top)) => (cof_top)
      | _ => t

    def substCofBot (t : Term) : Term :=
      match t with
      | (substCof $n $r (cof_bot)) => (cof_bot)
      | _ => t

    def substCofEq (t : Term) : Term :=
      match t with
      | (substCof $n $r (cof_eq $s $t)) => (cof_eq (substDimInDim $n $r $s) (substDimInDim $n $r $t))
      | _ => t

    def substCofAnd (t : Term) : Term :=
      match t with
      | (substCof $n $r (cof_and $φ $ψ)) => (cof_and (substCof $n $r $φ) (substCof $n $r $ψ))
      | _ => t

    def substCofOr (t : Term) : Term :=
      match t with
      | (substCof $n $r (cof_or $φ $ψ)) => (cof_or (substCof $n $r $φ) (substCof $n $r $ψ))
      | _ => t

    def substDimVar (t : Term) : Term :=
      match t with
      | (substDimInDim $n $r (dimVar $n)) => $r
      | _ => t

    def substDimVarOther (t : Term) : Term :=
      match t with
      | (substDimInDim $n $r (dimVar $m)) => (dimVar $m)
      | _ => t

    def substDim0 (t : Term) : Term :=
      match t with
      | (substDimInDim $n $r (dim0)) => (dim0)
      | _ => t

    def substDim1 (t : Term) : Term :=
      match t with
      | (substDimInDim $n $r (dim1)) => (dim1)
      | _ => t

  end DimSubst

  section Forall

    def forallCof (t : Term) : Term :=
      match t with
      | (forallDim $i $φ) => (cof_and (substCof $i (dim0) $φ) (substCof $i (dim1) $φ))
      | _ => t

    def existsCof (t : Term) : Term :=
      match t with
      | (existsDim $i $φ) => (cof_or (substCof $i (dim0) $φ) (substCof $i (dim1) $φ))
      | _ => t

  end Forall

end Cofibration