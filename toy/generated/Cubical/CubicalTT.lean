namespace CubicalTT

  section Dimension

    def dim : Parser :=
      ((annotated str "0" → i0) <|> ((annotated str "1" → i1) <|> ((annotated (special <ident>) → ivar) <|> ((annotated dim str "∨" dim → join) <|> ((annotated dim str "∧" dim → meet) <|> (annotated str "~" dim → inv))))))

    def join0L (t : Term) : Term :=
      match t with
      | (join (num (number 0)) $r) => $r
      | _ => t

    def join0R (t : Term) : Term :=
      match t with
      | (join $r (num (number 0))) => $r
      | _ => t

    def join1L (t : Term) : Term :=
      match t with
      | (join (num (number 1)) $r) => (num (number 1))
      | _ => t

    def join1R (t : Term) : Term :=
      match t with
      | (join $r (num (number 1))) => (num (number 1))
      | _ => t

    def joinIdem (t : Term) : Term :=
      match t with
      | (join $r $r) => $r
      | _ => t

    def meet0L (t : Term) : Term :=
      match t with
      | (meet (num (number 0)) $r) => (num (number 0))
      | _ => t

    def meet0R (t : Term) : Term :=
      match t with
      | (meet $r (num (number 0))) => (num (number 0))
      | _ => t

    def meet1L (t : Term) : Term :=
      match t with
      | (meet (num (number 1)) $r) => $r
      | _ => t

    def meet1R (t : Term) : Term :=
      match t with
      | (meet $r (num (number 1))) => $r
      | _ => t

    def meetIdem (t : Term) : Term :=
      match t with
      | (meet $r $r) => $r
      | _ => t

    def inv0 (t : Term) : Term :=
      match t with
      | (inv (num (number 0))) => (num (number 1))
      | _ => t

    def inv1 (t : Term) : Term :=
      match t with
      | (inv (num (number 1))) => (num (number 0))
      | _ => t

    def invInv (t : Term) : Term :=
      match t with
      | (inv (inv $r)) => $r
      | _ => t

    def deMorganOr (t : Term) : Term :=
      match t with
      | (inv (join $r $s)) => (meet (inv $r) (inv $s))
      | _ => t

    def deMorganAnd (t : Term) : Term :=
      match t with
      | (inv (meet $r $s)) => (join (inv $r) (inv $s))
      | _ => t

    -- Test: test
    -- (join (num (number 0)) $(i))

    -- Test: test
    -- (meet (num (number 0)) $(i))

    -- Test: test
    -- ()

  end Dimension

  section Cofibration

    def cof : Parser :=
      ((annotated str "⊥" → cof0) <|> ((annotated str "⊤" → cof1) <|> ((annotated dim str "=" dim → eq) <|> ((annotated cof str "∨" cof → cofOr) <|> (annotated cof str "∧" cof → cofAnd)))))

    def cof0Or (t : Term) : Term :=
      match t with
      | (cofOr (cof0) $φ) => $φ
      | _ => t

    def cof1Or (t : Term) : Term :=
      match t with
      | (cofOr (cof1) $φ) => (cof1)
      | _ => t

    def cofOrIdem (t : Term) : Term :=
      match t with
      | (cofOr $φ $φ) => $φ
      | _ => t

    def cof0And (t : Term) : Term :=
      match t with
      | (cofAnd (cof0) $φ) => (cof0)
      | _ => t

    def cof1And (t : Term) : Term :=
      match t with
      | (cofAnd (cof1) $φ) => $φ
      | _ => t

    def cofAndIdem (t : Term) : Term :=
      match t with
      | (cofAnd $φ $φ) => $φ
      | _ => t

    def eqRefl (t : Term) : Term :=
      match t with
      | (eq $r $r) => (cof1)
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | (eq (num (number 0)) (num (number 1))) => (cof0)
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | (eq (num (number 1)) (num (number 0))) => (cof0)
      | _ => t

  end Cofibration

  section Core

    def term : Parser :=
      ((annotated str "U" → U) <|> ((annotated (special <ident>) → var) <|> ((annotated str "(" term term str ")" → app) <|> ((annotated str "(" term str "," term str ")" → pair) <|> ((annotated term str ".fst" → fst) <|> (annotated term str ".snd" → snd))))))

    def fstPair (t : Term) : Term :=
      match t with
      | (fst (pair $a $b)) => $a
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | (snd (pair $a $b)) => $b
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- ()

  end Core

  section Lambda

    def term : Parser :=
      ((annotated str "λ" (special <ident>) str "." term → lam) <|> ((annotated str "λᵢ" (special <ident>) str "." term → dlam) <|> (annotated term str "@" dim → dapp)))

    def beta (t : Term) : Term :=
      match t with
      | (app (lam (binder $ x . $body)) $arg) => (subst [ $x := $arg ] $body)
      | _ => t

    def dbeta (t : Term) : Term :=
      match t with
      | (dapp (dlam (binder $ i . $body)) $r) => (subst [ $i := $r ] $body)
      | _ => t

    -- Test: test
    -- (app (lam (objBinder x . $(x))) $(y))

    -- Test: test
    -- (dapp (dlam (objBinder i . (dapp $(f) $(i)))) (num (number 0)))

  end Lambda

  section Pi

    def term : Parser :=
      ((annotated str "Π" str "(" (special <ident>) str ":" term str ")" str "." term → Pi) <|> (annotated term str "→" term → arr))

    def arrSugar (t : Term) : Term :=
      match t with
      | ($A (→) $B) => (Pi (labeledArg _ : (binder $ A . $B)))
      | _ => t

  end Pi

  section Sigma

    def term : Parser :=
      ((annotated str "Σ" str "(" (special <ident>) str ":" term str ")" str "." term → Sigma) <|> (annotated term str "×" term → prod))

    def prodSugar (t : Term) : Term :=
      match t with
      | ($A (×) $B) => (Sigma (labeledArg _ : (binder $ A . $B)))
      | _ => t

  end Sigma

  section Path

    def term : Parser :=
      ((annotated str "Path" term term term → Path) <|> (annotated str "PathP" (special <ident>) str "." term term term → PathP))

    def pathSugar (t : Term) : Term :=
      match t with
      | (Path $A $a $b) => (introExpr ( PathP _ . $A (.) (binder $ a . $b) ))
      | _ => t

    -- Test: test
    -- ()

  end Path

  section System

    def system : Parser :=
      ((annotated str "[" str "]" → sysEmpty) <|> (annotated str "[" sysbranch many ((group ( str "," sysbranch ))) str "]" → sys))

    def sysbranch : Parser :=
      (annotated cof str "↦" term → branch)

  end System

  section Coe

    def term : Parser :=
      (annotated str "coe" dim str "~>" dim str "(" (special <ident>) str "." term str ")" term → coe)

    def coeRefl (t : Term) : Term :=
      match t with
      | (coe $r (~>) $r (binderParen ( $ i . $A )) $a) => $a
      | _ => t

    def coeConst (t : Term) : Term :=
      match t with
      | (coe $r (~>) $s (binderParen ( $ i . $A )) $a) => $a
      | _ => t

    -- Test: test
    -- (coe (num (number 0)) (~>) (num (number 0)) (objBinderParen ( i . $(A) )) $(a))

  end Coe

  section Hcom

    def term : Parser :=
      (annotated str "hcom" dim str "~>" dim term system term → hcom)

    def hcomRefl (t : Term) : Term :=
      match t with
      | (hcom $r (~>) $r $A $sys $a) => $a
      | _ => t

    def hcomTotal (t : Term) : Term :=
      match t with
      | (hcom $r (~>) $s $A (sys (bracket [ (cof1 (↦) $u) ])) $a) => (subst [ $j := $s ] $u)
      | _ => t

  end Hcom

  section Com

    def term : Parser :=
      (annotated str "com" dim str "~>" dim str "(" (special <ident>) str "." term str ")" system term → com)

    def comRefl (t : Term) : Term :=
      match t with
      | (com $r (~>) $r (binderParen ( $ i . $A )) $sys $a) => $a
      | _ => t

  end Com

  section VType

    def term : Parser :=
      ((annotated str "V" dim term term term → V) <|> ((annotated str "Vin" dim term → Vin) <|> (annotated str "Vproj" dim term term → Vproj)))

    def V0 (t : Term) : Term :=
      match t with
      | (V (num (number 0)) $A $B $e) => $A
      | _ => t

    def V1 (t : Term) : Term :=
      match t with
      | (V (num (number 1)) $A $B $e) => $B
      | _ => t

    def Vin0 (t : Term) : Term :=
      match t with
      | (Vin (num (number 0)) $a) => (fst $a)
      | _ => t

    def Vin1 (t : Term) : Term :=
      match t with
      | (Vin (num (number 1)) $a) => $a
      | _ => t

    def Vproj0 (t : Term) : Term :=
      match t with
      | (Vproj (num (number 0)) $v $e) => (app $e (snd $v))
      | _ => t

    def Vproj1 (t : Term) : Term :=
      match t with
      | (Vproj (num (number 1)) $v $e) => $v
      | _ => t

  end VType

  section Sub

    def term : Parser :=
      ((annotated str "Sub" term cof term → Sub) <|> ((annotated str "inS" term → inS) <|> (annotated str "outS" term → outS)))

    def outInS (t : Term) : Term :=
      match t with
      | (outS (inS $a)) => $a
      | _ => t

  end Sub

  section Glue

    def term : Parser :=
      ((annotated str "Glue" system term → Glue) <|> ((annotated str "glue" system term → glue) <|> (annotated str "unglue" cof term → unglue)))

    def unglueGlue (t : Term) : Term :=
      match t with
      | (unglue $φ (glue $sys $a)) => $a
      | _ => t

  end Glue

  section Conversion

    def convRefl (t : Term) : Term :=
      match t with
      | (conv $A $A) => (true)
      | _ => t

    def convSym (t : Term) : Term :=
      match t with
      | (conv $A $B) => (conv $B $A)
      | _ => t

    def convU (t : Term) : Term :=
      match t with
      | (conv (U) (U)) => (true)
      | _ => t

    def convPi (t : Term) : Term :=
      match t with
      | (conv (Pi (typedVar $ x : (binder $ A1 . $B1))) (Pi (typedVar $ x : (binder $ A2 . $B2)))) => (and (conv $A2 $A1) (conv $B1 $B2))
      | _ => t

    def convSigma (t : Term) : Term :=
      match t with
      | (conv (Σ (typedVar $ x : (binder $ A1 . $B1))) (Σ (typedVar $ x : (binder $ A2 . $B2)))) => (and (conv $A1 $A2) (conv $B1 $B2))
      | _ => t

    def convPath (t : Term) : Term :=
      match t with
      | (conv (PathP (binder $ i . (binder $ A1 . (binder $ a01 . $a11)))) (PathP (binder $ i . (binder $ A2 . (binder $ a02 . $a12))))) => (and (conv $A1 $A2) (and (conv $a01 $a02) (conv $a11 $a12)))
      | _ => t

  end Conversion

  section Neutral

    def isNeutralVar (t : Term) : Term :=
      match t with
      | (neutral (var $x)) => (true)
      | _ => t

    def isNeutralApp (t : Term) : Term :=
      match t with
      | (neutral (app $f $a)) => (neutral $f)
      | _ => t

    def isNeutralFst (t : Term) : Term :=
      match t with
      | (neutral (fst $p)) => (neutral $p)
      | _ => t

    def isNeutralSnd (t : Term) : Term :=
      match t with
      | (neutral (snd $p)) => (neutral $p)
      | _ => t

    def isNeutralDApp (t : Term) : Term :=
      match t with
      | (neutral (dapp $p $r)) => (neutral $p)
      | _ => t

    def isNeutralCoe (t : Term) : Term :=
      match t with
      | (neutral (coe $r (~>) $s (binderParen ( $ i . $A )) $a)) => (or (neutral $A) (neutral $a))
      | _ => t

    def isNeutralHcom (t : Term) : Term :=
      match t with
      | (neutral (hcom $r (~>) $s $A $sys $a)) => (or (neutral $A) (neutral $a))
      | _ => t

  end Neutral

  section Equiv

    def term : Parser :=
      ((annotated str "Equiv" term term → Equiv) <|> ((annotated str "idEquiv" term → idEquiv) <|> (annotated str "equivFun" term → equivFun)))

    def equivFunId (t : Term) : Term :=
      match t with
      | (equivFun (idEquiv $A)) => (introExpr ( lam x . x ))
      | _ => t

  end Equiv

  section Fiber

    def term : Parser :=
      (annotated str "Fiber" term term → Fiber)

  end Fiber

end CubicalTT