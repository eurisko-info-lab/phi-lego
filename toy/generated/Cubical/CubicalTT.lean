namespace CubicalTT

  section Dimension

    def dim : Parser :=
      ((annotated str "0" → i0) <|> ((annotated str "1" → i1) <|> ((annotated (special <ident>) → ivar) <|> ((annotated dim str "∨" dim → join) <|> ((annotated dim str "∧" dim → meet) <|> (annotated str "~" dim → inv))))))

    def join0L (t : Term) : Term :=
      match t with
      | (con ( join (num (number 0)) $r )) => (con ( join (num (number 0)) $r ))
      | _ => t

    def join0R (t : Term) : Term :=
      match t with
      | (con ( join $r (num (number 0)) )) => (con ( join $r (num (number 0)) ))
      | _ => t

    def join1L (t : Term) : Term :=
      match t with
      | (con ( join (num (number 1)) $r )) => (con ( join (num (number 1)) $r ))
      | _ => t

    def join1R (t : Term) : Term :=
      match t with
      | (con ( join $r (num (number 1)) )) => (con ( join $r (num (number 1)) ))
      | _ => t

    def joinIdem (t : Term) : Term :=
      match t with
      | (con ( join $r $r )) => (con ( join $r $r ))
      | _ => t

    def meet0L (t : Term) : Term :=
      match t with
      | (con ( meet (num (number 0)) $r )) => (con ( meet (num (number 0)) $r ))
      | _ => t

    def meet0R (t : Term) : Term :=
      match t with
      | (con ( meet $r (num (number 0)) )) => (con ( meet $r (num (number 0)) ))
      | _ => t

    def meet1L (t : Term) : Term :=
      match t with
      | (con ( meet (num (number 1)) $r )) => (con ( meet (num (number 1)) $r ))
      | _ => t

    def meet1R (t : Term) : Term :=
      match t with
      | (con ( meet $r (num (number 1)) )) => (con ( meet $r (num (number 1)) ))
      | _ => t

    def meetIdem (t : Term) : Term :=
      match t with
      | (con ( meet $r $r )) => (con ( meet $r $r ))
      | _ => t

    def inv0 (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def inv1 (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def invInv (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def deMorganOr (t : Term) : Term :=
      match t with
      | (con ( meet (inv $r) (inv $s) )) => (con ( meet (inv $r) (inv $s) ))
      | _ => t

    def deMorganAnd (t : Term) : Term :=
      match t with
      | (con ( join (inv $r) (inv $s) )) => (con ( join (inv $r) (inv $s) ))
      | _ => t

    -- Test: test
    -- (con ( join (num (number 0)) (var i) ))

    -- Test: test
    -- (con ( meet (num (number 0)) (var i) ))

    -- Test: test
    -- ()

  end Dimension

  section Cofibration

    def cof : Parser :=
      ((annotated str "⊥" → cof0) <|> ((annotated str "⊤" → cof1) <|> ((annotated dim str "=" dim → eq) <|> ((annotated cof str "∨" cof → cofOr) <|> (annotated cof str "∧" cof → cofAnd)))))

    def cof0Or (t : Term) : Term :=
      match t with
      | (con ( cofOr (con cof0) $φ )) => (con ( cofOr (con cof0) $φ ))
      | _ => t

    def cof1Or (t : Term) : Term :=
      match t with
      | (con ( cofOr (con cof1) $φ )) => (con cof1)
      | _ => t

    def cofOrIdem (t : Term) : Term :=
      match t with
      | (con ( cofOr $φ $φ )) => (con ( cofOr $φ $φ ))
      | _ => t

    def cof0And (t : Term) : Term :=
      match t with
      | (con ( cofAnd (con cof0) $φ )) => (con cof0)
      | _ => t

    def cof1And (t : Term) : Term :=
      match t with
      | (con ( cofAnd (con cof1) $φ )) => (con ( cofAnd (con cof1) $φ ))
      | _ => t

    def cofAndIdem (t : Term) : Term :=
      match t with
      | (con ( cofAnd $φ $φ )) => (con ( cofAnd $φ $φ ))
      | _ => t

    def eqRefl (t : Term) : Term :=
      match t with
      | (con ( eq $r $r )) => (con cof1)
      | _ => t

    def eq01 (t : Term) : Term :=
      match t with
      | (con ( eq (num (number 0)) (num (number 1)) )) => (con cof0)
      | _ => t

    def eq10 (t : Term) : Term :=
      match t with
      | (con ( eq (num (number 1)) (num (number 0)) )) => (con cof0)
      | _ => t

  end Cofibration

  section Core

    def term : Parser :=
      ((annotated str "U" → U) <|> ((annotated (special <ident>) → var) <|> ((annotated str "(" term term str ")" → app) <|> ((annotated str "(" term str "," term str ")" → pair) <|> ((annotated term str ".fst" → fst) <|> (annotated term str ".snd" → snd))))))

    def fstPair (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def sndPair (t : Term) : Term :=
      match t with
      | () => ()
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
      | (con ( app (lam (binder $ x . $body)) $arg )) => (con ( app (lam (binder $ x . $body)) $arg ))
      | _ => t

    def dbeta (t : Term) : Term :=
      match t with
      | (con ( dapp (dlam (binder $ i . $body)) $r )) => (con ( dapp (dlam (binder $ i . $body)) $r ))
      | _ => t

    -- Test: test
    -- (con ( app (lam (objBinder x . (var x))) (var y) ))

    -- Test: test
    -- (con ( dapp (dlam (objBinder i . (con ( dapp (var f) (var i) )))) (num (number 0)) ))

  end Lambda

  section Pi

    def term : Parser :=
      ((annotated str "Π" str "(" (special <ident>) str ":" term str ")" str "." term → Pi) <|> (annotated term str "→" term → arr))

    def arrSugar (t : Term) : Term :=
      match t with
      | (con ( $A (con →) $B )) => (con ( $A (con →) $B ))
      | _ => t

  end Pi

  section Sigma

    def term : Parser :=
      ((annotated str "Σ" str "(" (special <ident>) str ":" term str ")" str "." term → Sigma) <|> (annotated term str "×" term → prod))

    def prodSugar (t : Term) : Term :=
      match t with
      | (con ( $A (con ×) $B )) => (con ( $A (con ×) $B ))
      | _ => t

  end Sigma

  section Path

    def term : Parser :=
      ((annotated str "Path" term term term → Path) <|> (annotated str "PathP" (special <ident>) str "." term term term → PathP))

    def pathSugar (t : Term) : Term :=
      match t with
      | (con ( Path $A $a $b )) => (con ( Path $A $a $b ))
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
      | (con ( coe $r (con ~>) $r (binderParen ( $ i . $A )) $a )) => (con ( coe $r (con ~>) $r (binderParen ( $ i . $A )) $a ))
      | _ => t

    def coeConst (t : Term) : Term :=
      match t with
      | (con ( coe $r (con ~>) $s (binderParen ( $ i . $A )) $a )) => (con ( coe $r (con ~>) $s (binderParen ( $ i . $A )) $a ))
      | _ => t

    -- Test: test
    -- (con ( coe (num (number 0)) (con ~>) (num (number 0)) (objBinderParen ( i . (var A) )) (var a) ))

  end Coe

  section Hcom

    def term : Parser :=
      (annotated str "hcom" dim str "~>" dim term system term → hcom)

    def hcomRefl (t : Term) : Term :=
      match t with
      | (con ( hcom $r (con ~>) $r $A $sys $a )) => (con ( hcom $r (con ~>) $r $A $sys $a ))
      | _ => t

    def hcomTotal (t : Term) : Term :=
      match t with
      | (con ( hcom $r (con ~>) $s $A (sys (bracket [ (con ( cof1 (con ↦) $u )) ])) $a )) => (con ( hcom $r (con ~>) $s $A (sys (bracket [ (con ( cof1 (con ↦) $u )) ])) $a ))
      | _ => t

  end Hcom

  section Com

    def term : Parser :=
      (annotated str "com" dim str "~>" dim str "(" (special <ident>) str "." term str ")" system term → com)

    def comRefl (t : Term) : Term :=
      match t with
      | (con ( com $r (con ~>) $r (binderParen ( $ i . $A )) $sys $a )) => (con ( com $r (con ~>) $r (binderParen ( $ i . $A )) $sys $a ))
      | _ => t

  end Com

  section VType

    def term : Parser :=
      ((annotated str "V" dim term term term → V) <|> ((annotated str "Vin" dim term → Vin) <|> (annotated str "Vproj" dim term term → Vproj)))

    def V0 (t : Term) : Term :=
      match t with
      | (con ( V (num (number 0)) $A $B $e )) => (con ( V (num (number 0)) $A $B $e ))
      | _ => t

    def V1 (t : Term) : Term :=
      match t with
      | (con ( V (num (number 1)) $A $B $e )) => (con ( V (num (number 1)) $A $B $e ))
      | _ => t

    def Vin0 (t : Term) : Term :=
      match t with
      | (con ( Vin (num (number 0)) $a )) => (con ( Vin (num (number 0)) $a ))
      | _ => t

    def Vin1 (t : Term) : Term :=
      match t with
      | (con ( Vin (num (number 1)) $a )) => (con ( Vin (num (number 1)) $a ))
      | _ => t

    def Vproj0 (t : Term) : Term :=
      match t with
      | (con ( Vproj (num (number 0)) $v $e )) => (con ( app $e (snd $v) ))
      | _ => t

    def Vproj1 (t : Term) : Term :=
      match t with
      | (con ( Vproj (num (number 1)) $v $e )) => (con ( Vproj (num (number 1)) $v $e ))
      | _ => t

  end VType

  section Sub

    def term : Parser :=
      ((annotated str "Sub" term cof term → Sub) <|> ((annotated str "inS" term → inS) <|> (annotated str "outS" term → outS)))

    def outInS (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

  end Sub

  section Glue

    def term : Parser :=
      ((annotated str "Glue" system term → Glue) <|> ((annotated str "glue" system term → glue) <|> (annotated str "unglue" cof term → unglue)))

    def unglueGlue (t : Term) : Term :=
      match t with
      | (con ( unglue $φ (con ( glue $sys $a )) )) => (con ( unglue $φ (con ( glue $sys $a )) ))
      | _ => t

  end Glue

  section Conversion

    def convRefl (t : Term) : Term :=
      match t with
      | (con ( conv $A $A )) => (con true)
      | _ => t

    def convSym (t : Term) : Term :=
      match t with
      | (con ( conv $A $B )) => (con ( conv $B $A ))
      | _ => t

    def convU (t : Term) : Term :=
      match t with
      | (con ( conv (con U) (con U) )) => (con true)
      | _ => t

    def convPi (t : Term) : Term :=
      match t with
      | (con ( conv (Pi (typedVar $ x : (binder $ A1 . $B1))) (Pi (typedVar $ x : (binder $ A2 . $B2))) )) => (con ( and (con ( conv $A2 $A1 )) (con ( conv $B1 $B2 )) ))
      | _ => t

    def convSigma (t : Term) : Term :=
      match t with
      | (con ( conv (Σ (typedVar $ x : (binder $ A1 . $B1))) (Σ (typedVar $ x : (binder $ A2 . $B2))) )) => (con ( and (con ( conv $A1 $A2 )) (con ( conv $B1 $B2 )) ))
      | _ => t

    def convPath (t : Term) : Term :=
      match t with
      | (con ( conv (PathP (binder $ i . (binder $ A1 . (binder $ a01 . $a11)))) (PathP (binder $ i . (binder $ A2 . (binder $ a02 . $a12)))) )) => (con ( and (con ( conv $A1 $A2 )) (con ( and (con ( conv $a01 $a02 )) (con ( conv $a11 $a12 )) )) ))
      | _ => t

  end Conversion

  section Neutral

    def isNeutralVar (t : Term) : Term :=
      match t with
      | (con true) => (con true)
      | _ => t

    def isNeutralApp (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def isNeutralFst (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def isNeutralSnd (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def isNeutralDApp (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

    def isNeutralCoe (t : Term) : Term :=
      match t with
      | (con ( or (neutral $A) (neutral $a) )) => (con ( or (neutral $A) (neutral $a) ))
      | _ => t

    def isNeutralHcom (t : Term) : Term :=
      match t with
      | (con ( or (neutral $A) (neutral $a) )) => (con ( or (neutral $A) (neutral $a) ))
      | _ => t

  end Neutral

  section Equiv

    def term : Parser :=
      ((annotated str "Equiv" term term → Equiv) <|> ((annotated str "idEquiv" term → idEquiv) <|> (annotated str "equivFun" term → equivFun)))

    def equivFunId (t : Term) : Term :=
      match t with
      | () => ()
      | _ => t

  end Equiv

  section Fiber

    def term : Parser :=
      (annotated str "Fiber" term term → Fiber)

  end Fiber

end CubicalTT