(DImport import (modulePath CubicalTT) ;)

namespace Red

  section ExtType

    def term : Parser :=
      ((annotated str "Ext" (special <ident>) str "." term system → Ext) <|> ((annotated str "extLam" (special <ident>) str "." term → extLam) <|> (annotated str "extApp" term dim → extApp)))

    def extBeta (t : Term) : Term :=
      match t with
      | (extApp (extLam (binder $ x . $body)) $r) => (subst [ $x := $r ] $body)
      | _ => t

    def extApp0 (t : Term) : Term :=
      match t with
      | (extApp (extLam (binder $ x . $body)) (num (number 0))) => (subst [ $x := (num (number 0)) ] $body)
      | _ => t

    def extApp1 (t : Term) : Term :=
      match t with
      | (extApp (extLam (binder $ x . $body)) (num (number 1))) => (subst [ $x := (num (number 1)) ] $body)
      | _ => t

    -- Test: test
    -- (extApp (extLam (objBinder i . (f $(i)))) (num (number 0)))

  end ExtType

  section GCom

    def term : Parser :=
      ((annotated str "ghcom" dim str "~>" dim term system term → ghcom) <|> (annotated str "gcom" dim str "~>" dim str "(" (special <ident>) str "." term str ")" system term → gcom))

    def ghcomRefl (t : Term) : Term :=
      match t with
      | (ghcom $r (~>) $r $A $sys $a) => $a
      | _ => t

    def gcomRefl (t : Term) : Term :=
      match t with
      | (gcom $r (~>) $r (binderParen ( $ i . $A )) $sys $a) => $a
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | (ghcom $r (~>) $s $A (bracket [ $φ (↦) (binder $ i . $u) ]) $a) => (subst [ $i := $s ] $u)
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | (gcom $r (~>) $s (binderParen ( $ i . $A )) (bracket [ $φ (↦) (binder $ j . $u) ]) $a) => (subst [ $j := $s ] $u)
      | _ => t

  end GCom

  section Data

    def decl : Parser :=
      (annotated str "data" (special <ident>) params str "where" constrs → data)

    def params : Parser :=
      (annotated str "(" (special <ident>) str ":" term many (str ")") → params)

    def constrs : Parser :=
      (annotated many (constr) → constrs)

    def constr : Parser :=
      (annotated str "|" (special <ident>) str ":" term optional (bounds) → constr)

    def bounds : Parser :=
      (annotated str "[" many (bound) str "]" → bounds)

    def bound : Parser :=
      (annotated cof str "↦" term → bound)

    def introElim (t : Term) : Term :=
      match t with
      | (elim $e ($C $ms) (intro $c $as)) => ((( $ms $c )) $as)
      | _ => t

    def introBdy (t : Term) : Term :=
      match t with
      | (intro $c $as) => $bdy
      | _ => t

  end Data

  section Twin

    def term : Parser :=
      (annotated str "twin" (special <ident>) (special <ident>) dim term → twin)

    def twin0 (t : Term) : Term :=
      match t with
      | (twin $x $y (num (number 0)) $a) => (subst [ $y := $x ] $a)
      | _ => t

    def twin1 (t : Term) : Term :=
      match t with
      | (twin $x $y (num (number 1)) $a) => $a
      | _ => t

    def twinSym (t : Term) : Term :=
      match t with
      | (twin $x $y $i (twin $y $x ((num (number 1)) (-) $i) $a)) => $a
      | _ => t

  end Twin

  section Restrict

    def term : Parser :=
      (annotated term str "↾" cof → restrict)

  end Restrict

  section FHcom

    def term : Parser :=
      (annotated str "fhcom" dim str "~>" dim term system term → fhcom)

    def fhcomRefl (t : Term) : Term :=
      match t with
      | (fhcom $r (~>) $r $A $sys $a) => $a
      | _ => t

    def fhcomBdy (t : Term) : Term :=
      match t with
      | (fhcom $r (~>) $s $A (bracket [ $φ (↦) (binder $ i . $u) ]) $a) => (subst [ $i := $s ] $u)
      | _ => t

  end FHcom

  section BoxCap

    def term : Parser :=
      ((annotated str "box" dim str "~>" dim system term → box) <|> (annotated str "cap" dim str "~>" dim system term → cap))

    def capBox (t : Term) : Term :=
      match t with
      | (cap $r (~>) $s $sys (box $r (~>) $s $sys' $a)) => $a
      | _ => t

    def boxBdy (t : Term) : Term :=
      match t with
      | (box $r (~>) $s (bracket [ $φ (↦) $u ]) $a) => $u
      | _ => t

  end BoxCap

  section Coeq

    def term : Parser :=
      ((annotated str "Coeq" term term term → Coeq) <|> ((annotated str "coeqIn" term → coeqIn) <|> ((annotated str "coeqGlue" term dim → coeqGlue) <|> (annotated str "coeqElim" term term term term → coeqElim))))

    def coeqGlue0 (t : Term) : Term :=
      match t with
      | (coeqGlue $a (num (number 0))) => (coeqIn ($f $a))
      | _ => t

    def coeqGlue1 (t : Term) : Term :=
      match t with
      | (coeqGlue $a (num (number 1))) => (coeqIn ($g $a))
      | _ => t

    def coeqElimIn (t : Term) : Term :=
      match t with
      | (coeqElim $P $h $p (coeqIn $b)) => ($h $b)
      | _ => t

  end Coeq

  section Pushout

    def term : Parser :=
      ((annotated str "Pushout" term term term term term → Pushout) <|> ((annotated str "inl" term → inl) <|> ((annotated str "inr" term → inr) <|> ((annotated str "push" term dim → push) <|> (annotated str "pushElim" term term term term term → pushElim)))))

    def push0 (t : Term) : Term :=
      match t with
      | (push $a (num (number 0))) => (inl ($f $a))
      | _ => t

    def push1 (t : Term) : Term :=
      match t with
      | (push $a (num (number 1))) => (inr ($g $a))
      | _ => t

    def pushElimInl (t : Term) : Term :=
      match t with
      | (pushElim $P $l $r $p (inl $a)) => ($l $a)
      | _ => t

    def pushElimInr (t : Term) : Term :=
      match t with
      | (pushElim $P $l $r $p (inr $b)) => ($r $b)
      | _ => t

  end Pushout

end Red