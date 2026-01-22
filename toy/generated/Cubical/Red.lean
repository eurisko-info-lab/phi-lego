(DImport import (modulePath CubicalTT) ;)

namespace Red

  section ExtType

    def term : Parser :=
      ((annotated str "Ext" (special <ident>) str "." term system → Ext) <|> ((annotated str "extLam" (special <ident>) str "." term → extLam) <|> (annotated str "extApp" term dim → extApp)))

    def extBeta (t : Term) : Term :=
      match t with
      | (con ( extApp (extLam (binder $ x . $body)) $r )) => (con ( extApp (extLam (binder $ x . $body)) $r ))
      | _ => t

    def extApp0 (t : Term) : Term :=
      match t with
      | (con ( extApp (extLam (binder $ x . $body)) (num (number 0)) )) => (con ( extApp (extLam (binder $ x . $body)) (num (number 0)) ))
      | _ => t

    def extApp1 (t : Term) : Term :=
      match t with
      | (con ( extApp (extLam (binder $ x . $body)) (num (number 1)) )) => (con ( extApp (extLam (binder $ x . $body)) (num (number 1)) ))
      | _ => t

    -- Test: test
    -- (con ( extApp (extLam (objBinder i . (f (var i)))) (num (number 0)) ))

  end ExtType

  section GCom

    def term : Parser :=
      ((annotated str "ghcom" dim str "~>" dim term system term → ghcom) <|> (annotated str "gcom" dim str "~>" dim str "(" (special <ident>) str "." term str ")" system term → gcom))

    def ghcomRefl (t : Term) : Term :=
      match t with
      | (con ( ghcom $r (con ~>) $r $A $sys $a )) => (con ( ghcom $r (con ~>) $r $A $sys $a ))
      | _ => t

    def gcomRefl (t : Term) : Term :=
      match t with
      | (con ( gcom $r (con ~>) $r (binderParen ( $ i . $A )) $sys $a )) => (con ( gcom $r (con ~>) $r (binderParen ( $ i . $A )) $sys $a ))
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | (con ( ghcom $r (con ~>) $s $A (bracket [ $φ (con ↦) (binder $ i . $u) ]) $a )) => (con ( ghcom $r (con ~>) $s $A (bracket [ $φ (con ↦) (binder $ i . $u) ]) $a ))
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | (con ( gcom $r (con ~>) $s (binderParen ( $ i . $A )) (bracket [ $φ (con ↦) (binder $ j . $u) ]) $a )) => (con ( gcom $r (con ~>) $s (binderParen ( $ i . $A )) (bracket [ $φ (con ↦) (binder $ j . $u) ]) $a ))
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
      | (con ( elim $e (con ( $C $ms )) (con ( intro $c $as )) )) => (con ( (( $ms $c )) $as ))
      | _ => t

    def introBdy (t : Term) : Term :=
      match t with
      | (con ( intro $c $as )) => (con ( intro $c $as ))
      | _ => t

  end Data

  section Twin

    def term : Parser :=
      (annotated str "twin" (special <ident>) (special <ident>) dim term → twin)

    def twin0 (t : Term) : Term :=
      match t with
      | (con ( twin $x $y (num (number 0)) $a )) => (con ( twin $x $y (num (number 0)) $a ))
      | _ => t

    def twin1 (t : Term) : Term :=
      match t with
      | (con ( twin $x $y (num (number 1)) $a )) => (con ( twin $x $y (num (number 1)) $a ))
      | _ => t

    def twinSym (t : Term) : Term :=
      match t with
      | (con ( twin $x $y $i (con ( twin $y $x (con ( (num (number 1)) (con -) $i )) $a )) )) => (con ( twin $x $y $i (con ( twin $y $x (con ( (num (number 1)) (con -) $i )) $a )) ))
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
      | (con ( fhcom $r (con ~>) $r $A $sys $a )) => (con ( fhcom $r (con ~>) $r $A $sys $a ))
      | _ => t

    def fhcomBdy (t : Term) : Term :=
      match t with
      | (con ( fhcom $r (con ~>) $s $A (bracket [ $φ (con ↦) (binder $ i . $u) ]) $a )) => (con ( fhcom $r (con ~>) $s $A (bracket [ $φ (con ↦) (binder $ i . $u) ]) $a ))
      | _ => t

  end FHcom

  section BoxCap

    def term : Parser :=
      ((annotated str "box" dim str "~>" dim system term → box) <|> (annotated str "cap" dim str "~>" dim system term → cap))

    def capBox (t : Term) : Term :=
      match t with
      | (con ( cap $r (con ~>) $s $sys (con ( box $r (con ~>) $s $sys' $a )) )) => (con ( cap $r (con ~>) $s $sys (con ( box $r (con ~>) $s $sys' $a )) ))
      | _ => t

    def boxBdy (t : Term) : Term :=
      match t with
      | (con ( box $r (con ~>) $s (bracket [ $φ (con ↦) $u ]) $a )) => (con ( box $r (con ~>) $s (bracket [ $φ (con ↦) $u ]) $a ))
      | _ => t

  end BoxCap

  section Coeq

    def term : Parser :=
      ((annotated str "Coeq" term term term → Coeq) <|> ((annotated str "coeqIn" term → coeqIn) <|> ((annotated str "coeqGlue" term dim → coeqGlue) <|> (annotated str "coeqElim" term term term term → coeqElim))))

    def coeqGlue0 (t : Term) : Term :=
      match t with
      | (con ( coeqGlue $a (num (number 0)) )) => (con ( coeqGlue $a (num (number 0)) ))
      | _ => t

    def coeqGlue1 (t : Term) : Term :=
      match t with
      | (con ( coeqGlue $a (num (number 1)) )) => (con ( coeqGlue $a (num (number 1)) ))
      | _ => t

    def coeqElimIn (t : Term) : Term :=
      match t with
      | (con ( coeqElim $P $h $p (coeqIn $b) )) => (con ( $h $b ))
      | _ => t

  end Coeq

  section Pushout

    def term : Parser :=
      ((annotated str "Pushout" term term term term term → Pushout) <|> ((annotated str "inl" term → inl) <|> ((annotated str "inr" term → inr) <|> ((annotated str "push" term dim → push) <|> (annotated str "pushElim" term term term term term → pushElim)))))

    def push0 (t : Term) : Term :=
      match t with
      | (con ( push $a (num (number 0)) )) => (con ( push $a (num (number 0)) ))
      | _ => t

    def push1 (t : Term) : Term :=
      match t with
      | (con ( push $a (num (number 1)) )) => (con ( push $a (num (number 1)) ))
      | _ => t

    def pushElimInl (t : Term) : Term :=
      match t with
      | (con ( pushElim $P $l $r $p (inl $a) )) => (con ( $l $a ))
      | _ => t

    def pushElimInr (t : Term) : Term :=
      match t with
      | (con ( pushElim $P $l $r $p (inr $b) )) => (con ( $r $b ))
      | _ => t

  end Pushout

end Red