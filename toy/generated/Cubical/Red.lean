/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace Red

  section ExtType

    def extBeta (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], r] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", r, Term.lit "]", body]
      | _ => t

    def extApp0 (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], .con "num" [.con "number" [.lit "0"]]] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", Term.con "num" [Term.con "number" [Term.lit "0"]], Term.lit "]", body]
      | _ => t

    def extApp1 (t : Term) : Term :=
      match t with
      | .con "extApp" [.con "app" [.var "extLam", .con "binder" [.lit "$", .var "x", .lit ".", body]], .con "num" [.con "number" [.lit "1"]]] => Term.con "subst" [Term.lit "[", Term.var "x", Term.lit ":=", Term.con "num" [Term.con "number" [Term.lit "1"]], Term.lit "]", body]
      | _ => t

    -- Test: test
    -- (extApp (extLam (objBinder i . (f $(i)))) (num (number 0)))

  end ExtType

  section GCom

    def ghcomRefl (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, .lit "~>", r_dup, A, sys, a] => a
      | _ => t

    def gcomRefl (t : Term) : Term :=
      match t with
      | .con "gcom" [r, .lit "~>", r_dup, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], sys, a] => a
      | _ => t

    def ghcomBdy (t : Term) : Term :=
      match t with
      | .con "ghcom" [r, .lit "~>", s, A, .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "i", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "i", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

    def gcomBdy (t : Term) : Term :=
      match t with
      | .con "gcom" [r, .lit "~>", s, .con "binderParen" [.lit "(", .lit "$", .var "i", .lit ".", A, .lit ")"], .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "j", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "j", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

  end GCom

  section Data

    def introElim (t : Term) : Term :=
      match t with
      | .con "elim" [e, .con "tuple" [C, ms], .con "intro" [c, as]] => Term.con "tuple" [Term.con "app" [Term.lit "(", ms, c, Term.lit ")"], as]
      | _ => t

    def introBdy (t : Term) : Term :=
      match t with
      | .con "intro" [c, as] => Term.var "bdy"
      | _ => t

  end Data

  section Twin

    def twin0 (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, .con "num" [.con "number" [.lit "0"]], a] => Term.con "subst" [Term.lit "[", y, Term.lit ":=", x, Term.lit "]", a]
      | _ => t

    def twin1 (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, .con "num" [.con "number" [.lit "1"]], a] => a
      | _ => t

    def twinSym (t : Term) : Term :=
      match t with
      | .con "twin" [x, y, i, .con "twin" [y_dup, x_dup, .con "tuple" [.con "num" [.con "number" [.lit "1"]], .lit "-", i_dup], a]] => a
      | _ => t

  end Twin

  section Restrict



  end Restrict

  section FHcom

    def fhcomRefl (t : Term) : Term :=
      match t with
      | .con "fhcom" [r, .lit "~>", r_dup, A, sys, a] => a
      | _ => t

    def fhcomBdy (t : Term) : Term :=
      match t with
      | .con "fhcom" [r, .lit "~>", s, A, .con "bracket" [.lit "[", φ, .lit "↦", .con "binder" [.lit "$", .var "i", .lit ".", u], .lit "]"], a] => Term.con "subst" [Term.lit "[", Term.var "i", Term.lit ":=", s, Term.lit "]", u]
      | _ => t

  end FHcom

  section BoxCap

    def capBox (t : Term) : Term :=
      match t with
      | .con "cap" [r, .lit "~>", s, sys, .con "box" [r_dup, .lit "~>", s_dup, sys', a]] => a
      | _ => t

    def boxBdy (t : Term) : Term :=
      match t with
      | .con "box" [r, .lit "~>", s, .con "bracket" [.lit "[", φ, .lit "↦", u, .lit "]"], a] => u
      | _ => t

  end BoxCap

  section Coeq

    def coeqGlue0 (t : Term) : Term :=
      match t with
      | .con "coeqGlue" [a, .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "coeqIn", Term.con "tuple" [Term.var "f", a]]
      | _ => t

    def coeqGlue1 (t : Term) : Term :=
      match t with
      | .con "coeqGlue" [a, .con "num" [.con "number" [.lit "1"]]] => Term.con "app" [Term.var "coeqIn", Term.con "tuple" [Term.var "g", a]]
      | _ => t

    def coeqElimIn (t : Term) : Term :=
      match t with
      | .con "coeqElim" [P, h, p, .con "app" [.var "coeqIn", b]] => Term.con "tuple" [h, b]
      | _ => t

  end Coeq

  section Pushout

    def push0 (t : Term) : Term :=
      match t with
      | .con "push" [a, .con "num" [.con "number" [.lit "0"]]] => Term.con "app" [Term.var "inl", Term.con "tuple" [Term.var "f", a]]
      | _ => t

    def push1 (t : Term) : Term :=
      match t with
      | .con "push" [a, .con "num" [.con "number" [.lit "1"]]] => Term.con "app" [Term.var "inr", Term.con "tuple" [Term.var "g", a]]
      | _ => t

    def pushElimInl (t : Term) : Term :=
      match t with
      | .con "pushElim" [P, l, r, p, .con "app" [.var "inl", a]] => Term.con "tuple" [l, a]
      | _ => t

    def pushElimInr (t : Term) : Term :=
      match t with
      | .con "pushElim" [P, l, r, p, .con "app" [.var "inr", b]] => Term.con "tuple" [r, b]
      | _ => t

  end Pushout

end Red