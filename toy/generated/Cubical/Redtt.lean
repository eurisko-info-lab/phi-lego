namespace Redtt

  -- Token lexer: Token
  def digit : Parser :=
    (char '0' <|> (char '1' <|> (char '2' <|> (char '3' <|> (char '4' <|> (char '5' <|> (char '6' <|> (char '7' <|> (char '8' <|> char '9')))))))))
  def lower : Parser :=
    (char 'a' <|> (char 'b' <|> (char 'c' <|> (char 'd' <|> (char 'e' <|> (char 'f' <|> (char 'g' <|> (char 'h' <|> (char 'i' <|> (char 'j' <|> (char 'k' <|> (char 'l' <|> (char 'm' <|> (char 'n' <|> (char 'o' <|> (char 'p' <|> (char 'q' <|> (char 'r' <|> (char 's' <|> (char 't' <|> (char 'u' <|> (char 'v' <|> (char 'w' <|> (char 'x' <|> (char 'y' <|> char 'z')))))))))))))))))))))))))
  def upper : Parser :=
    (char 'A' <|> (char 'B' <|> (char 'C' <|> (char 'D' <|> (char 'E' <|> (char 'F' <|> (char 'G' <|> (char 'H' <|> (char 'I' <|> (char 'J' <|> (char 'K' <|> (char 'L' <|> (char 'M' <|> (char 'N' <|> (char 'O' <|> (char 'P' <|> (char 'Q' <|> (char 'R' <|> (char 'S' <|> (char 'T' <|> (char 'U' <|> (char 'V' <|> (char 'W' <|> (char 'X' <|> (char 'Y' <|> char 'Z')))))))))))))))))))))))))
  def greek : Parser :=
    (char 'α' <|> (char 'β' <|> (char 'γ' <|> (char 'δ' <|> (char 'ε' <|> (char 'ζ' <|> (char 'η' <|> (char 'θ' <|> (char 'ι' <|> (char 'κ' <|> (char 'λ' <|> (char 'μ' <|> (char 'ν' <|> (char 'ξ' <|> (char 'ο' <|> (char 'π' <|> (char 'ρ' <|> (char 'σ' <|> (char 'τ' <|> (char 'υ' <|> (char 'φ' <|> (char 'χ' <|> (char 'ψ' <|> (char 'ω' <|> (char 'Α' <|> (char 'Β' <|> (char 'Γ' <|> (char 'Δ' <|> (char 'Ε' <|> (char 'Ζ' <|> (char 'Η' <|> (char 'Θ' <|> (char 'Ι' <|> (char 'Κ' <|> (char 'Λ' <|> (char 'Μ' <|> (char 'Ν' <|> (char 'Ξ' <|> (char 'Ο' <|> (char 'Π' <|> (char 'Ρ' <|> (char 'Σ' <|> (char 'Τ' <|> (char 'Υ' <|> (char 'Φ' <|> (char 'Χ' <|> (char 'Ψ' <|> char 'Ω')))))))))))))))))))))))))))))))))))))))))))))))
  def mathbb : Parser :=
    (char '𝕀' <|> (char '𝔽' <|> char '𝕊'))
  def mathsym : Parser :=
    (char '≈' <|> (char '≅' <|> (char '≤' <|> (char '≥' <|> (char '∘' <|> (char '⊗' <|> (char '⊙' <|> (char '∧' <|> (char '∨' <|> char '³')))))))))
  def alpha : Parser :=
    (lower <|> (upper <|> (greek <|> (mathbb <|> (mathsym <|> char '_')))))
  def symch : Parser :=
    (char '(' <|> (char ')' <|> (char '[' <|> (char ']' <|> (char '{' <|> (char '}' <|> (char '<' <|> (char '>' <|> (char ':' <|> (char ';' <|> (char ',' <|> (char '.' <|> (char '|' <|> (char '!' <|> (char '?' <|> (char '@' <|> (char '#' <|> (char '$' <|> (char '%' <|> (char '^' <|> (char '&' <|> (char '*' <|> (char '+' <|> (char '-' <|> (char '=' <|> (char '~' <|> (char '/' <|> (char '\\' <|> (char '→' <|> (char '←' <|> (char '↔' <|> (char '⊕' <|> (char '⊢' <|> (char '×' <|> (char 'λ' <|> (char '∂' <|> (char '∀' <|> (char '∃' <|> (char '★' <|> (char '☆' <|> (char '⦉' <|> (char '⦊' <|> (char '«' <|> (char '»' <|> char '`'))))))))))))))))))))))))))))))))))))))))))))
  def strchar : Parser :=
    (alt char '\\' escape | printable)
  def escape : Parser :=
    (char '"' <|> (char '\\' <|> (char 'n' <|> (char 't' <|> (char 'r' <|> char '\'')))))
  def printable : Parser :=
    (alpha <|> (digit <|> (symch <|> char ' ')))
  def ws : Parser :=
    (char ' ' <|> (char '\t' <|> (char '\n' <|> char '\r')))
  def nonnl : Parser :=
    (alpha <|> (digit <|> (symch <|> (char ' ' <|> (char '\t' <|> (char '\'' <|> char '"'))))))
  def sym : Parser :=
    symch

  section File

    def file : Parser :=
      many (topdecl)

    def topdecl : Parser :=
      (importdecl <|> (defndecl <|> (datadecl <|> (metadecl <|> str "opaque"))))

  end File

  section Imports

    def name : Parser :=
      (ident <|> (str "data" <|> (str "def" <|> (str "import" <|> (str "public" <|> (str "where" <|> (str "let" <|> (str "in" <|> (str "elim" <|> (str "opaque" <|> (str "private" <|> str "meta")))))))))))

  end Imports

  section Definitions

    def defmodifiers : Parser :=
      many ((group ( (str "opaque" <|> str "private") )))

    def defndecl : Parser :=
      (alt defmodifiers str "def" defname defscheme str "=" expr | str "quit")

    def defscheme : Parser :=
      (alt defargs str ":" expr | defargs)

    def defident : Parser :=
      (alt ident str "~" ident | ident)

    def defnamesuffix : Parser :=
      (alt str "→" ident | (alt str "→" | str "~" ident))

    def defargs : Parser :=
      many (defarg)

    def defarg : Parser :=
      (alt str "(" (plus ident +) str ":" expr str ")" | ident)

  end Definitions

  section Meta

    def ltr : Parser :=
      (alt str "⦉" | str "<" str ":")

    def rtr : Parser :=
      (alt str "⦊" | str ":" str ">")

    def llgl : Parser :=
      (alt str "«" | str "<" str "<")

    def rrgl : Parser :=
      (alt str "»" | str ">" str ">")

    def mlcmd : Parser :=
      (alt str "let" ident str "=" mlcmd str "in" mlcmd | (alt str "let" ident str "=" mlcmd | mlcmdseq))

    def mlcmdatom : Parser :=
      (alt str "fun" ident str "→" mlcmd | (alt str "check" mlval str ":" mlval | (alt str "!" mlval | (alt str "print" optional (str "normalize") mlcmdatom | (alt str "normalize" mlcmdatom | (alt str "debug" optional (ident) | (str "quit" <|> (alt llgl defndecl rrgl | (alt llgl datadecl rrgl | (alt llgl expr rrgl | (mlval <|> (alt str "(" mlcmd str ")" | str "begin" mlcmd str "end"))))))))))))

    def mlval : Parser :=
      (alt str "{" mlcmd str "}" | (alt str "<" mlval many ((group ( str "," mlval ))) str ">" | (string <|> ident)))

  end Meta

  section DataTypes

    def righttack : Parser :=
      (alt str "⊢" | str "!" str "-")

    def datacons : Parser :=
      many (datacon)

    def dataconname : Parser :=
      (ident <|> (str "*" <|> (str "★" <|> (str "☆" <|> (str "ε" <|> str "η")))))

    def dataconargs : Parser :=
      many (dataconarg)

  end DataTypes

  section Expr

    def expr : Parser :=
      (lam <|> (lamstar <|> (lampair <|> (lamelim <|> (letin <|> (coeexpr <|> (compexpr <|> (hcomexpr <|> (vproj <|> (piexpr <|> (sigmaexpr <|> (arrowexpr <|> appexpr))))))))))))

  end Expr

  section Lambda

    def binders : Parser :=
      (plus binder +)

    def binder : Parser :=
      (alt str "(" (plus ident +) str ":" expr str ")" | (alt str "(" pattern many ((group ( str "," pattern ))) str ")" | (alt str "[" pattern str "," str "]" | (alt str "[" str "," str "]" | (bindername <|> (str "_" <|> str "*"))))))

    def bindernameplus : Parser :=
      (alt str "+" ident | str "+" number)

    def pattern : Parser :=
      (alt str "(" pattern many ((group ( str "," pattern ))) str ")" | (ident <|> (str "_" <|> (str "*" <|> (alt str "[" pattern str "," str "]" | str "[" str "," str "]")))))

  end Lambda

  section Let

    def letpat : Parser :=
      (alt str "(" pattern many ((group ( str "," pattern ))) str ")" | letname)

    def letnamesuffix : Parser :=
      (alt str "→" ident | str "→")

    def letinvalue : Parser :=
      (letin <|> (lam <|> (lamstar <|> (lampair <|> (lamelim <|> (compexpr <|> (hcomexpr <|> (coeexpr <|> (piexpr <|> (sigmaexpr <|> (arrowexpr <|> appexpr)))))))))))

  end Let

  section Types

    def arrowexpr : Parser :=
      (alt appexpr str "→" expr | (alt appexpr str "×" expr | appexpr))

  end Types

  section Application

    def appitem : Parser :=
      (projsuffix <|> projexpr)

    def projsuffix : Parser :=
      (alt str "." ident | levelspec)

  end Application

  section Atoms

    def atom : Parser :=
      (alt str "(" expr str ")" | (pair <|> (pathtype <|> (rawterm <|> (hole <|> (namedhole <|> (alt str "type" optional (levelspec) | (str "𝕀" <|> (alt str "pre" optional (levelspec) | (alt str "kan" optional (levelspec) | (str "cof" <|> (pathsugar <|> (pathdsugar <|> (str "refl" <|> (fibertype <|> (isequiv <|> (equivtype <|> (idequiv <|> (isotoequiv <|> (alt str "is-contr" optional (levelspec) | (alt str "is-prop" optional (levelspec) | (alt str "is-set" optional (levelspec) | (str "has-hlevel" <|> (vtype <|> (vin <|> (str "trans" <|> (str "symm" <|> (symmfiller <|> (funext <|> (apd <|> (str "ap" <|> (str "cong" <|> (squaretype <|> (connectionor <|> (connectionand <|> (connectionboth <|> (weakconnor <|> (weakconnand <|> (elimexpr <|> (boxexpr <|> (capexpr <|> (runml <|> (str "_" <|> (number <|> (ihident <|> (ident <|> (str "*" <|> (str "★" <|> str "☆"))))))))))))))))))))))))))))))))))))))))))))))))

    def hole : Parser :=
      str "?"

    def ihident : Parser :=
      (alt ident str "~" ident | (alt ident str "+" number | (alt ident str "+" ident | ident str "-" ident)))

  end Atoms

  section PathTypes

    def dimvars : Parser :=
      (plus ident +)

    def cofibclause : Parser :=
      (alt many (faceor) face optional (ident) str "→" expr | many (faceor) face)

    def face : Parser :=
      (alt ident str "=" dimexpr | (alt str "∂" str "[" dimvars str "]" | (alt str "boundary" str "[" dimvars str "]" | str "(" many (faceor) face str ")")))

    def dimexpr : Parser :=
      (number <|> ident)

    def iterm : Parser :=
      (number <|> ident)

  end PathTypes

  section Cubical

    def compexpr : Parser :=
      (alt str "comp" projexpr projexpr projexpr str "in" expr constraints | str "comp" projexpr projexpr projexpr constraints)

    def hcomexpr : Parser :=
      (alt str "hcom" projexpr projexpr projexpr str "in" expr constraints | str "hcom" projexpr projexpr projexpr constraints)

  end Cubical

  section Universe



  end Universe

  section VTypes



  end VTypes

  section EquivTypes



  end EquivTypes

  section FunExtApd



  end FunExtApd

  section Connections



  end Connections

  section SquareTypes



  end SquareTypes

  section Eliminators

    def elimblock : Parser :=
      (alt str "[" elimcases str "]" | str "with" elimcases str "end")

    def elimpat : Parser :=
      (alt ident optional (elimpatargs) | (str "*" <|> (alt str "★" optional (elimpatargs) | (alt str "☆" optional (elimpatargs) | (alt str "ε" | str "η" optional (elimpatargs))))))

    def elimpatargs : Parser :=
      many (elimpatarg)

    def elimpatarg : Parser :=
      (alt str "(" elimpat optional ((group ( str "→" ihbinding ))) str ")" | elimpat)

    def ihbinding : Parser :=
      (alt ident str "+" number | (alt ident str "+" ident | (alt ident str "-" ident | ident)))

  end Eliminators

  section BoxCap



  end BoxCap

  section RawTerms

    def sexpr : Parser :=
      (ident <|> (number <|> (alt str "@" | str "(" sexprlist str ")")))

    def sexprlist : Parser :=
      many (sexpr)

  end RawTerms

  section RunML

    def beta-lam (t : Term) : Term :=
      match t with
      | (App (Lam $x $body) $arg) => (subst $body $x $arg)
      | _ => t

    def beta-fst (t : Term) : Term :=
      match t with
      | (Fst (Cons $a $b)) => $a
      | _ => t

    def beta-snd (t : Term) : Term :=
      match t with
      | (Snd (Cons $a $b)) => $b
      | _ => t

    def beta-let (t : Term) : Term :=
      match t with
      | (Let $x $val $body) => (subst $body $x $val)
      | _ => t

    def beta-extapp-0 (t : Term) : Term :=
      match t with
      | (ExtApp (ExtLam $i $body) (Dim0)) => (subst $body $i (Dim0))
      | _ => t

    def beta-extapp-1 (t : Term) : Term :=
      match t with
      | (ExtApp (ExtLam $i $body) (Dim1)) => (subst $body $i (Dim1))
      | _ => t

    def coe-refl (t : Term) : Term :=
      match t with
      | (Coe $r $r $ty $tm) => $tm
      | _ => t

    def hcom-refl (t : Term) : Term :=
      match t with
      | (HCom $r $r $ty $cap $sys) => $cap
      | _ => t

    def coe-const (t : Term) : Term :=
      match t with
      | (Coe $r $r' (const $A) $tm) => $tm
      | _ => t

    def path-app-refl (t : Term) : Term :=
      match t with
      | (ExtApp (Refl $a) $r) => $a
      | _ => t

    def path-0 (t : Term) : Term :=
      match t with
      | (ExtApp (ExtLam $i $body) (Dim0)) => (subst $body $i (Dim0))
      | _ => t

    def path-1 (t : Term) : Term :=
      match t with
      | (ExtApp (ExtLam $i $body) (Dim1)) => (subst $body $i (Dim1))
      | _ => t

    def v-0 (t : Term) : Term :=
      match t with
      | (V (Dim0) $ty0 $ty1 $equiv) => $ty0
      | _ => t

    def v-1 (t : Term) : Term :=
      match t with
      | (V (Dim1) $ty0 $ty1 $equiv) => $ty1
      | _ => t

    def vin-0 (t : Term) : Term :=
      match t with
      | (VIn (Dim0) $tm0 $tm1) => $tm0
      | _ => t

    def vin-1 (t : Term) : Term :=
      match t with
      | (VIn (Dim1) $tm0 $tm1) => $tm1
      | _ => t

    def elim-intro (t : Term) : Term :=
      match t with
      | (Elim (Intro $dlbl $clbl $args) $mot $clauses) => (apply-clause (lookup $clbl $clauses) $args)
      | _ => t

    -- Test: test
    -- ()

    -- Test: test
    -- (import $(prelude) $(path))

    -- Test: test
    -- (def $(id) $(x) $(x))

    -- Test: test
    -- (def $(id) (x $(COLON) $(A)) $(COLON) $(A) $(x))

  end RunML

end Redtt