/-
  Lego.Interp: Bidirectional Grammar Interpretation

  The grammar is itself an Iso: TokenStream ⇌ Term
  This is not special - it's the same structure as any rule-based language.
-/

import Lego.Algebra

namespace Lego

/-! ## Grammar as Iso -/

/-- Parsing state -/
structure ParseState where
  tokens : TokenStream
  binds  : List (String × Term)
  deriving Repr, Nonempty

/-- Grammar productions map -/
abbrev Productions := List (String × GrammarExpr)

/-! ## Helper functions -/

def combineSeq (t1 t2 : Term) : Term :=
  match t1, t2 with
  | .con "seq" ts, .con "seq" us => .con "seq" (ts ++ us)
  | .con "seq" ts, t => .con "seq" (ts ++ [t])
  | t, .con "seq" us => .con "seq" (t :: us)
  | .con "unit" [], t => t
  | t, .con "unit" [] => t
  | t1, t2 => .con "seq" [t1, t2]

def splitSeq (t : Term) : Term × Term :=
  match t with
  | .con "seq" (h :: rest) => (h, .con "seq" rest)
  | t => (t, .con "unit" [])

def wrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con "seq" ts => .con name ts
  | _ => .con name [t]

def unwrapNode (name : String) (t : Term) : Term :=
  match t with
  | .con n ts => if n == name then .con "seq" ts else t
  | _ => t

/-! ## Interpretation -/

/-- Result of grammar interpretation -/
abbrev ParseResult := Option (Term × ParseState)

/-- Interpret a GrammarExpr for parsing (forward direction) -/
partial def parseGrammar (prods : Productions) (g : GrammarExpr) (st : ParseState) : ParseResult :=
  match g with
  | .mk .empty => some (.con "unit" [], st)

  | .mk (.lit s) =>
    match st.tokens with
    | .lit l :: rest => if l == s then some (.lit s, { st with tokens := rest }) else none
    | .sym l :: rest => if l == s then some (.lit s, { st with tokens := rest }) else none
    | .ident l :: rest => if l == s then some (.lit s, { st with tokens := rest }) else none
    | _ => none

  | .mk (.ref name) =>
    -- Handle built-in token types
    if name == "TOKEN.ident" then
      match st.tokens with
      | .ident s :: rest => some (.var s, { st with tokens := rest })
      | _ => none
    else if name == "TOKEN.string" then
      match st.tokens with
      | .lit s :: rest => some (.lit s, { st with tokens := rest })
      | _ => none
    else if name == "TOKEN.number" then
      match st.tokens with
      | .number s :: rest => some (.lit s, { st with tokens := rest })
      | _ => none
    else
      match prods.find? (·.1 == name) with
      | some (_, g') => parseGrammar prods g' st
      | none => none

  | .mk (.seq g1 g2) => do
    let (t1, st1) ← parseGrammar prods g1 st
    let (t2, st2) ← parseGrammar prods g2 st1
    pure (combineSeq t1 t2, st2)

  | .mk (.alt g1 g2) =>
    parseGrammar prods g1 st <|> parseGrammar prods g2 st

  | .mk (.star g') =>
    let rec go (acc : List Term) (st : ParseState) : ParseResult :=
      match parseGrammar prods g' st with
      | some (t, st') => go (acc ++ [t]) st'
      | none => some (.con "seq" acc, st)
    go [] st

  | .mk (.bind x g') => do
    let (t, st') ← parseGrammar prods g' st
    pure (t, { st' with binds := (x, t) :: st'.binds })

  | .mk (.node name g') => do
    let (t, st') ← parseGrammar prods g' st
    pure (wrapNode name t, st')

/-- Interpret a GrammarExpr for printing (backward direction) -/
partial def printGrammar (prods : Productions) (g : GrammarExpr) (t : Term) (acc : List Token) : Option (List Token) :=
  match g with
  | .mk .empty => some acc

  | .mk (.lit s) => some (acc ++ [.sym s])

  | .mk (.ref name) =>
    match prods.find? (·.1 == name) with
    | some (_, g') => printGrammar prods g' t acc
    | none => none

  | .mk (.seq g1 g2) =>
    let (t1, t2) := splitSeq t
    match printGrammar prods g1 t1 acc with
    | some acc' => printGrammar prods g2 t2 acc'
    | none => none

  | .mk (.alt g1 g2) =>
    printGrammar prods g1 t acc <|> printGrammar prods g2 t acc

  | .mk (.star g') =>
    match t with
    | .con "seq" ts =>
      ts.foldlM (fun acc' t' => printGrammar prods g' t' acc') acc
    | _ => some acc

  | .mk (.bind _ g') => printGrammar prods g' t acc

  | .mk (.node name g') =>
    let t' := unwrapNode name t
    printGrammar prods g' t' acc

/-! ## Language Interpretation -/

/-- A Language gives us two Isos:
    1. Grammar: TokenStream ⇌ Term (syntax)
    2. Rules:   Term ⇌ Term        (semantics) -/
structure LangInterp where
  /-- Parse: tokens → term -/
  parse : TokenStream → Option Term
  /-- Print: term → tokens -/
  print : Term → Option TokenStream
  /-- Normalize: term → term (via rules) -/
  normalize : Term → Term
  /-- Expand: term → term (reverse normalize) -/
  expand : Term → Term

/-- Build interpreter from a Language -/
def Language.toInterp (lang : Language) (startProd : String) : LangInterp where
  parse := fun tokens =>
    let prods := lang.allGrammar
    let st : ParseState := { tokens := tokens, binds := [] }
    match prods.find? (·.1 == startProd) with
    | some (_, g) =>
      match parseGrammar prods g st with
      | some (t, st') => if st'.tokens.isEmpty then some t else none
      | none => none
    | none => none

  print := fun t =>
    let prods := lang.allGrammar
    match prods.find? (·.1 == startProd) with
    | some (_, g) => printGrammar prods g t []
    | none => none

  normalize := fun t =>
    let reducer := lang.interpreter
    reducer.forward t |>.getD t

  expand := fun t =>
    let reducer := lang.interpreter
    reducer.backward t |>.getD t

/-- Convert grammar interpretation to an Iso -/
def grammarToIso (prods : Productions) (startProd : String) : Iso TokenStream Term where
  forward := fun tokens =>
    let st : ParseState := { tokens := tokens, binds := [] }
    match prods.find? (·.1 == startProd) with
    | some (_, g) =>
      match parseGrammar prods g st with
      | some (t, st') => if st'.tokens.isEmpty then some t else none
      | none => none
    | none => none
  backward := fun t =>
    match prods.find? (·.1 == startProd) with
    | some (_, g) => printGrammar prods g t []
    | none => none

end Lego
