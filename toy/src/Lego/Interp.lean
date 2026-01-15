/-
  Lego.Interp: Bidirectional Grammar Interpretation (Parser)

  The grammar is an Iso: TokenStream ⇌ Term

  This module contains only the syntax-level grammar engine.
  For the character-level (tokenizer) engine, see Token.lean.

  Helper functions (combineSeq, splitSeq, wrapNode, unwrapNode) are
  imported from BootstrapRules where they are defined alongside the
  equivalent rewrite rules from Bootstrap.lego.
-/

import Lego.Algebra
import TokenEngine
import BootstrapRules

namespace Lego

-- Re-export from TokenEngine
open Lego.Generated (Productions)
export Lego.Generated (Productions tokenizeWithGrammar lexGrammar)

-- Import helper functions from generated rules module
open Lego.Generated.Bootstrap (combineSeq splitSeq wrapNode unwrapNode)

/-! ## Parsing State -/

/-- Parsing state -/
structure ParseState where
  tokens : TokenStream
  binds  : List (String × Term)
  deriving Repr, Nonempty

/-- Result of grammar interpretation -/
abbrev ParseResult := Option (Term × ParseState)

/-! ## Token-level Grammar Engine (Parser) -/

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
    -- Handle built-in token types (TOKEN.*)
    if name.startsWith "TOKEN." then
      let tokType := name.drop 6  -- Remove "TOKEN." prefix
      match tokType, st.tokens with
      | "ident",   .ident s :: rest  => some (.var s, { st with tokens := rest })
      | "string",  .lit s :: rest    => some (.lit s, { st with tokens := rest })
      | "char",    .lit s :: rest    =>
        -- Match 'x' character literals
        if s.startsWith "'" && s.endsWith "'" then
          some (.lit s, { st with tokens := rest })
        else none
      | "number",  .number s :: rest => some (.lit s, { st with tokens := rest })
      | "sym",     .sym s :: rest    => some (.var s, { st with tokens := rest })
      | "special", .sym s :: rest    =>
        -- Match any <...> token
        if s.startsWith "<" && s.endsWith ">" then
          some (.var s, { st with tokens := rest })
        else none
      | _, _ => none
    else
      -- Regular production reference
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

/-! ## Parameterized Grammar Interpretation (AST typeclass) -/

/-- ParseState parameterized over AST type -/
structure ParseStateT (α : Type) where
  tokens : TokenStream
  binds : List (String × α) := []

/-- Result of parameterized grammar interpretation -/
abbrev ParseResultT (α : Type) := Option (α × ParseStateT α)

/-- Combine two AST nodes into a sequence (parameterized) -/
def combineSeqT [AST α] (t1 t2 : α) : α := AST.seq t1 t2

/-- Wrap with node name (parameterized) -/
def wrapNodeT [AST α] (name : String) (inner : α) : α := AST.con name [inner]

/-- Parameterized grammar parser: builds into any AST type. -/
partial def parseGrammarT [AST α] (prods : Productions) (g : GrammarExpr)
    (st : ParseStateT α) : ParseResultT α :=
  match g with
  | .mk .empty => some (AST.unit, st)

  | .mk (.lit s) =>
    match st.tokens with
    | .lit l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
    | .sym l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
    | .ident l :: rest => if l == s then some (AST.lit s, { st with tokens := rest }) else none
    | _ => none

  | .mk (.ref name) =>
    -- Handle built-in token types (TOKEN.*)
    if name.startsWith "TOKEN." then
      let tokType := name.drop 6
      match tokType, st.tokens with
      | "ident",   .ident s :: rest  => some (AST.var s, { st with tokens := rest })
      | "string",  .lit s :: rest    => some (AST.lit s, { st with tokens := rest })
      | "char",    .lit s :: rest    =>
        if s.startsWith "'" && s.endsWith "'" then
          some (AST.lit s, { st with tokens := rest })
        else none
      | "number",  .number s :: rest => some (AST.lit s, { st with tokens := rest })
      | "special", .sym s :: rest    =>
        if s.startsWith "<" && s.endsWith ">" then
          some (AST.var s, { st with tokens := rest })
        else none
      | _, _ => none
    else
      match prods.find? (·.1 == name) with
      | some (_, g') => parseGrammarT prods g' st
      | none => none

  | .mk (.seq g1 g2) =>
    match parseGrammarT prods g1 st with
    | some (t1, st1) =>
      match parseGrammarT prods g2 st1 with
      | some (t2, st2) => some (combineSeqT t1 t2, st2)
      | none => none
    | none => none

  | .mk (.alt g1 g2) =>
    parseGrammarT prods g1 st <|> parseGrammarT prods g2 st

  | .mk (.star g') =>
    let rec go (acc : List α) (st : ParseStateT α) : ParseResultT α :=
      match parseGrammarT prods g' st with
      | some (t, st') => go (acc ++ [t]) st'
      | none => some (AST.con "seq" acc, st)
    go [] st

  | .mk (.bind x g') =>
    match parseGrammarT prods g' st with
    | some (t, st') => some (t, { st' with binds := (x, t) :: st'.binds })
    | none => none

  | .mk (.node name g') =>
    match parseGrammarT prods g' st with
    | some (t, st') => some (wrapNodeT name t, st')
    | none => none

/-- Convenience: parse with specific AST target -/
def parseGrammarAs (α : Type) [AST α] (prods : Productions) (g : GrammarExpr)
    (tokens : TokenStream) : Option α :=
  match parseGrammarT prods g ⟨tokens, []⟩ with
  | some (result, _) => some result
  | none => none

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
