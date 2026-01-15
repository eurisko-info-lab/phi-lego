/-
  Lego.Interp: Bidirectional Grammar Interpretation

  The grammar is itself an Iso - same algebra for both levels:
  - Token level:  CharStream ⇌ TokenStream (lexer)
  - Syntax level: TokenStream ⇌ Term (parser)

  Helper functions (combineSeq, splitSeq, wrapNode, unwrapNode) are
  imported from BootstrapRules where they are defined alongside the
  equivalent rewrite rules from Bootstrap.lego.
-/

import Lego.Algebra
import BootstrapRules

namespace Lego

-- Import helper functions from generated rules module
open Lego.Generated.Bootstrap (combineSeq splitSeq wrapNode unwrapNode)

/-! ## Common Types -/

/-- Grammar productions map -/
abbrev Productions := List (String × GrammarExpr)

/-! ## Character Stream (for lexer) -/

abbrev CharStream := List Char

/-- Lexer state -/
structure LexState where
  chars : CharStream
  acc   : String := ""  -- accumulated characters for current token
  deriving Repr

/-- Result of lexing one token -/
abbrev LexResult := Option (String × LexState)

/-! ## Token-level Grammar Interpretation (Lexer) -/

/-- Extract character from 'x' format literal -/
def extractCharLit (s : String) : Option Char :=
  if s.startsWith "'" && s.endsWith "'" && s.length == 3 then
    s.toList[1]?
  else
    none

/-- Interpret a GrammarExpr for lexing (CharStream → String)
    Single quotes in grammar match single characters -/
partial def lexGrammar (prods : Productions) (g : GrammarExpr) (st : LexState) : LexResult :=
  match g with
  | .mk .empty => some (st.acc, st)

  | .mk (.lit s) =>
    -- For token grammars, check for 'x' character literals first
    match extractCharLit s with
    | some expected =>
      -- Character literal: match single char
      match st.chars with
      | c :: rest =>
        if c == expected then
          some (st.acc.push c, { st with chars := rest, acc := st.acc.push c })
        else none
      | [] => none
    | none =>
      -- Regular literal: match sequence
      if s.length == 1 then
        match st.chars with
        | c :: rest =>
          if c == s.get ⟨0⟩ then
            some (st.acc.push c, { st with chars := rest, acc := st.acc.push c })
          else none
        | [] => none
      else
        let rec matchChars (pat : List Char) (chars : CharStream) (acc : String) : Option (String × CharStream) :=
          match pat with
          | [] => some (acc, chars)
          | p :: ps =>
            match chars with
            | c :: rest => if c == p then matchChars ps rest (acc.push c) else none
            | [] => none
        match matchChars s.toList st.chars st.acc with
        | some (acc', rest) => some (acc', { st with chars := rest, acc := acc' })
        | none => none

  | .mk (.ref name) =>
    match prods.find? (·.1 == name) with
    | some (_, g') => lexGrammar prods g' st
    | none => none

  | .mk (.seq g1 g2) => do
    let (acc1, st1) ← lexGrammar prods g1 st
    let (acc2, st2) ← lexGrammar prods g2 { st1 with acc := acc1 }
    pure (acc2, st2)

  | .mk (.alt g1 g2) =>
    lexGrammar prods g1 st <|> lexGrammar prods g2 st

  | .mk (.star g') =>
    let rec go (st : LexState) : LexResult :=
      match lexGrammar prods g' st with
      | some (acc', st') => go { st' with acc := acc' }
      | none => some (st.acc, st)
    go st

  | .mk (.bind _ g') => lexGrammar prods g' st

  | .mk (.node _ g') => lexGrammar prods g' st

/-- Tokenize using token grammar productions -/
partial def tokenizeWithGrammar (prods : Productions) (mainProds : List String) (input : String) : TokenStream :=
  -- Remove comments from input before tokenizing
  let lines := input.splitOn "\n" |>.map removeLineComment
  let cleanInput := "\n".intercalate lines
  go prods mainProds cleanInput.toList []
where
  removeLineComment (s : String) : String :=
    match s.splitOn "--" with
    | [] => ""
    | h :: _ => h

  skipWhitespace : CharStream → CharStream
    | [] => []
    | c :: rest => if c.isWhitespace then skipWhitespace rest else c :: rest

  /-- Check if character is a symbol char that should become a Token.sym -/
  isSymChar (c : Char) : Bool :=
    c ∈ ['(', ')', '[', ']', '{', '}', ':', '=', '|', '*', '+', '?', '~', '>', '<', '$', '.', ',', ';', '^', '/', '\\', '!', '@', '#', '%', '&', '-']

  /-- Check if character is a Unicode symbol -/
  isUnicodeSymChar (c : Char) : Bool :=
    c ∈ ['→', '←', '×', '∂', '∨', '∧', '∀', '∃', '▸', '▹', '⊢', '⦉', '⦊', '↔', '⊕']

  /-- Try to extract a multi-char operator -/
  tryMultiCharOp : CharStream → Option (String × CharStream)
    | ':' :: ':' :: '=' :: rest => some ("::=", rest)
    | ':' :: '=' :: rest => some (":=", rest)
    | '~' :: '~' :: '>' :: rest => some ("~~>", rest)
    | '~' :: '>' :: rest => some ("~>", rest)
    | '-' :: '>' :: rest => some ("->", rest)
    | '<' :: '-' :: rest => some ("<-", rest)
    | _ => none

  /-- Try to extract a character literal 'x' or '\x' -/
  tryCharLit : CharStream → Option (Token × CharStream)
    | '\'' :: '\\' :: c :: '\'' :: rest => some (Token.lit s!"'\\{c}'", rest)
    | '\'' :: c :: '\'' :: rest => some (Token.lit s!"'{c}'", rest)
    | _ => none

  /-- Try to extract a string literal "..." -/
  tryStringLit : CharStream → Option (Token × CharStream)
    | '"' :: rest =>
      let rec takeString (chars : List Char) (acc : String) : Option (String × List Char) :=
        match chars with
        | [] => none  -- unterminated string
        | '"' :: rest' => some (acc, rest')
        | '\\' :: c :: rest' => takeString rest' (acc.push '\\' |>.push c)
        | c :: rest' => takeString rest' (acc.push c)
      match takeString rest "" with
      | some (str, rest') => some (Token.lit s!"\"{str}\"", rest')
      | none => none
    | _ => none

  /-- Try to extract a special <ident> token -/
  trySpecial : CharStream → Option (Token × CharStream)
    | '<' :: rest =>
      let rec takeUntilClose (chars : List Char) (acc : String) : Option (String × List Char) :=
        match chars with
        | [] => none  -- unterminated
        | '>' :: rest' => some (acc, rest')
        | c :: rest' => takeUntilClose rest' (acc.push c)
      match takeUntilClose rest "" with
      | some (name, rest') => some (Token.sym s!"<{name}>", rest')
      | none => none
    | _ => none

  tryTokenize (prods : Productions) (mainProds : List String) (chars : CharStream) : Option (Token × CharStream) :=
    -- First try string and character literals (they have special syntax)
    match tryStringLit chars with
    | some result => some result
    | none =>
      match tryCharLit chars with
      | some result => some result
      | none =>
        -- Then try special <...> syntax
        match trySpecial chars with
        | some result => some result
        | none =>
          -- Then try each main production
          mainProds.findSome? fun prodName =>
      match prods.find? (·.1 == prodName) with
      | some (_, g) =>
        match lexGrammar prods g { chars := chars, acc := "" } with
        | some (acc, st') =>
          if acc.isEmpty then none
          else
            -- Create appropriate token type based on production name
            let tok := if prodName.endsWith "ident" then Token.ident acc
                      else if prodName.endsWith "number" then Token.number acc
                      else if prodName.endsWith "string" then Token.lit acc
                      else Token.sym acc
            some (tok, st'.chars)
        | none => none
      | none => none

  go (prods : Productions) (mainProds : List String) (chars : CharStream) (acc : TokenStream) : TokenStream :=
    match skipWhitespace chars with
    | [] => acc.reverse
    | chars' =>
      match tryTokenize prods mainProds chars' with
      | some (tok, rest) => go prods mainProds rest (tok :: acc)
      | none =>
        -- Try multi-char operators first
        match tryMultiCharOp chars' with
        | some (op, rest) => go prods mainProds rest (Token.sym op :: acc)
        | none =>
          -- Then single-char symbols
          match chars' with
          | c :: rest =>
            if isSymChar c || isUnicodeSymChar c then
              go prods mainProds rest (Token.sym (String.singleton c) :: acc)
            else
              -- Skip truly unknown char
              go prods mainProds rest acc
          | [] => acc.reverse

/-! ## Syntax-level Grammar Interpretation (Parser) -/

/-- Parsing state -/
structure ParseState where
  tokens : TokenStream
  binds  : List (String × Term)
  deriving Repr, Nonempty

/-! ## Syntax-level Interpretation -/

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

/-- Parameterized grammar parser: builds into any AST type.

    This is the key abstraction that allows building typed ASTs
    from grammars. The default instance builds Term, but custom
    instances can build GADTs with compile-time validation.

    Example: RedttExpr instance could pattern-match on constructor
    names to build the appropriate typed constructors.
-/
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

/-- Convenience: parse with default Term target -/
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
