/-
  TokenEngine: Grammar-driven Tokenizer Engine

  Helpers for the generated tokenizer. Interprets the Token grammar
  (character-level) to produce TokenStream.

  Uses lexGrammar to interpret character patterns, plus special handling for:
  - Comments (-- to end of line)
  - Multi-char operators (::=, ~>, etc.)
  - String/char literals ("...", '.')
  - Special syntax (<ident>)
  - Symbol fallback for unrecognized chars

  DO NOT EDIT - this is infrastructure for generated/BootstrapTokenizer.lean
-/

import Lego.Algebra

namespace Lego.Generated

/-! ## Character Stream Types -/

abbrev CharStream := List Char

/-- Lexer state -/
structure LexState where
  chars : CharStream
  acc   : String := ""  -- accumulated characters for current token
  deriving Repr

/-- Result of lexing one token -/
abbrev LexResult := Option (String × LexState)

/-- Grammar productions map -/
abbrev Productions := List (String × GrammarExpr)

/-! ## Character-level Grammar Engine -/

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

/-! ## Tokenizer: Grammar + Special Handling -/

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

end Lego.Generated
