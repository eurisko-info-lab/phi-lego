/-
  Lego.Algebra: Core algebraic structures for bidirectional transformations

  The fundamental insight: everything is an Iso (partial isomorphism).
  - Grammar: Token ↔ Term (representation ↔ structure)
  - Rules:   Term ↔ Term  (structure ↔ structure)
  - Types:   Term → Prop  (structure → validity)

  A Language is a composition of Isos.
-/

namespace Lego

/-! ## The Core: Partial Isomorphism -/

/-- A partial isomorphism between types A and B.
    This is the atomic unit of computation in Lego.

    Mathematically: a partial isomorphism (A ⇌ B)
    - forward:  A → Option B  (parse/reduce)
    - backward: B → Option A  (print/expand)

    Laws (when both succeed):
    - forward ∘ backward = id
    - backward ∘ forward = id
-/
structure Iso (A B : Type) where
  forward  : A → Option B
  backward : B → Option A

namespace Iso

/-- Identity: A ⇌ A -/
def id : Iso A A where
  forward  := some
  backward := some

/-- Composition: (A ⇌ B) → (B ⇌ C) → (A ⇌ C) -/
def comp (f : Iso A B) (g : Iso B C) : Iso A C where
  forward  := fun a => f.forward a >>= g.forward
  backward := fun c => g.backward c >>= f.backward

infixr:90 " >>> " => comp

/-- Parallel composition (product): (A ⇌ B) → (C ⇌ D) → (A × C ⇌ B × D) -/
def par (f : Iso A B) (g : Iso C D) : Iso (A × C) (B × D) where
  forward  := fun (a, c) => do
    let b ← f.forward a
    let d ← g.forward c
    pure (b, d)
  backward := fun (b, d) => do
    let a ← f.backward b
    let c ← g.backward d
    pure (a, c)

infixr:80 " *** " => par

/-- Choice (coproduct): (A ⇌ C) → (B ⇌ C) → (A ⊕ B ⇌ C) -/
def choice (f : Iso A C) (g : Iso B C) : Iso (Sum A B) C where
  forward := fun
    | .inl a => f.forward a
    | .inr b => g.forward b
  backward := fun c =>
    match f.backward c with
    | some a => some (.inl a)
    | none => g.backward c |>.map .inr

infixr:70 " ||| " => choice

/-- Alternative: try first, fallback to second (same types) -/
def orElse (f g : Iso A B) : Iso A B where
  forward := fun a => f.forward a <|> g.forward a
  backward := fun b => f.backward b <|> g.backward b

/-- Symmetric: flip forward and backward -/
def sym (f : Iso A B) : Iso B A where
  forward  := f.backward
  backward := f.forward

prefix:max "~" => sym

end Iso

/-! ## Terms: The Universal Structure -/

/-- Term: the universal AST representation.
    Everything reduces to/from Terms. -/
inductive Term where
  | var : String → Term
  | con : String → List Term → Term
  | lit : String → Term
  deriving Repr, BEq, Inhabited

namespace Term

/-- Constructor with no arguments -/
def atom (s : String) : Term := con s []

/-- Convenient constructor -/
def app (f : String) (args : List Term) : Term := con f args

/-- Match a pattern against a term, returning bindings -/
partial def matchPattern (pat : Term) (t : Term) : Option (List (String × Term)) :=
  match pat, t with
  | .var name, _ =>
    if name.startsWith "$" then some [(name, t)]
    else if t == pat then some []
    else none
  | .lit a, .lit b => if a == b then some [] else none
  | .con c1 args1, .con c2 args2 =>
    if c1 == c2 && args1.length == args2.length then
      matchList args1 args2
    else none
  | _, _ => none
where
  matchList : List Term → List Term → Option (List (String × Term))
    | [], [] => some []
    | p :: ps, t :: ts => do
      let m1 ← matchPattern p t
      let m2 ← matchList ps ts
      pure (m1 ++ m2)
    | _, _ => none

/-- Apply substitution with bindings to produce a term -/
partial def substitute (t : Term) (env : List (String × Term)) : Term :=
  match t with
  | .var name =>
    if name.startsWith "$" then
      env.find? (·.1 == name) |>.map (·.2) |>.getD t
    else t
  | .lit s => .lit s
  | .con c args => .con c (args.map (substitute · env))

/-- Convert term to string representation -/
partial def toString : Term → String
  | .var name => name
  | .lit s => s!"\"{s}\""
  | .con c [] => s!"({c})"
  | .con c args => s!"({c} {" ".intercalate (args.map toString)})"

instance : ToString Term := ⟨toString⟩

end Term

/-! ## Tokens: The Universal Representation -/

/-- Token: atomic unit of text representation -/
inductive Token where
  | ident  : String → Token
  | lit    : String → Token
  | sym    : String → Token
  | number : String → Token
  deriving Repr, BEq, Inhabited

/-- A stream of tokens with position tracking -/
abbrev TokenStream := List Token

/-! ## The Grammar Algebra -/

/-- GrammarF: functor for grammar expressions.
    This is the *-semiring (Kleene algebra) structure. -/
inductive GrammarF (α : Type) where
  | empty : GrammarF α                      -- ε (identity for alt)
  | lit   : String → GrammarF α             -- literal string
  | ref   : String → GrammarF α             -- reference to production
  | seq   : α → α → GrammarF α              -- sequence (monoidal)
  | alt   : α → α → GrammarF α              -- alternative (coproduct)
  | star  : α → GrammarF α                  -- Kleene star
  | bind  : String → α → GrammarF α         -- capture binding
  | node  : String → α → GrammarF α         -- AST node wrapper
  deriving Repr, BEq

/-- Fixed point of GrammarF -/
inductive GrammarExpr where
  | mk : GrammarF GrammarExpr → GrammarExpr
  deriving Repr, BEq

namespace GrammarExpr

def empty : GrammarExpr := mk .empty
def lit (s : String) : GrammarExpr := mk (.lit s)
def ref (s : String) : GrammarExpr := mk (.ref s)
def seq (a b : GrammarExpr) : GrammarExpr := mk (.seq a b)
def alt (a b : GrammarExpr) : GrammarExpr := mk (.alt a b)
def star (g : GrammarExpr) : GrammarExpr := mk (.star g)
def bind (x : String) (g : GrammarExpr) : GrammarExpr := mk (.bind x g)
def node (n : String) (g : GrammarExpr) : GrammarExpr := mk (.node n g)

-- Infix notation
infixr:65 " ⬝ " => seq   -- sequence
infixr:60 " ⊕ " => alt   -- alternative

end GrammarExpr

/-! ## Rule Algebra -/

/-- A rewrite rule: pattern ↔ template -/
structure Rule where
  name     : String
  pattern  : Term
  template : Term
  deriving Repr, BEq

/-- Match a pattern against a term, returning bindings -/
partial def matchPattern (pat : Term) (t : Term) : Option (List (String × Term)) :=
  match pat, t with
  | .var name, _ =>
    if name.startsWith "$" then some [(name.drop 1, t)]
    else if t == pat then some []
    else none
  | .lit a, .lit b => if a == b then some [] else none
  | .con c1 args1, .con c2 args2 =>
    if c1 == c2 && args1.length == args2.length then
      matchList args1 args2
    else none
  | _, _ => none
where
  matchList : List Term → List Term → Option (List (String × Term))
    | [], [] => some []
    | p :: ps, t :: ts => do
      let m1 ← matchPattern p t
      let m2 ← matchList ps ts
      pure (m1 ++ m2)
    | _, _ => none

/-- Apply a template with bindings to produce a term -/
partial def applyTemplate (env : List (String × Term)) : Term → Term
  | .var name =>
    if name.startsWith "$" then
      env.find? (·.1 == name.drop 1) |>.map (·.2) |>.getD (.var name)
    else .var name
  | .lit s => .lit s
  | .con c args => .con c (args.map (applyTemplate env))

/-- Convert a Rule to an Iso on Terms -/
def Rule.toIso (r : Rule) : Iso Term Term where
  forward := fun t =>
    match matchPattern r.pattern t with
    | some env => some (applyTemplate env r.template)
    | none => none
  backward := fun t =>
    match matchPattern r.template t with
    | some env => some (applyTemplate env r.pattern)
    | none => none

/-- Apply a rule to a term (forward direction) -/
def Rule.apply (r : Rule) (t : Term) : Option Term :=
  r.toIso.forward t

/-- Apply a rule in reverse (backward direction) -/
def Rule.unapply (r : Rule) (t : Term) : Option Term :=
  r.toIso.backward t

/-! ## Language: Composition of Pieces -/

/-- A Piece: grammar fragment + rules.
    Each piece is a self-contained language fragment with its own interpreter. -/
structure Piece where
  name       : String
  grammar    : List (String × GrammarExpr)
  rules      : List Rule
  deriving Repr

/-- A Language: composition of pieces via pushout.
    Language = ⊔ Pieces = Combined Grammar + Combined Interpreter -/
structure Language where
  name    : String
  pieces  : List Piece
  deriving Repr

namespace Language

/-- Get all grammar productions -/
def allGrammar (lang : Language) : List (String × GrammarExpr) :=
  lang.pieces.flatMap (·.grammar)

/-- Get all rules -/
def allRules (lang : Language) : List Rule :=
  lang.pieces.flatMap (·.rules)

/-- Combine rules into a single Iso that tries each rule -/
def combineRules (rules : List Rule) : Iso Term Term :=
  match rules with
  | [] => Iso.id
  | r :: rs => rs.foldl (fun acc r' => Iso.orElse acc r'.toIso) r.toIso

/-- Get combined interpreter from all rules -/
def interpreter (lang : Language) : Iso Term Term :=
  combineRules lang.allRules

end Language

end Lego
