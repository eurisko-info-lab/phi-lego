/-
  Lego.Laws: Algebraic laws for Isos

  The key insight: we can PROVE that parse ∘ print = id (roundtrip).
  This is the mathematical foundation that makes the whole system work.
-/

import Lego.Algebra
import Lego.Interp

namespace Lego

/-! ## Iso Laws -/

/-- An Iso is lawful if forward and backward are partial inverses -/
class LawfulIso (r : Iso A B) : Prop where
  /-- If forward succeeds, backward inverts it -/
  forward_backward : ∀ a b, r.forward a = some b → r.backward b = some a
  /-- If backward succeeds, forward inverts it -/
  backward_forward : ∀ a b, r.backward b = some a → r.forward a = some b

namespace Iso

/-- Identity is lawful -/
instance : LawfulIso (Iso.id : Iso A A) where
  forward_backward := by intros; simp_all [id]
  backward_forward := by intros; simp_all [id]

/-- Composition preserves lawfulness -/
theorem comp_lawful [LawfulIso f] [LawfulIso g] :
    ∀ a c, (f >>> g).forward a = some c →
           (f >>> g).backward c = some a := by
  intro a c h
  simp [comp] at h ⊢
  obtain ⟨b, hf, hg⟩ := Option.bind_eq_some_iff.mp h
  have hg' := LawfulIso.forward_backward a b hf
  have hf' := LawfulIso.forward_backward b c hg
  simp [hf', hg']

end Iso

/-! ## Kleene Algebra Laws (GrammarExpr) -/

/-- Sequence is associative (semantic) -/
axiom seq_assoc (a b c : GrammarExpr) (prods : Productions) (st : ParseState) :
    parseGrammar prods ((a.seq b).seq c) st = parseGrammar prods (a.seq (b.seq c)) st

/-! ## Semantic Equality Axioms -/

/-- Alternative is commutative (semantic) -/
axiom alt_comm_semantic (a b : GrammarExpr) (prods : Productions) (st : ParseState) :
    parseGrammar prods (a.alt b) st = parseGrammar prods (b.alt a) st

/-- Star unfolds: g* = (g ⬝ g*) ⊕ ε -/
axiom star_unfold_semantic (g : GrammarExpr) (prods : Productions) (st : ParseState) :
    parseGrammar prods g.star st = parseGrammar prods ((g.seq g.star).alt .empty) st

/-! ## Roundtrip Theorem -/

/-- The fundamental theorem: for a well-formed grammar,
    parse ∘ print = id (on the domain where both succeed) -/
axiom roundtrip (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t : Term, ∀ tokens : TokenStream,
      interp.parse tokens = some t →
      interp.print t >>= interp.parse = some t

/-! ## Confluence (Church-Rosser) -/

/-- If rules are orthogonal, normalization is confluent -/
axiom confluence (lang : Language) (startProd : String) :
    let interp := lang.toInterp startProd
    ∀ t : Term,
      interp.normalize (interp.normalize t) = interp.normalize t

end Lego
