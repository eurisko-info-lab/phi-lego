/-
  Lego.Algebra.All
  
  Re-exports all algebra modules for convenient access.
  
  Usage:
    import Lego.Algebra.All
  
  This provides access to:
  - Setoid: Equivalence relations, quotients, congruences
  - KleeneAlgebra: Grammar as Kleene algebra with formal laws
  - TermEquiv: Alpha/beta/eta equivalence for terms
  - Substitution: Capture-avoiding substitution with composition
  - Confluence: Church-Rosser theorem for term rewriting
  - NormalForm: Canonical representatives and caching
  - Iso: Parse/print isomorphism with type safety
  - Roundtrip: Bidirectional roundtrip proofs
  - Bootstrap: Meta-circularity and grammar self-description
  - SelfDescribing: Complete self-description formalization
-/

-- Foundation
import Lego.Algebra.Setoid
import Lego.Algebra.KleeneAlgebra

-- Term theory
import Lego.Algebra.TermEquiv
import Lego.Algebra.Substitution

-- Rewriting theory
import Lego.Algebra.Confluence
import Lego.Algebra.NormalForm

-- Bidirectional transformations
import Lego.Algebra.Iso
import Lego.Algebra.Roundtrip

-- Meta-circularity
import Lego.Algebra.Bootstrap
import Lego.Algebra.SelfDescribing
