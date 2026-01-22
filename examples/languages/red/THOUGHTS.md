# Universal Cubical VM (design notes)

**Thesis**: *Execution = path normalization.*

- Rewriting is not a directed “term → term” relation but a *witnessed equality*.
- Sharing is not an optimization bolted onto an evaluator; it is *re-use of paths*.
- Confluence is not a meta-proof about a rewrite system; it is *higher-dimensional coherence*.

This document reframes evaluation as cubical structure: transport, coercion, and Kan filling/comp become the primitive dynamics.

## 1. Algebra first

The design goal is to avoid ad-hoc evaluators. Every feature should come with an algebraic home and laws.

### 1.1 Core objects

- **Interval** $\mathbb{I}$ with endpoints $0,1$ and dimension variables $i,j,\dots$.
- **Terms** $t$.
- **Paths** $p : t \equiv u$ (computational equalities).
- **Transport** along paths:
  - $\mathsf{transport} : (P : A \to \mathsf{Type}) \to (p : x \equiv y) \to P(x) \to P(y)$.
- **Cubical structure** (informal API):
  - $\mathsf{coe}$ (coercion along a line)
  - $\mathsf{comp}$ (Kan composition / filling)
  - $\mathsf{sym}$, $\mathsf{refl}$, and (higher) composition of paths.

### 1.2 Laws (non-negotiable)

At minimum, the runtime must satisfy these as definitional/program equations (or as rewrite-oracles in tests):

- **Groupoid laws** for paths: $\mathsf{refl}$ is identity, $\mathsf{sym}$ is inverse, and composition is associative up to higher cells.
- **Functoriality of transport**:
  - transport along $\mathsf{refl}$ is identity
  - transport respects composition of paths
- **Kan coherence**:
  - $\mathsf{coe}$ and $\mathsf{comp}$ satisfy the standard cubical computation rules for the chosen fragment.

## 2. Operational view: evaluate by normalizing paths

Instead of evaluating $t$ directly, the machine normalizes a *diagram*.

- A configuration is a term together with an explicit equality witness (path/box) explaining why a step is valid.
- A step either:
  1) simplifies a path expression (path normalization), or
  2) performs a cubical computation rule (e.g. a $\mathsf{comp}$ boundary fills).

Fuel is required for safety when exploring higher-dimensional normal forms.

## 3. Compilation sketches

These are not commitments to concrete syntax; they indicate where the algebra lives.

### 3.1 Lambda calculus → cubical dynamics

Goal: treat $\beta$ as a witnessed equality, not a one-way rewrite.

- A $\beta$-step becomes a path constructor $\beta(t)$ such that:
  - $\beta((\lambda x. b)\ a) : ((\lambda x. b)\ a) \equiv b[a/x]$.
- Evaluation becomes simplifying/transporting along the generated path.

This makes reduction direction a choice of normalization strategy over paths.

### 3.2 Interaction nets → cubical graph rewriting

Interaction nets already make sharing explicit. The cubical re-interpretation is:

- Net rewrites produce equalities between graphs.
- Duplication/erasure are tracked as path reuse/degenerate structure.
- Optimal reduction corresponds to normalizing diagrams with maximal sharing.

## 4. HITs and colimits (pushouts as gluing programs)

Higher inductive types are the natural interface for data + equations.

- A HIT point constructor introduces terms.
- A HIT path constructor introduces computation-relevant equalities.

Pushouts (and more general colimits) act like program linkage: gluing components plus explicit identifications. If languages compose via pushouts (as in this repo), the VM should expose a corresponding runtime notion: compose programs by gluing and then normalize the resulting equalities.

## 5. Scope control (what to make computable)

Full HoTT has infinite coherence; a VM needs a decidable fragment.

Pragmatic axes to choose:

- Truncation level: sets / 1-types / n-types.
- Definitional vs propositional equality: which equalities reduce automatically?
- Dimension discipline: which dimension terms are allowed (variables only vs lattice ops)?

The intent is to start with a small cubical core (RedTT-like) and add expressivity via algebraic extensions.

## 6. MVP plan

1. Specify a minimal core calculus: terms, paths, $\mathsf{transport}$, $\mathsf{coe}$, $\mathsf{comp}$.
2. Implement a small-step normalizer with fuel and a deterministic strategy.
3. Add law tests as oracles:
   - groupoid laws
   - transport functoriality
   - basic Kan computation rules
4. Add one HIT exemplar (e.g. $S^1$) and validate its computation rules.
5. Add a compilation bridge from a tiny lambda subset or interaction-net subset.

## 7. Open questions

- What fragment of cubical structure is primitive vs derived?
- How are higher-dimensional equalities represented operationally (explicit syntax vs implicit normalization)?
- Which normal forms are intended: term normal forms, path normal forms, or both?
- How to expose sharing as a first-class algebraic structure (e.g. explicit Share nodes / pushouts)?

If this file is meant to become an engineering spec, the next edit should add:

- a formal grammar for the core calculus, and
- an explicit list of computation rules that constitute the VM’s definitional equality.
