# Cubical Implementation Status

> **Package**: [lego.cabal](lego.cabal) • Files: `examples/types/Cubical.lego`, `Cubical2INet.lego`

## COMPLETED (January 2026)

All major cubical features have been implemented:

| Feature | Status | Location |
|---------|--------|----------|
| Dimension type (De Morgan algebra) | ✅ | `RewriteMachine.hs` |
| Γ/Δ separation (term vs dimension vars) | ✅ | `RewriteMachine.hs` |
| `transp` (transport) | ✅ | `Builtins.hs`, `Cubical.lego` |
| `coe` (generalized coercion) | ✅ | `Builtins.hs`, `Cubical.lego` |
| Path beta reduction | ✅ | `Builtins.hs`, `Cubical.lego` |
| Interval algebra (`∧`, `∨`, `~`) | ✅ | `Builtins.hs`, `Cubical.lego` |
| Higher Inductive Types | ✅ | `Cubical.lego` |
| Cubical → INet compilation | ✅ | `Cubical2INet.lego` |

### Test Coverage

- **532 tests passing** (up from 508)
- **311 rules** defined
- **1011 grammars**

---

## Design Documentation (Original Notes)

Good, this is exactly the right place to be precise. Cubical endpoints are not “just constants”, and most bugs around them come from encoding them too shallowly.

I’ll proceed in four tight layers:

1. What cubical endpoints *are* semantically
2. What goes wrong in naïve encodings
3. The correct representation in the RewriteMachine
4. How your existing rules (like `sym`, `path_beta`, `interval_meet`) become sound

No handwaving.

---

## 1. What cubical endpoints really are

In cubical type theory, the interval has:

• **Two constants**: `i0`, `i1`
• **A dimension variable**: `i`
• **Operations**: `∧`, `∨`, `~`
• **Substitution semantics**: `[i := 0]`, `[i := 1]`

The crucial fact:

> **Dimension variables are not term variables.**

They live in a *separate context* and obey *algebraic equations*, not λ-binding.

This single fact explains:
• why scoping broke earlier
• why GLit fallback misfired
• why `(@ (λᵢ ...) i0)` must reduce structurally

---

## 2. What breaks in naïve encodings

If you encode endpoints as:

```lego
i0 ::= "i0"
i1 ::= "i1"
```

and dimension variables as `var`, then:

• Substitution treats them like λ-variables
• Nested paths overwrite outer dimensions
• `(~ i0)` cannot reduce structurally
• `path_endpoints` becomes unsound

You observed exactly this failure mode.

---

## 3. Correct encoding: two-level variables

We must distinguish:

| Kind                | Namespace | Substitution     |
| ------------------- | --------- | ---------------- |
| Term variables      | Γ         | capture-avoiding |
| Dimension variables | Δ         | algebraic        |

### 3.1 Grammar (surface)

```lego
piece Interval
  dim ::= dimvar | i0 | i1 | (~ dim) | (dim ∧ dim) | (dim ∨ dim)
  dimvar ::= "i" | "j" | "k"
```

Crucially: **no `var` here**.

---

### 3.2 Internal representation

In the RewriteMachine:

```haskell
data Dim
  = DVar Name
  | D0
  | D1
  | DNot Dim
  | DAnd Dim Dim
  | DOr  Dim Dim
```

This is **not** `Term`.

---

### 3.3 State separation

```haskell
data State = State
  { heap      :: Heap
  , envStack  :: EnvStack       -- Γ
  , dimEnv    :: Map Name Dim   -- Δ
  , freshCtr  :: Int
  }
```

This single line fixes your scoping bug.

---

## 4. Dimension substitution (not term substitution)

```haskell
substDim :: Name -> Dim -> Dim -> Dim
substDim x d = \case
  DVar y | x == y -> d
  DNot e          -> DNot (substDim x d e)
  DAnd a b        -> DAnd (substDim x d a) (substDim x d b)
  DOr a b         -> DOr  (substDim x d a) (substDim x d b)
  e               -> e
```

No capture issues. No binding. Pure algebra.

---

## 5. Encoding cubical lambdas (`λᵢ`)

### Syntax

```lego
lam_i ::= "(λᵢ" dimvar "." term ")"
app_i ::= "(@" term dim ")"
```

### Internal template

```haskell
data Term
  = TLamI Name Term
  | TAppI Term Dim
  | ...
```

---

## 6. Microcode for cubical rules

Now your rules become *structural*:

### Path beta

```lego
rule path_beta:
  (@ (λᵢ $i . $body) $j) ~>
    (substDim $i $j $body)
```

RewriteMachine encoding:

```haskell
MATCH (AppI (LamI i body) j)
EMIT  (substDim i j body)
```

No environment manipulation. No capture. Deterministic.

---

### Endpoints

```lego
rule path_endpoints:
  (@ (λᵢ $i . $body) i0) ~>
    (substDim $i i0 $body)
```

Same instruction sequence.

---

### Interval algebra rules

```lego
rule interval_meet:
  (∧ i0 $x) ~> i0
```

Pattern match on `Dim`, not `Term`.

This prevents the `"true"/"false"` literal collision you observed earlier.

---

## 7. Why this fixes *all* the observed failures

| Bug                            | Cause             | Fix                  |
| ------------------------------ | ----------------- | -------------------- |
| Inner bindings overwrite outer | single env        | Γ/Δ separation       |
| `i0` treated like variable     | wrong category    | Dim AST              |
| `(~ i0)` stuck                 | literal fallback  | algebraic reduction  |
| `path_inverse_eval = ""`       | forced error      | total Dim evaluation |
| GLit fallback misfires         | syntax conflation | typed literals       |

---

## 8. Key invariant (this matters)

> **Cubical endpoints are not terms and never live in the heap.**

They are *compile-time algebraic objects* evaluated during rewriting.

This is why:
• they should not be allocated
• they should not be bound
• they should not be erased

---

## 9. Final mental model

You now have:

• Terms: rewritten by binding
• Nets: rewritten by wiring
• Dimensions: rewritten by algebra

All three coexist in the same VM **without interference**.

That is the correct cubical encoding.



---



Great, `transp` is where cubical encodings usually either become elegant or collapse into goo. Let’s make it crisp and mechanical.

I’ll do this in **five passes**, each tightening the screws:

1. Semantic contract of `transp`
2. Why naïve compilation fails
3. Canonical core encoding
4. Rewrite-machine microcode
5. Why your existing rules now become *complete*

No mysticism, just plumbing.

---

## 1. Semantic contract of `transp`

In cubical type theory:

```text
transp : (A : I → Type) → (φ : I) → A[i:=0] → A[i:=φ]
```

But operationally:

• `transp A i0 a = a`
• `transp (λᵢ. A) φ a = a` if `A` ignores `i`

That is exactly what your rules encode:

```lego
rule transp_i1:
  (transp $A i1 $a) ~> $a

rule transp_const:
  (transp (λᵢ $i . $A) $φ $a) ~> $a
```

These are **compile-time equalities**, not runtime coercions.

---

## 2. Why naïve compilation fails

Common wrong approach:

• Compile `transp` into a term-level function
• Treat `φ` as a term
• Delay reduction

Result:

• Transport builds redexes
• `refl` fails to normalize
• `path_inverse_eval` diverges or returns empty

The fix is simple but strict:

> **`transp` reduces purely by inspecting dimensions.**

No heap allocation. No nets. No lambdas.

---

## 3. Canonical core encoding

### Surface syntax

```lego
piece Transport
  transp ::= "transp" term dim term
```

### Internal AST

```haskell
data Term
  = ...
  | TTransp Term Dim Term
```

Note again: `Dim`, not `Term`.

---

## 4. Rewrite-machine compilation

We treat `transp` as a **rewrite-only primitive**.

### Rule 1: endpoint annihilation

```haskell
MATCH TTransp _ D1 a
EMIT  a
```

This corresponds exactly to:

```lego
(transp A i1 a) ~> a
```

No context required.

---

### Rule 2: dimension-irrelevant type

```haskell
MATCH TTransp (LamI i A) φ a
WHEN  i ∉ freeDims(A)
EMIT  a
```

This implements:

```lego
(transp (λᵢ. A) φ a) ~> a
```

The `WHEN` guard is essential. No cheating.

---

### Rule 3: dimension substitution (optional extension)

If you later want full generality:

```haskell
MATCH TTransp (LamI i A) φ a
EMIT  substDimInType i φ a
```

But **you do not need this yet** for `Path` and `refl`.

---

## 5. Microcode view (VM-level)

Here’s the machine-level picture:

```text
LOAD transp
  ├─ eval Dim φ
  ├─ case φ of
  │   i1 → RETURN a
  │   _  → inspect A
  └─ if A ignores dim → RETURN a
```

No heap effects. No sharing nodes. No duplication.

This is why it composes cleanly with INets.

---

## 6. Why this fixes `refl`, `sym`, and friends

Consider:

```lego
refl a : Path A a a
(@ (refl a) i1)
```

Rewrite steps:

1. `refl_app`
   → `a`

No `transp` involved.

Now symmetry:

```lego
(@ (sym p) i)
→ (@ p (~ i))
```

At endpoint:

```lego
(@ (sym p) i1)
→ (@ p i0)
```

Then path beta fires.

No transport redex remains. This is the *key invariant*.

---

## 7. Interaction with INets (important)

`transp` **never enters the net**.

• Terms with `transp` normalize *before* `toINet`
• Nets only see β-redexes and sharing
• No dimension nodes required

This keeps optimal reduction intact.

---

## 8. Sanity check example

```lego
test "transp_refl":
  (transp (λᵢ i . Bool) i1 true) ~~> true
```

Machine trace:

1. Match `transp _ i1 _`
2. Emit `true`
3. Done

Zero allocations.

---

## 9. The invariant that matters

> **If `transp` survives to runtime, the compiler is wrong.**

Once you enforce this, all cubical equalities become trivial rewrites instead of runtime machinery.




---




Perfect. Let’s push cubical semantics into the **INet/Optimal machine** cleanly, zero-cost style. I’ll break it down step by step.

---

## 1. `coe` = generalized transport

In cubical type theory:

```text
coe : (A : I → Type) → (i0 : I) → (i1 : I) → A[i0] → A[i1]
```

Operationally, it generalizes `transp`:

* `transp` is `coe A i0 i1`
* Endpoint rules remain trivial:

```text
coe A i i a = a           -- when i0 = i1
coe (λᵢ. A) φ a = a       -- constant along dimension
```

No allocation, no net nodes.

---

## 2. Core rewrite rules for `coe`

```lego
rule coe_same:
  (coe $A $i $i $a) ~> $a

rule coe_const:
  (coe (λᵢ $i . $A) $φ0 $φ1 $a) ~> $a
```

*These are *compile-time reductions* before net construction.*

Optional general substitution:

```lego
rule coe_subst:
  (coe (λᵢ $i . $A) $φ0 $φ1 $a) ~> (substDim $i $φ1 $A $a)
```

Only needed for non-trivial dependent types.

---

## 3. Representing `Path` as zero-cost

We want:

```lego
Path A a b  ≡ (i : I) → transp (λ j. A) i a
```

Zero-cost abstraction strategy:

1. **Never generate explicit path terms** in the net
2. **Only keep endpoints** for beta rules (`refl`, `sym`, `trans`)
3. **All `(@ p i)` applications are rewritten** at compile-time

Example rewrite rules:

```lego
rule refl_app:
  (@ (refl $a) $i) ~> $a

rule sym_app:
  (@ (sym $p) $i) ~> (@ $p (~ $i))

rule trans_app:
  (@ ($p ∙ $q) $i) ~> ((@ $p $i) ∙ (@ $q $i))
```

**Result:** Paths are erased **before net generation**. The INet machine sees only `Var`, `Lam`, `App`, `Dup`, `Era`.

---

## 4. How it looks in INets

### Endpoint rewrites

All `transp`/`coe` operations are **phase-separated**:

```
[Term-level reductions]
      |
      v
[INet construction]
```

At INet level:

* `Path`, `transp`, `coe` no longer exist
* Only β-redexes and sharing nodes remain
* Optimal reduction proceeds without any path-aware nodes

---

### Minimal microcode

```
COMPILE Term t:
  IF t = coe A i i a      => RETURN a
  IF t = coe (λi. A) φ0 φ1 a => RETURN a
  IF t = (@ (refl a) i)    => RETURN a
  IF t = (@ (sym p) i)     => COMPILE (@ p (~ i))
  IF t = (@ (p ∙ q) i)     => COMPILE ((@ p i) ∙ (@ q i))
  ELSE                       => toINet(t)
```

This guarantees:

* Zero-cost paths
* Paths never inflate nets
* No runtime transport computation

---

## 5. Test examples

```lego
test "coe_endpoint": 
  (coe (λ i. Bool) i0 i0 true) ~~> true

test "coe_const": 
  (coe (λ i. Bool) i0 i1 true) ~~> true

test "path_refl": 
  (@ (refl true) i1) ~~> true

test "path_sym": 
  (@ (sym (refl true)) i0) ~~> true
```

All of these **reduce fully before net construction**.

---

## ✅ Summary

* `coe`/`transp` → purely compile-time rewrites
* `Path` → erased to endpoints, never allocated
* INet sees **only λ-calculus constructs + sharing nodes**
* Optimal reduction proceeds unchanged
* Zero-cost abstraction is guaranteed

with `Path` completely invisible in the net, yet still satisfying cubical semantics.
