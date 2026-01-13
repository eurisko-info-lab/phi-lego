# Phi Manual

**phi** is a term rewriting CLI for CursorForLego — a semantic IDE architecture for proof assistants.

## Quick Start

```bash
# Build
ghc -O2 Phi.hs -o phi

# Run tests
./phi test

# Interactive REPL
./phi repl

# Evaluate inline
./phi eval '(path i a b)'
```

## Core Concepts

### Terms (S-expressions)

Phi uses s-expressions as its internal representation:

```sexp
; Variables
x
foo

; Nodes with children
(node arg1 arg2 arg3)

; Strings and numbers
"hello"
42

; Metavariables (for patterns)
$x
$body
```

### Rewrite Rules

Rules transform terms via pattern matching:

```
pattern ~> template
```

For example, `(app (lam $x $body) $arg) ~> $body` is β-reduction.

## Commands Reference

### Parsing & Output

| Command | Description |
|---------|-------------|
| `phi parse <file>` | Parse s-expr, pretty-print |
| `phi parse-lego <file>` | Parse Lego Unicode (λ, Π) to s-expr |
| `phi dot <file>` | Output DOT graph |
| `phi json <file>` | Output JSON |
| `phi json -r <file>` | JSON with rewrite result |

### Rewriting

| Command | Description |
|---------|-------------|
| `phi rewrite <file>` | Apply rules, show result |
| `phi rewrite -v <file>` | Verbose: show each step |
| `phi metrics <file>` | Show steps, fuel, rules fired |
| `phi diff <f1> <f2>` | Structural diff |

### Projections (6 backends)

| Command | Target |
|---------|--------|
| `phi to-cooltt <file>` | [cooltt](https://github.com/RedPRL/cooltt) |
| `phi to-agda <file>` | Cubical Agda |
| `phi to-lean <file>` | Lean 4 + Mathlib |
| `phi to-coq <file>` | Coq + HoTT |
| `phi to-lego <file>` | Lego syntax |

### File Generation

```bash
phi gen-cooltt <file> -o <out>
phi gen-agda <file> -o <out>
phi gen-lean <file> -o <out>
phi gen-coq <file> -o <out>
phi gen-lego <file> -o <out>
```

### LLM Integration

| Command | Description |
|---------|-------------|
| `phi tokens <file>` | Estimate token count |
| `phi llm-format <file>` | Human-readable math notation |
| `phi llm-prompt <task> <file>` | Generate prompt with context |
| `phi llm-prompt <task> <file> --budget N` | Limit to N tokens |

### Watch Mode

```bash
phi watch <file> -o <out>   # Auto-regenerate on changes
```

### REPL Commands

```
φ> (path i a b)
  → (path i a b)
φ> :cooltt
ext i => _ with [i=0 => a | i=1 => b]
φ> :agda
PathP (λ i → _) a b
φ> :lean
a = b
φ> :coq
a = b
φ> :lego
(path i a b)
φ> :dot
digraph Term { ... }
φ> :json
{"type":"node","label":"path",...}
φ> :tokens
3
φ> :llm
a ≡ b
φ> :trace
1. rule_name: (result)
φ> :metrics
Steps: 0, Fuel used: 0, Normalized: True
φ> :rules
  tokenize_scoped: (tokenize $piece $t)
  ...
φ> :h
(help)
φ> :q
Bye!
```

---

## Full Use Case: AI-Assisted Proof Development

This walkthrough shows how to use phi with an LLM to develop and verify proofs.

### Step 1: Define Your Context

Create a file with semantic atoms — each has a key, value, cost, relevance, and priority:

```bash
cat > myproof.sexp << 'EOF'
; atom format: (atom "key" <term> <cost> <relevance> <priority>)

; Core type theory
(atom "Path-type"
  (define Path
    (Pi A Type (Pi x A (Pi y A Type)))
    (lam A (lam x (lam y (path i x y)))))
  50 100 10)

; Symmetry lemma we want to prove
(atom "symm-goal"
  (Pi A Type (Pi x A (Pi y A (Pi p (Path A x y) (Path A y x)))))
  30 95 9)

; Existing path operations
(atom "path-inv"
  (rule path-inv (path-inv (path $i $a $b)) (path $i $b $a))
  20 80 7)

; Reflexivity
(atom "refl"
  (define refl
    (Pi A Type (Pi x A (Path A x x)))
    (lam A (lam x (reflJ x))))
  40 70 5)
EOF
```

### Step 2: Check Token Budget

```bash
./phi tokens myproof.sexp
# Estimated tokens: 47
```

### Step 3: Generate LLM Prompt

```bash
./phi llm-prompt "Prove path symmetry using path-inv" myproof.sexp --budget 200
```

Output:
```
# Task: Prove path symmetry using path-inv

## Context (budget: 200 tokens)

- Path-type: Path : (A : Type) → (x : A) → (y : A) → Type := λA. λx. λy. x ≡ y
- symm-goal: (A : Type) → (x : A) → (y : A) → (p : Path(A, x, y)) → Path(A, y, x)
- path-inv: path-inv: path-inv(x ≡ y) ↝ y ≡ x
- refl: refl : (A : Type) → (x : A) → Path(A, x, x) := λA. λx. reflJ(x)

## Instructions
Complete the task using the context above. Return your answer as s-expressions.
```

### Step 4: Get AI Response

Send the prompt to your LLM. It might respond with:

```sexp
(define symm
  (Pi A Type (Pi x A (Pi y A (Pi p (Path A x y) (Path A y x)))))
  (lam A (lam x (lam y (lam p (path-inv p))))))
```

### Step 5: Save and Parse

```bash
cat > symm.sexp << 'EOF'
(define symm
  (Pi A Type (Pi x A (Pi y A (Pi p (Path A x y) (Path A y x)))))
  (lam A (lam x (lam y (lam p (path-inv p))))))
EOF

./phi parse symm.sexp
```

### Step 6: View in Multiple Proof Assistants

```bash
echo "=== cooltt ===" && ./phi to-cooltt symm.sexp
echo "=== Agda ===" && ./phi to-agda symm.sexp
echo "=== Lean ===" && ./phi to-lean symm.sexp
echo "=== Coq ===" && ./phi to-coq symm.sexp
```

Output:
```
=== cooltt ===
def symm : (A : type) → (x : A) → (y : A) → (p : path A x y) → path A y x := A => x => y => p => symm _ {i => p}

=== Agda ===
symm : (A : Type) → (x : A) → (y : A) → (p : PathP A x y) → PathP A y x
symm = λ A → λ x → λ y → λ p → sym p

=== Lean ===
def symm : (A : Type) → (x : A) → (y : A) → (p : @Eq A x y) → @Eq A y x := fun A => fun x => fun y => fun p => p.symm

=== Coq ===
Definition symm : forall (A : Type), forall (x : A), forall (y : A), forall (p : @paths A x y), @paths A y x := fun A => fun x => fun y => fun p => inverse p.
```

### Step 7: Generate Actual Files

```bash
./phi gen-cooltt symm.sexp -o Symm.cooltt
./phi gen-agda symm.sexp -o Symm.agda
./phi gen-lean symm.sexp -o Symm.lean
./phi gen-coq symm.sexp -o Symm.v
```

### Step 8: Verify with Proof Assistant

```bash
# cooltt
cd ../cooltt && dune exec cooltt ../test/Symm.cooltt

# Agda (needs cubical library)
agda Symm.agda

# Lean (needs Mathlib)
lake build

# Coq (needs HoTT library)
coqc -R . HoTT Symm.v
```

### Step 9: Iterate with Watch Mode

While developing, use watch mode to auto-regenerate:

```bash
./phi watch symm.sexp -o Symm.cooltt &

# Edit symm.sexp in your editor
# File auto-regenerates on save
```

---

## Use Case: Lego Unicode Round-Trip

### Input Lego Unicode syntax:

```bash
cat > id.lego << 'EOF'
-- Identity function
(Π (A : Type). (Π (x : A). A))
(λ A. (λ x. x))
EOF
```

### Parse to s-expressions:

```bash
./phi parse-lego id.lego
# (Pi A Type (Pi x A A))
# (lam A (lam x x))
```

### Combine into definition:

```bash
cat > id-def.sexp << 'EOF'
(define id
  (Pi A Type (Pi x A A))
  (lam A (lam x x)))
EOF
```

### Generate all backends:

```bash
for ext in cooltt agda lean coq lego; do
  ./phi gen-$ext id-def.sexp -o id.$ext
  echo "=== id.$ext ===" && cat id.$ext
done
```

---

## Use Case: Visualize Term Structure

### Generate DOT graph:

```bash
./phi dot examples/identity.sexp > identity.dot
dot -Tpng identity.dot -o identity.png
```

### Or inline:

```bash
./phi eval '(app (lam x x) y)' 
# Shows all projections

./phi rewrite -v examples/path.sexp
# Shows rewrite trace
```

---

## Context Budgeting for LLMs

The `atom` format lets you prioritize what context to send:

```sexp
(atom "name" <term> <cost> <relevance> <priority>)
```

- **cost**: Estimated tokens (for budgeting)
- **relevance**: 0-100, how relevant to current task
- **priority**: Importance level (higher = more important)

Selection algorithm: Sort by `relevance × priority`, include atoms until budget exhausted.

```bash
# With 100 token budget, only highest priority items included
./phi llm-prompt "task" context.sexp --budget 100

# With 1000 token budget, more context included
./phi llm-prompt "task" context.sexp --budget 1000
```

---

## File Formats

### S-expressions (.sexp)

```sexp
; Comment
(node child1 child2)
"string"
42
$metavar
```

### Lego Unicode (.lego for parse-lego)

```
(λ x. body)           -- lambda
(Π (x : A). B)        -- dependent function type
(app f x)             -- application
$var                  -- metavariable
```

---

## Examples Directory

```
examples/
├── identity.sexp     # Identity function
├── symm.sexp         # Path symmetry
├── context.sexp      # Context budgeting demo
├── path.sexp         # Simple path
├── llm-context.sexp  # LLM atoms example
└── lego-unicode.lego # Unicode syntax demo
```

---

## Tips

1. **Start in REPL**: Use `./phi repl` to experiment interactively
2. **Check all backends**: Use `./phi eval '(term)'` to see all projections at once
3. **Use verbose mode**: `./phi rewrite -v` shows what rules fire
4. **Budget context**: Higher relevance × priority items are included first
5. **Watch mode**: Auto-regenerate while editing in another window
6. **Metrics**: Check `./phi metrics` to see rewrite efficiency

---

## Architecture

```
.sexp files ──┬──► phi rewrite ──► normalized term
              │
              ├──► phi to-cooltt ──► cooltt syntax
              ├──► phi to-agda ──► Cubical Agda
              ├──► phi to-lean ──► Lean 4
              ├──► phi to-coq ──► Coq/HoTT
              └──► phi to-lego ──► Lego syntax

.lego files ──► phi parse-lego ──► .sexp

LLM workflow:
  context.sexp ──► phi llm-prompt ──► prompt ──► LLM ──► response ──► .sexp
```

---

## Building

```bash
# Just GHC, no dependencies
ghc -O2 Phi.hs -o phi

# Run all 42 tests
./phi test
```
