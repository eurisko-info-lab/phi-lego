# Compilation Pipeline: Lambda/Cubical → INet → RewriteMachine

## Architecture Overview

```
┌─────────────┐     ┌──────────────┐     ┌──────────────────────┐     ┌─────────────────┐
│  Lambda.lego │────▶│ Lambda2INet  │────▶│                      │     │                 │
└─────────────┘     └──────────────┘     │                      │     │                 │
                                         │   INet.lego          │────▶│ RewriteMachine  │
┌─────────────┐     ┌──────────────┐     │   (Interaction Nets) │     │ (Bytecode)      │
│ Cubical.lego│────▶│ Cubical2INet │────▶│                      │     │                 │
└─────────────┘     └──────────────┘     └──────────────────────┘     └─────────────────┘
                                                    │
                                         ┌──────────────────────┐
                                         │  INet2RewriteMachine │
                                         │  (Compiler)          │
                                         └──────────────────────┘
```

## Files

| File | Purpose |
|------|---------|
| `Lambda.lego` | Lambda calculus (var, lam, app, β-reduction) |
| `INet.lego` | Interaction nets (agents, ports, wires, rules) |
| `Cubical.lego` | Cubical type theory (paths, intervals, transport) |
| `Lambda2INet.lego` | Compile λ-terms to interaction nets (Lamping) |
| `Cubical2INet.lego` | Compile cubical terms to interaction nets |
| `INet2RewriteMachine.lego` | Compile INet to RewriteMachine bytecode |
| `RewriteMachine.lego` | Abstract machine specification |
| `Lego/RewriteMachine.hs` | Haskell implementation of the machine |

## Key Concepts

### Interaction Nets (INet)

Lafont's interaction nets provide optimal β-reduction:

- **Agents**: Nodes with a principal port + auxiliary ports
- **Wires**: Connect ports bidirectionally
- **Interaction**: Only between principal ports (no interference)

```
Fundamental agents:
  γ (con)  - constructor, 2 aux ports
  δ (dup)  - duplicator, 2 aux ports  
  ε (era)  - eraser, 0 aux ports

Lambda encoding:
  @λ (lam) - lambda node: binder port + body port
  @@ (app) - application node: func port + arg port
```

### Lambda → INet (Lamping's Algorithm)

```
encode(x)       = port x (free variable wire)
encode(λx.M)    = @λ node with x bound to port 1, M on port 2
encode(M N)     = @@ node with M on port 1, N on port 2

Sharing: Variables used multiple times get δ (duplicator) nodes
Erasure: Unused variables get ε (eraser) nodes
```

### Cubical → INet

Extend INet with interval agents:

```
Interval endpoints:
  i0, i1  - 0-ary agents (constants)

Interval operations:
  @∧ (meet) - min(a,b)
  @∨ (join) - max(a,b)
  @~ (rev)  - 1-a

Path operations:
  @λᵢ (pathabs) - path abstraction (dim binder + body)
  @@ᵢ (pathapp) - path application (path + dim)

Transport:
  @transp - transport along path
  @hcomp  - homogeneous composition
```

### INet → RewriteMachine

The RewriteMachine executes INet reduction:

```
Instructions:
  MATCH p    - Find redex matching pattern p
  PUSH_ENV   - Enter new scope
  POP_ENV    - Exit scope
  BIND x h   - Bind variable x to handle h
  FRESH n    - Allocate n fresh handles
  EMIT t     - Emit template t to heap
  FAIL       - Abort current reduction

Compilation:
  (interact A B ~> net) compiles to:
    MATCH (interact A B)
    PUSH_ENV
    <compile net construction>
    POP_ENV
```

### Reduction Strategies

The RewriteMachine supports multiple strategies:

- **Outermost**: Lazy, reduces outermost redex first
- **Innermost**: Eager, reduces innermost redex first
- **Optimal**: INet-style, no duplication of work

## Example: Compiling (λx.x) y

```
Source:     (app (lam x (var x)) (var y))

INet:       @@ ─── @λ
            │      │
            y      x─┐
                   └─┘

Bytecode:
  MATCH (interact @@ @λ)
  PUSH_ENV
  EMIT (wire (port @@ 1) (port @λ 1))  -- y connects to x's use
  POP_ENV
```

## Future Work

1. **Type-directed compilation**: Use types to guide sharing analysis
2. **Garbage collection**: Reclaim unreachable handles
3. **Parallel reduction**: Multiple redexes can fire simultaneously
4. **JIT compilation**: Specialize bytecode for hot paths
