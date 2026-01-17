# Attribute Grammar Implementation

**Status**: Phase 1 Complete ✅ (Core data types + catamorphism/paramorphism)

## Mathematical Foundation

Attribute Grammars are catamorphisms + paramorphisms over parse trees:

| Attribute Type | Algebraic Morphism | Direction |
|----------------|-------------------|-----------|
| **Synthesized** | Catamorphism (fold) | Bottom-up: `Fix F → A` |
| **Inherited** | Paramorphism | Top-down: carries context |
| **Both** | Hylomorphism | Anamorphism ∘ Catamorphism |

## Implementation Status

### Phase 1: Core Data Types ✅
- [x] `AttrFlow` enum: Syn | Inh | SynInh
- [x] `AttrRef` structure: attribute path + name
- [x] `AttrRule` structure: production + target + expression
- [x] `AttrDef` structure: name + flow + type + rules
- [x] `AttrEnv` structure: environment for computed attributes
- [x] `AttrLanguage` structure: Language + attributes

### Phase 2: Catamorphism Evaluation ✅
- [x] `evalSyn`: Synthesized attribute via catamorphism
- [x] `evalAttrExpr`: Expression evaluation in environment
- [x] `findRule`: Rule lookup by production

### Phase 3: Paramorphism Evaluation ✅
- [x] `evalInh`: Inherited attribute via paramorphism
- [x] `evalAttrs`: Combined two-pass evaluation

### Phase 4: Generic Morphisms ✅
- [x] `cataT`: Generic catamorphism over Term
- [x] `paraT`: Generic paramorphism over Term
- [x] `mapWithIndex`: Helper for indexed mapping

### Phase 5: Pushout Compatibility ✅
- [x] `AttrLanguage.pushout`: Coproduct of attribute algebras

### Phase 6: Grammar Syntax (TODO)
- [ ] Parse `attributes:` section in .lego files
- [ ] Parse `syn name : Type` declarations
- [ ] Parse `inh name : Type` declarations
- [ ] Parse `attr-rules:` section
- [ ] Parse `Prod.attr = expr` equations

### Phase 7: Integration with Redtt (TODO)
- [ ] Define type-checking attributes for Redtt
- [ ] Define scope/environment attributes
- [ ] Test on redtt example files

## Usage Example

```lean
-- Define a "depth" synthesized attribute
let depthAttr : AttrDef := {
  name := "depth"
  flow := .syn
  type := some (Term.var "Nat")
  rules := [
    { prod := "var", target := [], expr := Term.lit "0" },
    { prod := "lit", target := [], expr := Term.lit "0" },
    { prod := "lam", target := [], expr := Term.con "succ" [Term.var "$child1.depth"] }
  ]
}

-- Evaluate on a term
let term := Term.con "lam" [Term.var "x", Term.var "x"]
let env := evalSyn depthAttr term
```

## Key Files

- `src/Lego/Attr.lean`: Core attribute grammar implementation
- `Test.lean`: Attribute grammar tests (5 tests)

## Algebraic Laws

The pushout of attributed languages satisfies:
```
(L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂)
```

Where `A₁ ⋈ A₂` is the coproduct of attribute algebras:
- Productions from L₁ use A₁ rules
- Productions from L₂ use A₂ rules
- Shared productions need resolution (priority or merge)
