# RED-TODO (RedTT surface coverage vs Lego grammar)

This is a working checklist for aligning our Lego-based RedTT parsing with the *actual* RedTT frontend.
Reference sources:
- `redtt/src/frontend/Lex.mll` (lexer: keyword table + tokenization constraints)
- `redtt/src/frontend/Grammar.mly` (parser: Menhir grammar for surface `econ`)

Our current parser target is `examples/languages/red/RedttParser.lego` as used by `cabal test redtt-test`.

## Status

- [x] **Library benchmark**: `redtt-test` currently parses **725 / 725 = 100%** of the checked-in RedTT library declarations.
- [ ] **Frontend alignment**: this checklist is now about closing the gap between the Lego grammar and the *full* RedTT surface syntax (including forms not exercised by the library).

## Lexical / tokenization alignment

### Keyword set (audit)

Upstream RedTT has a fixed, global keyword table in `src/frontend/Lex.mll` (plus a special lexer mode for `import`).

From `Lex.mll` (as of `RedPRL/redtt` main), the keyword table includes:

- Decls / commands: `def`, `data`, `import`, `public`, `private`, `opaque`, `meta`, `debug`, `normalize`, `print`, `check`, `quit`
- Term constructors / syntax words: `let`, `in`, `where`, `with`, `begin`, `end`, `fun`, `lam`, `refl`, `elim`, `pair`, `fst`, `snd`, `coe`, `com`, `hcom`, `comp`, `V`, `vin`, `vproj`, `cap`, `box`
- Universes / kinds: `U`, `type`, `pre`, `kan`
- Unicode aliases: `λ` (lam), `→`/`->` (RIGHT_ARROW), `𝕀` (DIM), `⊢` (RIGHT_TACK), `∂` (BOUNDARY)

Current status in this repo:

- We *do not* globally classify these as keywords at lexing time for composed languages.
  - We tokenize into atoms (`TIdent` / `TSym`) and let the grammar match literals.
  - We reserve only a tiny structural subset (currently just `in`) so `<ident>` cannot greedily swallow key delimiters.
- We *cannot* naively “reserve all keywords” without also adding the upstream `import` lexer mode, because module path components like `data.nat` must be allowed as identifiers inside `import`.
  - Separately: we must not reserve non-keywords like `case` globally, because the library contains slash-qualified identifiers such as `le/case`.

Alignment options (future work):

- (A) Keep current approach (atoms + structural reservation) and document it as an intentional divergence.
- (B) Implement RedTT-style lexer mode for `import` so we can reserve the full keyword set without breaking module paths.

- [x] **Backtick**: RedTT treats backtick as a standalone token introducing a quoted internal term (`BACKTICK; t = tm`).
  - We now tokenize backtick as `TSym "`"` for composed languages (like RedTT), while keeping `.lego` backtick-delimited reserved literals.
  - Remaining: ensure quoted forms that occur in the library are actually accepted by `quoteexpr`.

- [ ] **Hole syntax**: RedTT supports `?` and `?name` holes (`HOLE_NAME`).
  - [x] Implemented in `RedttParser.lego` as `holeexpr ::= "?" [<ident>]`.

- [ ] **IMPORT tokenization**: RedTT lexes `import` specially, including a dot-separated module path.
  - We parse `importdecl` as `"import" modpath` with `modpath ::= <ident> ("." <ident>)*`.
  - Confirm this matches all library imports.

## Core surface constructs from `Grammar.mly` (econ)

### `elim` forms

RedTT supports:
- `elim [| ... ]` (function eliminator)
- `elim scrut [| ... ]`
- `elim scrut in mot [| ... ]`
- `elim in mot [| ... ]`

- [x] Add `elim … in …` motive support in [examples/languages/red/RedttParser.lego](examples/languages/red/RedttParser.lego)
- [ ] Confirm we also cover `with ... end` blocks (RedTT allows both `WITH ... END` and `[ ... ]`).
 - [x] `with ... end` blocks are supported as a second surface form (forward-compat), and covered by golden tests.

### Cubical systems (`pipe_block` / faces)

RedTT uses `pipe_block` with either:
- `with | ... end`
- `[| ... ]`

and within a face, cofibrations are disjunctions with `|`.

- [x] We support both `[| ... ]` and `with | ... end` as pipe-block surfaces.
- [~] We implemented a permissive `bdyformula` with internal `|` disjunction.
  - Risk: PEG greediness can accidentally absorb *outer* face separators.

  Current mitigation: keep “outer” separators structurally explicit (e.g. `pathconstrs`, `compconstrs`) and keep “inner” disjunction confined to `bdyformula(s)`.

### `let`

RedTT surface let is:

`let pat scheme = tm in body`

where `pat` supports split patterns (tuples) and wildcards.

- [~] We support:
  - `let x (args...) [:T] = tm in body`
  - `let (x, y, z, ...) = tm in body`
- [ ] Missing: wildcard/split patterns beyond flat tuples; confirm if used in library.
  - Note: parsing the current library does not require more than n-ary tuples + identifier binders.

### `V` / univalence primitives

RedTT surface has:
- `V x ty0 ty1 equiv` (as an atomic constructor)
- `vproj` projection, `cap` projection

- [x] `V` parses via a dedicated `vtype` production (not just generic application).
- [x] `.vproj` and `.cap` are accepted as projections.
- [x] Mirrored upstream’s tighter argument category split: added an `atomic` nonterminal and require `V`/`box`/`cap` arguments to be `atomic`.
  - Escape hatch: `atomic` includes parenthesized `("(" term ")")` for “atomic-but-complex” forms.

## Former “failure targets” (resolved in the library benchmark)

- [x] `let …` blocks: resolved for the library benchmark.

- [x] `elim [zero → ... | ...]` without a leading `|`: resolved for the library benchmark.

- [x] Paths/extensions: `[i j] A [| ... ]` are covered by `pathtype` + `bdyformula(s)` well enough for the library benchmark.

## Next alignment targets (not necessarily in the library)

- [x] Add holes: `?` / `?name` as `atom`/`term` according to `Grammar.mly`.
- [x] Add `with ... end` as an alternative surface for `pipe_block` constructs.
- [x] Audit univalence surface: ensure `V`, `vproj`, and associated forms match `Grammar.mly`.
- [ ] Decide a policy for “full Menhir equivalence” vs “library-driven permissiveness” (PEG ordering will differ).

## How to validate

- Run `cabal test redtt-test --test-show-details=direct` and check:
  - overall rate
  - sample failures (look for new dominant patterns)
- For a specific failing declaration, isolate it and run `parseProduction` on `Term.term` / `Term.atom`.

For frontend alignment work (beyond the library), add targeted golden tests that mirror specific `Grammar.mly` productions even if the RedTT library never triggers them.

