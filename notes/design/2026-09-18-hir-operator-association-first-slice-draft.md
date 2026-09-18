# First HIR slice: operator-chain association

Status: Draft

Date: 2026-09-18

Scope: the first `yu-hir` slice required by Gate 3 of
`2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`. It defines
the association-phase input/output and the minimal HIR product for one accepted
fixture. It does not define the module graph, stable `DefId`s, name resolution,
type/effect representation, solver, or core IR.

Supersedes: none

## Authority and current state

- `docs/yulang3-architecture.md` (Authoritative) fixes the phase model:
  `Resolve / Lower: ParsedFile + imported interfaces -> HirModule`, with
  `yu-hir` owning "source file, module, stable `DefId`, resolved name, HIR".
- `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` (Authoritative,
  "Association phase contract") fixes the association phase:

  ```text
  ParsedFile + exact OperatorAssociationEnvironment
      -> associate_operator_chains
      -> HirModule containing precedence-shaped applications
      -> type inference / solving
  ```

  It states the association owner is `yu-hir`'s syntax-to-HIR lowering (or a
  dedicated pre-HIR module that `yu-hir` alone calls), that association is not
  type inference, and that neither `yu-syntax` nor the solver holds a second
  association authority.
- `crates/yu-hir` and `crates/yu-types` are empty boundaries. There is no
  concrete HIR node schema or `HirModule` shape in `notes/` or `docs/`.
- Gate 2 is implemented: `ParsedFile` retains the exact effective
  `Arc<OperatorTable>` the parser used and exposes `operators()`.

## Why this is the bounded first slice

The full `HirModule` (module graph, `DefId`s, name resolution, declarations) is
a large durable decision. Gate 3 asks for the smallest accepted fixture that
exercises source -> Rowan CST -> HIR so implementation can expose missing
design. The association contract is the one piece with an already Authoritative,
bounded, testable specification.

The slice is defined as a whole-CST walk, not a declaration lowering: it visits
every `OperatorChain` in the Rowan tree and associates it. Declaration
structure, names and types stay unlowered, so the slice needs no `DefId` model
and does not guess the eventual `HirModule` shape. This mirrors the Gate 1
shadow walk: a total structural pass with source provenance.

## Decisions required before implementation

- **D1 `yu-hir` dependency direction.** The architecture graph is
  `yu-syntax -> yu-hir -> yu-types`. This slice needs only `yu-syntax`.
  - D1a: add `yu-syntax` as a `yu-hir` dependency now.
  - D1b: place the associator in a temporary module outside `yu-hir` until the
    `yu-hir` public surface is designed.
- **D2 first public product.**
  - D2a: introduce `HirModule` immediately as the phase product, initially
    holding only the associated chains.
  - D2b: introduce a narrower pre-HIR product (e.g. `AssociatedChains` /
    `associated_expression`) and defer `HirModule` until declarations and names
    exist.
- **D3 associated expression representation.**
  - D3a: a recursive owned tree (`HirExpr::Apply { operator, operands, range }`)
    with source ranges.
  - D3b: an arena/indexed representation with stable node ids.
  The association contract only requires a deterministic precedence-shaped tree
  with source provenance; it does not require ids yet.
- **D4 first fixture.** Candidates under `tests/contracts/stable-core/v0/`:
  `run/vm/pass/example_types` (8 lines: `our twice x = x + x`, `twice 21`,
  `answer`), `run/vm/pass/example_nondet_all` (6 lines: infix `+` inside a
  parenthesized projection), `run/vm/pass/path_display` (2 lines: projections
  only), and the one-line `1` fixtures (no `OperatorChain`). The fixture must
  contain at least one `OperatorChain` for the slice to be meaningful.

## Proposed default for review

D1a, D2b, D3a, and `run/vm/pass/example_types`.

Rationale: keep the first durable public surface small and reversible, avoid
guessing the eventual `HirModule` shape, and still exercise both infix
association (`x + x`) and nested application (`twice 21`).

## Observable contract for the slice

Taken directly from the association phase contract:

- one pass over each `OperatorChain` in source order;
- prefix right BP, infix left/right BP and suffix left BP read from the
  canonical retained table and compared lexicographically;
- call / index / field / projection / path and `MlArgument` are reserved
  structural postfix handled before dynamic comparison;
- `TypeAnnotationTail` reduces all pending dynamic segments before the
  annotation;
- nested `MlArgument` chains associate first and apply left in source order
  (`f x y` becomes `(f x) y`) without writing that nesting back into the CST;
- the same flat item sequence and association environment deterministically
  produce the same tree;
- no CST mutation and no `yu-syntax` association authority.

## Out of scope

Declarations, patterns, types, effects, name resolution, `DefId`s, module graph,
constraint collection, solver, diagnostic publication, and any CST or
`syntax-v0` change.

## Open questions for the user

1. D1-D4 choices.
2. Should the first slice stop at association, or also produce a trivial
   placeholder type for the fixture to touch `yu-types`?
3. Is `example_types` the right fixture, or should the slice use a fixture
   whose operator chain is the top-level statement (`example_nondet_all`)?
