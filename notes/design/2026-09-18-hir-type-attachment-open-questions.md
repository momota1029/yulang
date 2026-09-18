# HIR type attachment — open questions memo

Status: Draft (exploratory memo; records no decision)

Date: 2026-09-18

Scope: captures the unresolved question "how does a type get attached to an
associated HIR expression?" so the approved association slice can proceed
without deciding it. This memo proposes no binding decision and authorizes no
implementation.

Related: `2026-09-18-hir-operator-association-first-slice-draft.md` (approved
2026-09-18), `docs/yulang3-architecture.md` phase model,
`2026-08-20-yu-syntax-chasa-architecture.md` association phase contract.

Supersedes: none

## Why this is open

- The architecture phase model is
  `HirModule -> ConstraintBatch -> SolvedModule -> PublicInterface/CoreModule`,
  with `yu-types` owning canonical type/effect nodes, schemes and public types,
  and `yu-solver` owning constraint collection and solve. Neither `yu-solver`
  nor `yu-compiler` exists in the workspace yet; `yu-types` is an empty
  boundary.
- `HirModule` is described as holding the resolved declarations and expressions
  plus per-node error markers; `SolvedModule` holds solved and unsolved facts
  together, with `Unknown` placeholders, and never uses `Any`/`Never` for
  recovery.
- The approved association slice (D3a) produces a recursive owned expression
  tree with source ranges and no stable node ids.

## The concrete tension

Attaching a type requires a stable identity for the expression the type belongs
to. D3a provides source ranges but no ids, and source ranges are not unique:
repeated occurrences and zero-width `Missing`/recovery nodes are both valid, so
a range cannot name one expression. A solver-side type map therefore needs one
of:

- D3a plus a derived identity (traversal ordinal or occurrence path), which is
  fragile across any re-association or incremental reuse;
- D3b after all (arena/indexed tree with stable ids);
- a solver that re-walks HIR and produces a parallel typed tree, so no HIR-side
  identity is needed.

This is the point that currently prevents "how a type attaches" from being
visible.

## Where a type could live

- **On the HIR node.** Conflicts with the architecture's immutable phase outputs
  and with solve being a later, separate phase.
- **In `SolvedModule`, keyed by a HIR identity.** Matches the phase model, but
  needs the identity above.
- **Nowhere in HIR.** HIR keeps only declared syntax facts; types exist only in
  the solved and public products.

## Prerequisite order

A meaningful type slice needs resolved names and declarations first: typing
`x + x` requires knowing what `x` is. A resolve/name slice (`DefId`, scopes)
therefore plausibly precedes any type attachment, and the approved association
slice deliberately provides neither. The smallest type-attachment fixture can
only be chosen after that slice exists.

## Open questions

1. Does the first type slice require D3b (stable ids) instead of D3a?
2. If a HIR-side identity is acceptable, is a traversal ordinal or occurrence
   path enough, or must it be an arena id?
3. Where is the boundary between declared syntax type facts (annotations,
   operator signatures) and solved types?
4. Does the first type slice need `yu-solver`, or can a trivial direct fact
   (for example "a decimal integer literal is `int`") live in `yu-types` plus
   `yu-hir` without the solver?
5. What is the smallest accepted fixture that exercises type attachment
   meaningfully once names exist?

## Non-goals

No decision, no `yu-types` or `yu-solver` API, no HIR schema, and no change to
the approved association slice.
