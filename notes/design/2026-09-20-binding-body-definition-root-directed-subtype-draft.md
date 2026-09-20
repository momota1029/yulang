# Binding body to definition-root directed subtype slice

Status: Authoritative; construction complete (2026-09-20)

Approved by: user, 2026-09-20 (recommended integrated choice).

Date: 2026-09-20

Scope: the next Yulang3 type/effect vertical slice for admitted plain bindings:
an artifact-branded definition-root HIR API, its batch/solved value facts, and
one directed body-value-to-root relation for recovery-free integer bodies.

Related authority:

- `notes/design/2026-09-20-directed-subtyping-integer-slice-draft.md`;
- `docs/yulang3-architecture.md` §§3.1–3.8, 4.1, 5, 6.3, and 9–10;
- `2026-09-19-hir-simple-module-resolution-first-slice-draft.md`;
- the frozen `yulang2-oracle` body-lowering evidence, used only for semantic
  direction and phase separation.

Supersedes: the completed direct-root integer slice only where it makes
binding-body expressions component/fact-ineligible or defers the
definition/body relation. All direct-root behavior, kinds, artifact rules,
store/provenance authorities, physical graph, and other deferrals remain in
force.

Reviewed by: compiler-referee, specification, and performance M3 pre-approval
reviews on 2026-09-20; clean after scoped repairs.

## Evidence and boundary

The completed integer slice intentionally leaves binding bodies as total
`Unknown` projections. The established model gives a successful binding body
one additional directed fact:

```text
body.value <: definition.value
```

It does not relate the body's effect to a definition root. Definition
generalization and name-use scheme instantiation occur later; neither is an
equality relation or a reason to make the definition project exact `Int` now.

## Proposed gate

For every admitted plain binding, HIR mints an artifact-branded
`DefinitionRootId`, logically keyed by `(exact HirModule artifact, DefId)`,
and retains it on `HirBinding`. This is distinct from both the stable namespace
`DefId` and the body occurrence ID. `HirModule::owns_definition_root` and
`HirBinding::definition_root` are the only HIR discovery/query surface;
foreign roots are rejected and an admitted binding never has an absent root.

`ComponentId` becomes a tagged immutable owner key:
`Occurrence(HirOccurrenceId, Value|Effect)` or
`Definition(DefinitionRootId, Value)`. `ConstraintBatch` owns O(1) indexes
from each eligible occurrence/root to its component position. `SolvedModule`
owns an O(1) root-value projection index for every admitted root; an exact
artifact query returns that root's `Unknown`/solved value, while a foreign root
returns `ArtifactMismatch`. These indexes and their capacities are part of the
production allocation/retention counters. The physical graph remains
`yu-types -> yu-hir` and `yu-solver -> {yu-hir, yu-types}`; this gate adds no
`yu-hir -> yu-types` edge.

The batch allocates one `Value` component for each such root, including
duplicate definitions and bindings whose body is `Error`. It never allocates a
definition effect component.

Only a recovery-free binding-body `ResolvedExpr::Integer` becomes eligible for
the existing body value/effect components and four literal/pure-effect bounds.
It emits one fifth ordered occurrence:

```text
body.value <: definition.value
```

The body remains `(Int, EmptyEffect)`. The definition root remains `Unknown`:
the one-way lower bound is observable in the canonical store but is not a
generalized or public type projection.

Duplicate bindings retain distinct `DefId` ordinals, roots, components, and
body relations. Their diagnostics do not suppress local facts. A malformed,
missing, unsupported, or Name body retains its admitted root with `Unknown`,
emits no body relation or substitute fact, and cannot block a later valid
binding. Rejected targets, represented by `HirItem::Error`, have no definition
root.

No name-use edge, schemes, generalization, annotation, equality/back-edge,
definition effect, runtime/evaluation behavior, public type, or Core IR enters
this gate.

## Fact authorities

| Fact family | Identity and class | Sole writer / reader | Authority and lifecycle |
| --- | --- | --- | --- |
| definition root | `(artifact token, DefId)` immutable current fact | HIR lowering / artifact-bound HIR query | `HirModule`; retained on every admitted `HirBinding` |
| definition-value component | `(definition root, Value)` immutable current fact | collector / exact batch root query | `ConstraintBatch`; O(1) root index |
| body-to-root occurrence | `(body occurrence, BodyValueToDefinition)` append-only occurrence | collector / batch iteration | `ConstraintBatch`; distinct fifth local slot |
| semantic subtype fact | canonical `(lower term, upper term)` current deduplicated fact | transaction commit / `ConstraintStore` query | `ConstraintStore`; root relation is not a leaf-bound projection rule |
| committed cause edge | `(CauseId, FactId)` append-only provenance | receipt recorder / provenance query | provenance log; receipt-only, explanation derived |
| definition solved projection | `(definition root, Value)` immutable current result | reference-solver freeze / exact root query | `SolvedModule`; O(1) root index, `Unknown` is present rather than absent |

## Required tests and measurement

- `my x = 42` has body `Int/EmptyEffect`, one definition-value root projected
  `Unknown`, and exactly five ordered facts.
- two same-name bindings retain two roots and two body relations without merge;
  malformed and Name bodies remain `Unknown` without facts while a later valid
  binding solves.
- cross-artifact roots/components/queries reject; body and root identities do
  not alias.
- no name relation occurs for `my x = 42; x`.
- N/2N distinct integer bindings require 3N components, 5N emitted/admitted
  facts and provenance edges, 10N logical endpoint incidences, zero ordinary
  duplicates/CST rescans/parallel typed-tree copies, and less than 2.5x growth
  in production work, probes, root/component/canonical/receipt indexes,
  allocations, retained root projections, and temporary workspace bytes.
  Every root/component/canonical/consumed-receipt/solved-root index reports its
  own retained bytes as well as capacity; batch and solve temporaries do the
  same. A probe is a logical inspected key/candidate comparison, with separate
  counters for canonical admission and root/component index lookups. Root
  storage must use compact identity/reference fields with zero `DefId` payload
  clone bytes; HIR root allocation bytes are measured rather than treated as a
  zero-copy assertion.

## Approval choice

Recommended integrated choice: accept the artifact-branded definition root on
every admitted `HirBinding`, tagged occurrence-or-root component ownership,
O(1) batch/solved root indexes, the value-only one-way body relation,
duplicate/malformed policy above, and the intentionally `Unknown` definition
projection until a later generalization/public-type gate.

Alternative: defer binding semantics entirely. Reusing `DefId` without the
artifact brand, aliasing the body occurrence, adding a definition effect,
equality/back-edges, or inferring exact definition `Int` requires a separate
successor design.

## Stop conditions

Stop before implementation if this relation requires range identity, a CST
rescan, a parallel typed tree, unbranded `DefId`, body/root identity aliasing,
effect-root invention, equality, name/generalization shortcuts,
diagnostic-dependent fact suppression, or non-linear ordinary admission.

## Construction result

Construction is complete. Every admitted `HirBinding` now retains an
artifact-branded `DefinitionRootId`; solver components structurally distinguish
occurrence value/effect owners from value-only definition roots. Recovery-free
integer bodies emit their four literal/pure-effect facts followed by exactly
`body.value <: definition.value`. Definition projections remain explicitly
present `Unknown` values, while malformed and Name bodies emit no relation.

Duplicate roots remain distinct, foreign roots/components reject, definition
effects are unrepresentable, and same-artifact missing solved-root entries are
invariant failures rather than implicit `Unknown`. Receipt provenance, name
resolution, generalization, annotations, Core IR, and runtime behavior remain
outside this gate except for the existing receipt authority reused unchanged.

M3 compiler-referee, specification, and performance delta reviews are clean.
With `RUSTC_WRAPPER=`, 36 `yu-hir` tests and 9 `yu-solver` tests pass;
`cargo xtask check-graph`, `cargo check --workspace`, and `git diff --check`
pass. Separate 1,000/2,000 direct-root and binding witnesses retain the former
2N/4N/8N contract and prove the new 3N/5N/10N linear contract respectively.
