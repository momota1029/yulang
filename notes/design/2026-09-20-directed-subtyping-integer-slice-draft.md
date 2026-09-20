# Directed-subtyping integer slice

Status: Authoritative; construction complete (2026-09-20)

Approved by: user, 2026-09-20 (integrated choice 1).

Date: 2026-09-20

Scope: the first Yulang3 type/effect vertical slice, limited to a direct-root
decimal integer expression.  This proposal resolves neither declarations nor
names, generalization, annotations, applications, public interfaces, core IR,
or runtime behavior.

Related authority:

- `docs/yulang3-architecture.md` §§3.1–3.8, 4.1, 6.3, 6.9, 9–10;
- `2026-09-20-hir-direct-root-expression-slice.md` (which explicitly defers
  expression identity, types, constraints, effects, and evaluation);
- the frozen `yulang2-oracle` semantic corpus, used here as evidence for
  directed lower/upper bounds rather than as an implementation layout.

Supersedes: none.

Reviewed by: compiler-referee, specification, and performance M3 pre-approval
reviews on 2026-09-20; clean after scoped repair rounds.

## Problem and evidence

Yulang3 currently has no semantic type implementation: `yu-types` is an empty
boundary, `yu-solver` does not exist, and `ResolvedExpr` has no occurrence
identity.  A solved fact therefore cannot be attached to a particular HIR
expression by source range: equal and zero-width ranges are not unique.

The withdrawn equality-only `ConstraintBatch` experiment is not authority and
must not be restored.  The legacy semantic evidence instead uses directed
subtyping:

- an integer literal contributes `Int+ <: value` and `value <: Int-`;
- its pure computation contributes `Bottom <: effect` and
  `effect <: EmptyEffect`;
- a binding body contributes `body-value <: definition-root`;
- a name use is connected from an instantiated predicate to a fresh use value.

Thus exact literal knowledge is represented by two directed bounds, not by a
new equality relation.  `Unknown` represents unresolved facts; `Any` and
`Never` are never recovery fallbacks.

## Proposed first slice

The only accepted end-to-end witness is the existing direct-root source `42`.
It remains non-executable: no program-result or evaluation semantics are
introduced.

1. `yu-hir` assigns each lowered `ResolvedExpr`, including `Error`, one opaque
   occurrence ID unique within its exact immutable `HirModule`.  IDs use
   deterministic lowering/source order, never a source range or a re-walk
   traversal path.  `HirModule` receives a non-serializable opaque artifact
   token, and `SolvedModule` retains the exact `Arc<HirModule>` that minted its
   IDs.  ID-bearing constructors and queries carry that token: cross-artifact
   lookup is rejected rather than silently selecting another module's ID 0.
2. Only `HirItem::Expression(ResolvedExpr::Integer)` is eligible for this
   slice.  Each eligible occurrence receives value and effect components.
   Binding-body integers receive an ID but no components or constraints.
   Every Name state (resolved, unresolved, or ambiguous) and every Error,
   whether direct-root or binding-body, receives the total solved projection
   `(Unknown, Unknown)` with no substitute constraint.  This is not
   declaration/name typing.
3. `yu-types` owns exactly four kinded/polarized leaves: `Int+`, `Int-`,
   `EffectBottom+`, and `EmptyEffect-`.  Value and effect component identities
   are distinct kinds; cross-kind constraints are rejected before commit.
   `Unknown` is a `SolvedModule` result state, never a subtype leaf.  The
   exact pair `Int+ <: value <: Int-` projects `Int`; the exact pair
   `EffectBottom+ <: effect <: EmptyEffect-` projects pure/empty effect; an
   underconstrained interval projects `Unknown`.  Same-kind incompatible-bound
   solving is deferred until a second same-kind leaf has an accepted semantic
   fixture; this slice does not fabricate one merely to test an error path.
4. `yu-solver` collects four ordered subtype occurrences for each eligible
   expression `e`: `Int+ <: value(e)`, `value(e) <: Int-`,
   `EffectBottom+ <: effect(e)`, and `effect(e) <: EmptyEffect-`.
5. A deterministic reference solve freezes a `SolvedModule` for the same HIR
   artifact.  `42` projects exact `Int` and pure/empty effect; a failed
   component remains locally `Unknown` so independent later `42` occurrences
   still solve.

The logical phase direction remains `yu-syntax -> yu-hir -> yu-types`, with
`yu-solver` reading both HIR and types.  The physical Cargo graph follows the
existing `xtask` contract: this slice activates the normal
`yu-types -> yu-hir` manifest dependency and preserves
`accepts_the_planned_core_direction`; it does not add `yu-hir -> yu-types`.
No inferred-type field or synthetic HIR use is added merely to justify a
manifest edge.  HIR/types do not become independent siblings and inferred
facts do not enter HIR.

## Fact-authority registry

| Fact family | Identity key and class | Sole writer / reader | Authority and lifecycle |
| --- | --- | --- | --- |
| HIR occurrence | `(artifact token, occurrence ordinal)`; immutable current fact | `lower_module` / artifact-bound HIR query | `HirModule`; retained by `Arc`, never serialized or reused across artifacts |
| value/effect component | `(artifact token, occurrence, Value|Effect)`; immutable current fact | collector planning / artifact-bound batch query | `ConstraintBatch`; only eligible direct-root integers receive components |
| ordered constraint occurrence | `(artifact token, source ordinal, local slot)`; append-only occurrence | collector / batch iteration | `ConstraintBatch`; preserves every source occurrence and its `CauseId` |
| semantic subtype fact | canonical ordered `(lower term, upper term)`; current deduplicated fact | solve transaction commit / `ConstraintStore` query | `ConstraintStore`; `CauseId` is excluded from the key |
| committed cause edge | `(CauseId, FactId)`; append-only provenance | transaction receipt (accepted-fact and duplicate-occurrence deltas) / provenance query | compact provenance log; every duplicate cause is retained, explanations are derived and never eagerly built |
| solved value/effect | `(artifact token, occurrence, Value|Effect)`; immutable current projection | reference-solver freeze / artifact-bound `SolvedModule` query | `SolvedModule`; includes explicit `Unknown` and structured local solver errors |

The transaction alone admits canonical facts and emits receipts.  Batch,
store, provenance log, and solved projection therefore have distinct fact
classes rather than duplicated semantic authority.

## Explicit deferrals

No definition/body constraint, name-use propagation, scheme
generalization/instantiation, value restriction, annotation interpretation,
operator/application typing, state-slot relation, effect subtraction, row
residual, role predicate, import, public signature, or Core IR behavior enters
this slice.  In particular, it must not infer `Definition = Expression` or
use equality as a convenience relation.

## Required invariants and checks

- an occurrence ID is unique even for equal/zero-width ranges, includes Error,
  and cannot be used with another `HirModule`;
- only direct-root integers are eligible; binding-body integers and every
  Name/Error state retain total `(Unknown, Unknown)` projections without facts;
- all endpoints and components are kinded; cross-kind admission fails before
  commit; same-kind conflicts remain deferred with the absent second leaf;
- collection is one HIR traversal with no CST rescan or parallel typed tree;
- the batch is the ordered source occurrence record, the canonical store is
  the deduplicated semantic authority, the provenance log is a separate
  append-only cause authority, and explanations are derived;
- identical source produces identical constraint and solution order;
- `Unknown` survives malformed/unsupported/unresolved nodes, while a later
  valid `42` still solves;
- collection/solve work is linear in expressions plus emitted constraints.

Focused model tests cover lower/upper admission, duplicate semantic facts with
separate causes, cross-kind rejection, the empty-effect interval, Unknown
preservation, identity/artifact isolation, direct-root-only eligibility,
alpha-renaming/module-path independence, and deterministic order.
The vertical test covers source -> CST -> HIR -> batch -> solved module for
`42`, a binding-body integer, every Name state, and a malformed-or-unsupported
predecessor followed by `42`.

Production collect/admit/solve counters record HIR/CST traversals, HIR
clone/copy count and copied spelling bytes; emitted/admitted/duplicate facts;
canonical-map probes (inspected candidate/key comparisons, not lookup calls)
and rebuilds; generated/accepted/duplicate work items;
adjacency appends and visits separately; component/fact/occurrence allocations
and retained bytes (or capacities); provenance edges/bytes and eager
explanation builds; and maximum fan-out/SCC count.  The N/2N witness is source
with 1,000 and 2,000 direct-root `42` items.  It requires 4N emitted facts, N
occurrence IDs, 2N+O(1) components, zero ordinary duplicates, 4N provenance
edges, zero CST rescans/rebuilds/HIR or typed-tree copies, and less than 2.5x
growth in generated/accepted work, adjacency visits, allocations/retained
bytes, canonical-map probes, and map/index rebuilds.  Fan-out is diagnostic
only: shared leaves may legitimately reach N.  No timing gate is introduced
before these counts expose a material risk.

## Approval choices

The recommended integrated choice is:

1. artifact-scoped HIR occurrence IDs plus retained `Arc<HirModule>`, not a
   parallel typed tree or an owning clone;
2. the value and pure-effect components together, not a value-only API that
   must later reshape solved facts;
3. complete collection, reference solve, and `SolvedModule` projection, not a
   collection-only endpoint;
4. the existing one-way dependency graph, not permanent HIR/types siblings.

The alternative is to keep the type boundary entirely deferred.  A permanent
sibling graph or an equality-only relation would require a separate successor
design and cannot be inferred from this proposal.

## Stop and rollback conditions

Stop the gate before implementation if occurrence identity requires range
identity, a CST rescan, a retained parallel typed tree, a prelude/module graph,
equality, definition/name shortcuts, scheme-less propagation, `Any`/`Never`
recovery, duplicated semantic/provenance authority, or non-linear ordinary
admission.  Roll back the whole gate if any such condition appears.

## Construction result

Construction is complete. `yu-hir` now mints artifact-branded occurrence IDs
for every lowered `ResolvedExpr`, including equal zero-width Error ranges.
`yu-types` owns the four specified leaves; `yu-solver` owns direct-root integer
collection, exact-artifact batch/store/provenance/solution ownership, total
local-error `Unknown` projection, and the reference solve. The physical Cargo
graph is `yu-types -> yu-hir` and `yu-solver -> {yu-hir, yu-types}`.

Focused M3 evidence is clean: 35 `yu-hir` tests, 5 `yu-solver` tests,
`cargo xtask check-graph`, and `cargo check --workspace`, all with
`RUSTC_WRAPPER=`. The production N/2N 1,000/2,000 direct-root literal witness
asserts linear logical work and retained/workspace growth, including full
endpoint fan-out. No bindings, names, equality, generalization, annotations,
applications, Core IR, or runtime semantics entered this gate.
