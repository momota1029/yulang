# Integer binding scheme and resolved-name instantiation slice

Status: Reviewed

Date: 2026-09-20

Scope: the next Yulang3 type/effect vertical slice for recovery-free integer
bindings and uniquely resolved value-name occurrences: positive lower-bound
closure, a closed value-only scheme, and per-use instantiation with a pure
lookup effect.

Related authority:

- `notes/design/2026-09-20-directed-subtyping-integer-slice-draft.md`;
- `notes/design/2026-09-20-binding-body-definition-root-directed-subtype-draft.md`;
- `notes/design/2026-09-19-hir-simple-module-resolution-first-slice-draft.md`;
- `notes/design/2026-09-20-hir-direct-root-expression-slice.md`;
- `docs/yulang3-architecture.md` §§3.1–3.8, 4.1–4.2, 5, and 6.1–6.8;
- frozen `yulang2-oracle@a58eefc31e22141574b6f20c6a5748151`, used only
  for semantic direction, value classification, and phase separation:
  `crates/infer/src/typing.rs:12-105`,
  `crates/infer/src/lowering/expr/constraints.rs:7-89`,
  `crates/infer/src/lowering/name_ref.rs:83-115`, and
  `crates/infer/src/analysis/session/instantiate.rs:14-83,342-520`.

Supersedes: the completed integer and binding-root slices only where they
defer positive bound closure, schemes, and resolved-name components/facts.
Their identity, artifact, direction, store, provenance, recovery, and physical
dependency contracts otherwise remain in force.

Drafted by: primary with an independent architect and bounded legacy-evidence
exploration on 2026-09-20.

Review history: compiler-referee, specification, and performance M3
pre-approval reviews closed the original draft on 2026-09-20. A subsequent
legacy-representation audit found that its `Int+` scheme payload conflated a
solver bound leaf with a canonical scheme body. The corrected `Int`-scheme
revision passed fresh compiler-referee and specification review; the unchanged
performance review carries forward. User approval remains required.

## Evidence and semantic boundary

For the existing accepted fixture:

```yu
my x = 42;
x
```

the established directed chain is:

```text
Int+ <: body.value <: definition.value
body.value <: Int-
EffectBottom+ <: body.effect <: EmptyEffect-
```

The frozen semantic oracle generalizes the positive predicate reachable from
the definition root, then gives every resolved name use a fresh value and
effect. Instantiation contributes one directed value fact:

```text
instantiated positive predicate <: use.value
```

It does not add the reverse edge. A name lookup independently has an exact
pure effect. Generalization is value/non-expansiveness restricted; an empty
effect is not itself evidence that an expression is non-expansive.

The current Yulang3 solver projects exact `Int` only when both `Int+` and
`Int-` bound the same component. Therefore this gate deliberately projects a
resolved name use as `(Unknown, EmptyEffect)`. Adding `use.value <: Int-`, a
reciprocal relation, equality, or an exact-type projection shortcut would be a
different semantic decision without current authority.

The existing Yulang3 name-resolution policy remains authoritative. Duplicate
definitions keep distinct roots and make a use ambiguous; the frozen oracle's
nearest-duplicate selection is not copied. Ambiguous and unresolved names
remain total HIR name states and stay `(Unknown, Unknown)`.

## Proposed integrated gate

### Ownership and identity

- `HirModule` remains the sole authority for exact artifact identity,
  `DefId`, `DefinitionRootId`, resolution, and occurrence ownership.
- `yu-types` owns an immutable `ClosedValueScheme`. In this slice it has zero
  binders and canonical semantic body `ClosedValueType::Int`. It does not store
  a solver leaf or a polarity suffix.
- A scheme's semantic identity is its existing artifact-branded
  `DefinitionRootId`; no parallel `SchemeId` or raw-`DefId` scheme key is
  introduced. Equal payloads on duplicate roots remain distinct schemes.
- `ConstraintBatch` owns components, integer generalization candidates, and
  resolved-name instantiation requests for the exact HIR artifact.
- `ConstraintStore` remains the sole authority for committed directed subtype
  facts. A scheme is a frozen canonical type derived from the root's positive
  lower closure, not a second mutable bound authority. The solver alone lowers
  `ClosedValueType::Int` back to `Leaf::IntPositive` when instantiating a use.
- `SolvedModule` owns the exact-artifact O(1) root-to-scheme projection and the
  existing occurrence value/effect projections.

`SolvedModule` retains exactly one dense `DefinitionSchemeState` for every
admitted root, in root order:

```text
Generalized(ClosedValueScheme)
NotGeneralized(NotGeneralizedReason)
```

The bounded reasons distinguish ineligible body shape and failed required
ordinary facts. `SolvedModule::scheme_state_for(root)` is a
decisive-one, artifact-checked query returning the retained state. A foreign
root returns `ArtifactMismatch`. Construction fails with an invariant
availability error if an exact-artifact admitted root has no state; this can
never degrade to `NotGeneralized`. Identity exhaustion, a resolved `DefId`
without an owned root, and broken candidate/component ownership likewise fail
collection or solve availability before a frozen product is returned.

### Eligibility and value restriction

Every admitted plain binding whose recovery-free body is exactly
`ResolvedExpr::Integer` is a candidate, independently of `my`/`our`/`pub`
visibility and independently of a duplicate-definition diagnostic. This is a
bounded syntactic non-expansiveness classification for the only supported
expression family. The body's exact empty effect is a validation invariant,
not the general value-restriction predicate. A candidate freezes to
`Generalized` only if all five required ordinary relations were successfully
admitted, no body or root component is failed, the body projects exactly
`(Int, EmptyEffect)`, and the positive closure contains `Int+` at its definition
root. An ineligible body or failed ordinary fact produces one
`NotGeneralized` reason for that root. It suppresses only that scheme and its
uses' value facts; those resolved uses retain their independent pure-effect
facts, and later candidates continue. Once all five facts are admitted and the
components/body projection are valid, absence of the mathematically required
root closure is a solver invariant availability failure; it never becomes a
recoverable `NotGeneralized` state or a frozen `SolvedModule`.

Malformed, unsupported, Error, or Name binding bodies produce no scheme in
this gate. In particular, `my x = 42; my y = x; y` does not silently extend
generalization to alias bodies: `x` may receive a pure lookup effect, but `y`
has no scheme and its use remains value-unknown.

### Collection and forward references

Collection performs one HIR traversal. It allocates all existing binding
roots/components/facts, records integer candidates, creates components for
uniquely resolved name occurrences, and records pending instantiation
requests. An ephemeral exact-artifact `DefId -> DefinitionRootId` index is
built during that same traversal with borrowed/shared HIR keys. After traversal,
forward requests are joined against the completed index without rescanning HIR
or CST. New batch and temporary storage retain zero cloned `DefId` payload
bytes; this claim does not include the HIR's pre-existing resolved-name payload.
Requests retain only shared/artifact-root identity. A collection counter
records exact zero new `DefId` clone bytes, target-key hash bytes, forward-index
probes/capacity/modeled slot bytes, and peak index/request workspace.

Only `NameResolution::Resolved(target)` receives fresh occurrence value and
effect components. The retained request uses the exact target root, not the
raw `DefId`. Ambiguous and unresolved names receive no components or facts and
keep their existing total unknown projection.

### Minimal positive-bound closure

The reference solve adds only the closure required by the existing fifth
relation:

```text
Int+ <: body.value
body.value <: definition.value
--------------------------------
Int+ is a lower bound of definition.value
```

It constructs an outgoing component adjacency index only from accepted
admission deltas/receipts and maintains a FIFO work queue keyed by
`(component, positive value leaf)`. Every key is accepted once. It never builds
closure by iterating `ConstraintStore::facts()` after admission. Ordinary facts
are admitted in source/local-slot order, positive lower-bound deltas are
drained, and candidate schemes are frozen in binding/root order.

This gate adds no upper-bound propagation, lower-by-upper pair materialization,
SCC scheduler, recursive/open scheme, role predicate, effect-row closure, or
full-store replay. Definition-root solved values remain `Unknown`; positive
lower closure is enough to construct a canonical `Int` scheme but not enough to
claim an exact solved value.

### Instantiation and effects

After scheme freezing, requests are planned and validated, then committed in
name-occurrence order. The post-freeze endpoint fence permits only admitted
leaves and the request's own occurrence components; no definition/body
component or component-to-component edge may be committed after the freeze.
All request ownership, endpoints, identities, capacity, and source-link inputs
are validated before its per-request atomic commit. A fulfilled request lowers
the canonical scheme body to its directed lower endpoint and emits exactly one
value relation:

```text
Int+ <: use.value
```

The zero-binder scheme needs no fresh semantic predicate component, but every
use still owns distinct fresh value/effect occurrence components and a distinct
request/cause. `ClosedValueType::Int -> Leaf::IntPositive` is a solver-owned
one-way instantiation conversion, not a stored `Int+` scheme payload or a
live-root-to-use shortcut.

Every uniquely resolved name lookup independently emits:

```text
EffectBottom+ <: use.effect
use.effect <: EmptyEffect-
```

These effect facts do not depend on successful generalization. A resolved use
of a nongeneralized target therefore stays value-`Unknown` but projects an
`EmptyEffect`. No definition effect or scheme effect exists.

Name constraint occurrence slots are fixed:

```text
slot 0: instantiated positive predicate <: use.value (only when fulfilled)
slot 1: EffectBottom+ <: use.effect
slot 2: use.effect <: EmptyEffect-
```

Slots 1 and 2 never renumber when slot 0 is absent. The global admission order
is also fixed: first all ordinary binding and name-effect facts in
source-occurrence/local-slot order; then positive closure and scheme freeze;
then fulfilled name-value facts in name-occurrence/slot order. Thus
`my x = 42; x` admits binding slots 0-4, name slots 1-2, then name slot 0;
`x; my x = 42` admits name slots 1-2, binding slots 0-4, then name slot 0. A
resolved use of a nongeneralized target has only slots 1-2.

For `my x = 42; x`, the exact observable result is:

- body: `(Int, EmptyEffect)`;
- definition root value: `Unknown`;
- root scheme: zero-binder canonical value scheme `Int`;
- name use: `(Unknown, EmptyEffect)`;
- eight admitted facts in the global order above: five existing binding facts,
  two name-effect facts, then one instantiated value fact.

### Provenance and fact authorities

| Fact family | Identity and class | Sole writer / reader | Authority and lifecycle |
| --- | --- | --- | --- |
| positive adjacency | accepted `(lower component, upper component)` arcs, derived index | admission receipt / closure queue | solve-session-only; appended once from committed deltas, never rebuilt or updated after freeze |
| positive root bound | `(root component, positive leaf)` immutable frozen summary | solve delta closure / generalization planner | derived from accepted receipts; frozen before endpoint fence, retired with solve workspace |
| definition scheme state | every `DefinitionRootId` maps to exactly one `Generalized`/`NotGeneralized` state | generalization freeze / `scheme_state_for` decisive-one query | `SolvedModule`; `Generalized` owns `ClosedValueType::Int` from `yu-types`, exact artifact lifetime |
| scheme instantiation conversion | `ClosedValueType::Int -> Leaf::IntPositive` derived one-way lowering | request planner / transaction plan | `yu-solver`; no persistent duplicate bound authority or public scheme payload containing `Int+` |
| instantiation request | `(name occurrence, target root)` append-only batch occurrence | collector / solve planner | `ConstraintBatch`; exact-artifact only |
| instantiated subtype fact | canonical `(positive predicate, use value)` current fact | transaction commit / store query | `ConstraintStore`; deduplicated semantic authority |
| instantiated cause edge | `(CauseId, FactId)` append-only provenance | transaction receipt / provenance query | existing provenance log |
| instantiation source link | `(CauseId, target root, FactId)` append-only compact provenance | fulfilled value-relation receipt / `instantiation_source_for(cause)` decisive-one query | `SolvedModule`; exactly one per fulfilled request, none for effect/unfulfilled requests, exact artifact lifetime |

Every generated semantic relation passes through the existing plan, validate,
per-request atomic commit, receipt, and provenance path. The source link is
created only from the committed value-fact receipt; if canonical admission
deduplicates a fact, each distinct cause still has one link to that shared
`FactId`. A missing link for a fulfilled retained cause is an invariant error;
an unfulfilled/effect cause returns `None`; a foreign cause is rejected. The
source-link index reports allocation, capacity, modeled retained bytes, and
query probes. Explanation remains lazy and all these views retire with their
exact `SolvedModule`. Hash tables are lookup-only; deterministic order is the
explicit global admission order, root order, FIFO delta order, then request
order.

## Failure and recovery

- A resolved use whose target has no scheme emits no substitute value fact;
  it remains locally value-`Unknown`, retains the pure lookup effect, and does
  not block later valid candidates or uses.
- Ambiguous and unresolved names remain `(Unknown, Unknown)` and emit nothing.
- Failure of any candidate body value fact, body effect fact, or body-to-root
  fact produces `NotGeneralized` for that root. Its uses keep pure effects and
  no value fact; independent later candidates and uses continue. A missing
  required closure delta after successful fact admission is an invariant
  availability failure and prevents freezing the whole solve result.
- A missing exact-artifact target root for `Resolved(DefId)`, broken candidate
  ownership, identity exhaustion, or a foreign artifact is an availability or
  invariant failure, never semantic `Unknown`.
- `Any`, `Never`, equality, reciprocal facts, direct root-to-use propagation,
  and guessed exact `Int` are forbidden recovery shortcuts.

## Required tests

Focused semantic fixtures:

- `my x = 42; x`: exact contract and admission sequence above; its structural
  scheme query returns `Generalized(ClosedValueScheme { binders: [], body:
  ClosedValueType::Int })`, its display is `Int` with no polarity suffix, and
  only the solver-owned instantiation conversion produces
  `Leaf::IntPositive <: use.value`;
- `x; my x = 42`: exact forward admission sequence above;
- `my x = 42; x; x`: one scheme, distinct use components and causes;
- `my bad = @; bad; my good = 42; good`: local recovery isolation;
- `my x = 1; my x = 2; x; my good = 42; good`: distinct duplicate-root
  schemes, no scheme use for the ambiguous occurrence;
- `my x = 42; my y = x; y`: no alias generalization or implicit body/root
  extension;
- `my x = 1; our y = 2; pub z = 3; x; y; z`: visibility independence without
  public-interface work;
- the same source lowered twice: cross-artifact scheme/request/component
  rejection.
- injected failure of one body-value fact, one body-effect fact, and the
  body-to-root fact, each followed by an independent valid candidate/use:
  exact dense state, source-link absence, retained pure use effect, and local
  failure isolation.
- an invariant harness that admits all five valid facts but suppresses the
  required root closure delta: solve availability fails and no `SolvedModule`
  or recoverable `NotGeneralized` state is returned.

Tests assert exact edge direction, the structural scheme payload/conversion
boundary above, absence of reverse/equality/definition effect facts, definition
roots remaining `Unknown`, resolved-name value remaining `Unknown`, resolved-name
effect becoming `EmptyEffect`, deterministic ordering, query cardinality,
artifact isolation, forward references, alpha/path independence, and zero
HIR/CST rescans or parallel typed-tree copies.

The N/2N witness uses 1,000 and 2,000 unique pairs `my x_i = 42; x_i`. For N
pairs it requires 5N components, 8N emitted/admitted facts and fact-provenance
edges, 16N logical endpoint incidences, N candidates, schemes, requests,
instantiation source links, actual body-to-root positive arcs, adjacency
appends, and adjacency visits. Binding seeds plus propagated root deltas are
exactly 2N generated/accepted closure items with zero duplicates; instantiated
use lower facts are counted separately as N post-freeze seed observations and
never enter the frozen closure queue. Forward-index and scheme-index probes are
exactly N each. Full-store relation scans/replays after admission and per-use
store-fact visits are exactly zero. It also requires zero ordinary fact
duplicates, CST rescans, HIR/typed-tree copies, SCC work, and eager explanation
builds.

Generated/accepted/duplicate lower-bound work, endpoint incidences separately
from actual adjacency appends/visits, canonical probes/rebuilds,
request/root/scheme/component indexes, allocation counts, exact capacities,
modeled retained slot bytes, source-link storage, target-key hash bytes,
collection-specific `DefId` clone bytes, and peak temporary workspace must each
grow by less than 2.5x from N to 2N. A closed scheme uses an inline fixed
predicate field and performs no per-scheme payload heap allocation; otherwise
payload allocations and bytes must be counted. Closure counters are local
plain integers frozen once, not atomics on each hot-path transition. The
algorithmic target is expected-amortized
`O(items + facts + accepted positive deltas + uses + total hashed-key bytes)`
with linear retained and temporary slots. A long-identifier companion witness
checks that key-byte work follows total spelling bytes. No timing benchmark is
required unless these counters expose a material unresolved risk.

## Explicit deferrals

No general non-expansiveness classifier, computed-binding generalization,
alias scheme, quantified variable, recursive/open/SCC scheme, upper-predicate
instantiation, annotation, operator/application typing, import, public
interface, Core IR, runtime behavior, definition effect, or exact name-value
projection enters this gate.

## Approval choice

Recommended integrated choice: accept integer-only candidate eligibility,
positive lower-bound closure, an artifact-root-keyed zero-binder canonical
`Int` scheme, solver-owned lowering to the `IntPositive` constraint endpoint at
each use, independent pure lookup effects, and the deliberate current-Yulang3
observable `(Unknown, EmptyEffect)` name result. The last projection is a new
Yulang3 solved-module contract, not a legacy per-use projection claim.

Alternative: defer generalization and resolved-name typing entirely. Exact
`Int` at a name occurrence is not a safe sub-option of this proposal: it needs
a separate design for an upper fact or a different solved-projection contract.

## Stop and rollback conditions

Stop before implementation if the slice requires equality/back-edges, a
definition effect, a raw-`DefId` scheme identity, source-order-dependent forward
resolution, another HIR/CST traversal, a parallel typed tree, a full SCC
scheduler, per-use store scans, or generalization of non-integer bodies.

Roll back the gate if the one-way instantiation cannot preserve the exact
observable contract, deterministic transaction order, artifact isolation, or
the N/2N production-counter bound.
