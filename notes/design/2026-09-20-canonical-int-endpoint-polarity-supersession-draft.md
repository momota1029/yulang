# Canonical `Int` and endpoint-polarity supersession

Status: Reviewed

Date: 2026-09-20

Reviewed by: compiler-referee, specification, and performance M3 pre-approval
reviews on 2026-09-20; clean after one bounded repair/delta round.

Scope: correct the completed first integer and binding-root type slices where
they reify Simple-Sub endpoint polarity as distinct primitive leaf identities.
This proposal establishes one canonical value type `Int`, position-typed
subtype endpoints, canonical interval projection, and compatibility rules for
the already implemented body-to-definition-root relation. It does not add name
typing, schemes, annotations, operators, Core IR, or runtime behavior.

Upon user approval, this successor supersedes:

- `2026-09-20-directed-subtyping-integer-slice-draft.md` only in its
  four-polarized-leaf representation, uniform `Term` endpoint representation,
  exactness matching, related test contract, and construction-result claims;
- `2026-09-20-binding-body-definition-root-directed-subtype-draft.md` only
  where it relies on those endpoint representations;
- the unimplemented
  `2026-09-20-integer-binding-scheme-name-instantiation-draft.md` as an active
  implementation candidate until it is rewritten on this repaired foundation.

The current user decision immediately withdraws the unapproved scheme/name
proposal as an implementation candidate. The existing Authoritative records
remain historical and authoritative until this successor is approved; their
completed construction facts are not rewritten. All occurrence/root identity, HIR ownership, component ownership, directed
body-to-root relation, artifact checks, canonical store, receipt provenance,
total local-error behavior, deterministic source order, and measurement
contracts remain in force unless this document states otherwise.

## User decision and evidence

The user requires that the internal representation of the primitive is itself
`int`, not `int+` or `int-`.

The frozen `yulang2-oracle@a58eefc31e22141574b6f20c6a5748151` has one
constructor payload `int`. `Pos::Con(path, args)` and `Neg::Con(path, args)`
are lower- and upper-endpoint grammars carrying the same constructor payload;
`Neu::Bounds(lower, upper)` represents an interval rather than a third integer
type. See `crates/poly/src/types.rs:60-95,736-826`,
`crates/infer/src/lowering/expr/constraints.rs:40-89`,
`crates/infer/src/lowering/expr/block_local.rs:1309-1325`, and
`crates/infer/src/constraints/machine/entry.rs:493-499`.

This is also the relevant Simple-Sub boundary: polarity controls a type's
constraint position, traversal, and variance; it is not nominal identity for
primitive types.

## Correct representation

`yu-types` owns one canonical primitive identity:

```text
ValueType::Int
```

There is no `IntPositive`, `IntNegative`, or `IntNeutral` type identity.
Effects retain semantically distinct `EffectType::Bottom` and
`EffectType::EmptyRow` forms, but their lower/upper position is likewise not a
suffix embedded in their identity.

`yu-solver` owns endpoint position. Facts make lower/upper-side inversion
unrepresentable through separate endpoint sorts with side-specific effect
forms:

```text
LowerTerm ::= Type(ValueType) | Effect(EffectLower::Bottom) | Component(ComponentId)
UpperTerm ::= Type(ValueType) | Effect(EffectUpper::EmptyRow) | Component(ComponentId)
SubtypeFact { lower: LowerTerm, upper: UpperTerm }
```

Endpoint constructors are private to the solver planner. `EmptyRow` cannot be
placed in a lower endpoint and `Bottom` cannot be placed in an upper endpoint.
`ValueType::Int` is legal on both sides because it is one canonical type viewed
at distinct positions. Component-kind mismatch remains the named structured
local `CrossKind` error, rejected before commit; its endpoint components are
marked failed while independent later facts continue. A generic uniform `Term`
plus advisory polarity metadata is forbidden.

For this bounded slice, direct literal constraints become:

```text
LowerTerm::Type(Int)       <: UpperTerm::Component(value)
LowerTerm::Component(value) <: UpperTerm::Type(Int)
LowerTerm::Effect(Bottom)  <: UpperTerm::Component(effect)
LowerTerm::Component(effect) <: UpperTerm::Effect(EmptyRow)
```

The body relation remains exactly:

```text
LowerTerm::Component(body.value) <: UpperTerm::Component(definition.value)
```

The ordered occurrence slots, semantic fact count, and cause/provenance rules
remain unchanged.

## Bounds and projection

The solver retains side-specific membership of the same canonical `Int`:

```text
Int in lower(value) and Int in upper(value) => solved value Int
Int only in one side                         => solved value Unknown
```

This is an interval projection, not equality and not a third neutral integer
type. A definition root with only the body-derived lower bound remains
`Unknown`. The same rule holds for future positive-only name instantiation:
placing canonical `Int` in a use's lower endpoint alone does not authorize
exact `Int` at the use.

The reference solver must never admit then ignore an illegal endpoint.
Lower/upper-side inversion is structurally unconstructable through its endpoint
API; component-kind mismatch is the structured local `CrossKind` error above.
`Unknown`,
`Any`, and `Never` remain outside endpoint vocabulary.

## Authority and lifecycle

| Fact family | Identity and authority | Lifecycle |
| --- | --- | --- |
| canonical primitive | `ValueType::Int`; `yu-types` sole owner | immutable canonical identity |
| lower/upper endpoint | position wrapper plus canonical type/component; solver planner and transaction | batch/store fact lifetime |
| semantic subtype fact | canonical ordered `(LowerTerm, UpperTerm)`; `ConstraintStore` | deduplicated current semantic authority |
| interval summary | `(component, canonical type, side)` derived from committed facts | solve workspace, frozen only through `SolvedModule` projection |
| solved value | artifact/occurrence or root projection; `SolvedModule` | immutable exact-artifact product |

No separate polarity-indexed primitive cache, no copied interval authority, and
no scheme-derived shortcut may be introduced.

## Construction gates

### R1 — canonical endpoint and binding migration

Replace the current polarized leaf representation and uniform `Term` in
`yu-types` and `yu-solver` with canonical type identities and position-typed
endpoints. In the same compilable construction gate, migrate the existing fifth
body-to-root relation mechanically. Rework direct-root exactness, local error
handling, receipts, provenance, public constraint queries, and focused tests.
Preserve four source occurrences for each direct integer, five for each eligible
binding, and every existing source/local-slot order.

### R2 — binding-root behavioral recertification

Re-certify the migrated fifth relation: duplicate roots, malformed/Name body
isolation, foreign artifact rejection, root `Unknown`, and direct/binding N/2N
contracts. This gate adds no name or scheme behavior.

### R3 — later scheme/name redesign

Create a replacement for the withdrawn historical scheme/name proposal only after R1/R2 are
complete. A future zero-binder scheme may store canonical `Int`; instantiation
places its positive projection into `LowerTerm::Type(Int)`, never into a
distinct `IntPositive` type. Its resulting name projection remains a separate
approval question.

## Required tests and measurement

- One canonical `Int` identity is used by both literal endpoints; no
  polarity-suffixed integer type variant exists.
- A matching lower/upper `Int` interval solves exactly; lower-only, upper-only,
  and failed intervals remain `Unknown`.
- Lower/upper effect-side inversion is unconstructable through the endpoint
  API; component-kind mismatch is rejected before commit as local `CrossKind`
  while later independent facts continue.
- Existing fact ordering, deduplication, receipt provenance, cross-artifact
  isolation, recovery continuation, and source occurrence identity remain
  exact.
- R2 preserves the body-to-root semantic relation and root-unknown contract.
- The diagnostic fan-out key is `EndpointKey { side, family, payload }`, so
  lower/upper canonical `Int` endpoints do not coalesce. It is derived only,
  reports capacity/bytes/probes/rebuilds, and retains the current `N` maximum
  fan-out contract.
- For this bounded slice, interval summaries use inline Copy canonical type and
  effect tags plus fixed lower/upper bits per component: no primitive interning
  lookup, per-component map/set, or canonical-type-cache allocation exists.
- Existing 1,000/2,000 witnesses retain exact logical counts: direct roots have
  `2N` components, `4N` facts/provenance edges, and `8N` endpoint incidences;
  bindings have `3N`, `5N`, `5N`, and `10N`. They retain zero added semantic or
  duplicate facts, HIR/CST rescans, typed-tree copies, SCC work, and eager
  explanations. Rebaseline every endpoint-bearing occurrence/fact/key/fan-out
  slot, canonical-map probe/rebuild field, and bounds workspace capacity/bytes;
  the less-than-2.5x growth methodology carries forward. No timing experiment
  is needed unless updated counters expose a material risk.

## Stop and rollback conditions

Stop before construction if preserving canonical `Int` requires duplicating it
by polarity, if a one-sided interval projects exact `Int`, if a uniform
unvalidated endpoint type remains, if the repair creates a second semantic bound
authority, or if it needs equality, a full-store replay, a HIR/CST rescan, or a
parallel typed tree.

Do not wholesale-revert the completed integer/binding commits: their artifact
identity, store, provenance, component, and body-root infrastructure are valid
and must be retained through this focused repair.

## Approval choice

Recommended choice: approve R1 then R2 with one canonical `Int`, position-typed
endpoints, exact interval projection, and the retained one-way body-to-root
relation. Defer R3 and every name/scheme observable until the repaired base is
implemented and reviewed.

Alternative: revert all type-slice construction and defer the whole type
boundary. This discards valid infrastructure without addressing the specific
representation error locally.
