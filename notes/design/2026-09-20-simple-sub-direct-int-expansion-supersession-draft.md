# Direct `Int` and Simple-Sub expansion supersession

Status: Superseded as an implementation candidate (2026-09-20)

Superseded by:
`2026-09-20-identity-function-simple-sub-r1-supersession-draft.md`. The user's
expanded R1 completion criterion requires `my f x = x` to infer a structural
identity scheme, so this record's integer-only completion boundary is no longer
available for implementation. Its direct-`Int` decisions remain candidate
inputs explicitly retained by the successor.

Reviewed by: compiler-referee, specification, and performance M3 reviews on
2026-09-20; clean after one bounded repair/delta round.

Date: 2026-09-20

Scope: repair the completed direct-integer and binding-root type slices where
they retain a literal value variable, polarized primitive leaves, or
lower/upper exactness projection. This proposal establishes direct canonical
integer expression values and positive definition-root expansion and
simplification for the existing integer fixture. It does not add names,
schemes, annotations, operators, Core IR, runtime behavior, a definition
effect, or a general constraint-closure engine.

Upon user approval, this successor supersedes:

- `2026-09-20-canonical-int-endpoint-polarity-supersession-draft.md` as an
  implementation candidate in full;
- `2026-09-20-directed-subtyping-integer-slice-draft.md` only where it
  requires literal value components, polarized integer leaves, two literal
  value bounds, exact/`Unknown` value projection, their test/count contracts,
  and their construction claims;
- `2026-09-20-binding-body-definition-root-directed-subtype-draft.md` only
  where it requires `body.value <: definition.value`, a body value component,
  a fifth-fact/root-`Unknown` contract, their test/count contracts, and their
  construction claims;
- the unimplemented scheme/name candidate's five-fact and root-`Unknown`
  premises until a later redesign.

Completed historical construction facts remain intact until approval. HIR
artifact ownership, definition-root identity, value-only roots, occurrence
identity, canonical store admission, receipt provenance, deterministic order,
local failure isolation, one HIR traversal, physical dependency boundaries, and
the existing pure-effect model remain in force.

## Controlling decision and evidence

The user's current decision controls this scope:

```text
42 : int
int <: definition.value
definition.value -> definition.value | int -> int
```

`42` and an integer binding's `body.value` are directly canonical `int`; they
are not type variables. The root result comes from positive expansion and
simplification, not equality, a reciprocal edge, an exact lower/upper match,
or an `Unknown` fallback.

The frozen `yulang2-oracle@a58eefc31e22141574b6f20c6a5748151` uses one
`BuiltinType::Int`. Its `Pos::Con` and `Neg::Con` are positive/lower and
negative/upper grammars carrying that same constructor payload. Its concrete
lowering does allocate a transient literal variable, so that layout is evidence
of a mechanism rather than authority over this successor. The relevant
Simple-Sub chain is: propagation derives `int <: definition`; positive compact
collection forms `definition | int`; positive-only variable elimination yields
`int`. See `crates/infer/src/lowering/expr/block_local.rs:1309-1324`,
`crates/infer/src/lowering/body/methods.rs:442-450`,
`crates/infer/src/constraints/machine/propagate.rs:104-160`,
`crates/infer/src/compact/collect/mod.rs:746-917`, and
`crates/infer/src/compact/analysis/mod.rs:41-57,163-250,506-512` in the frozen
oracle.

The current solver instead creates an occurrence value component, reconstructs
`Int` only from `IntPositive`/`IntNegative` bits, ignores the
component-to-component binding fact during solve, and initializes roots as
`Unknown` (`crates/yu-solver/src/lib.rs:266-315,985-1089`). That is the owning
defect.

## Correct model

`yu-types` owns the closed primitive identity:

```text
ValueType ::= Int
```

There is no `IntPositive`, `IntNegative`, or `IntNeutral`. Polarity belongs to
the solver's open-term grammar and traversal, not primitive nominal identity.

`ConstraintBatch` records an integer occurrence's immutable known value
`Known(ValueType::Int)`. This source fact is solver-owned collection metadata:
it is neither an HIR inferred-type field nor a solver value component or
subtype fact. The frozen `SolvedModule` projects it as `Int`. The only retained
integer occurrence component is its existing effect component.

Solver endpoints are position typed. `OpenValueId` is exactly the existing
artifact-branded `DefinitionRootId`; its existing definition-value component is
only that root's batch/index storage, not a second identity. R1 allocates no
other value variable or value-variable index. R1 exposes only its bounded
planner forms; its logical union is transient and private, and no negative
value grammar or generic union/intersection constructor is admitted yet:

```text
LowerTerm ::= Value(Int) | Effect(Bottom) | EffectComponent(ComponentId)
UpperTerm ::= RootVariable(OpenValueId) | Effect(EmptyRow) | EffectComponent(ComponentId)
SubtypeFact { lower: LowerTerm, upper: UpperTerm }
```

The public planner makes side inversion unconstructable; component-kind
mismatch remains the local `CrossKind` error before admission. A future general
positive/negative term grammar requires its own approved design.

For `my x = 42`, the sole value relation is:

```text
LowerTerm::Value(Int) <: UpperTerm::RootVariable(definition.value)
```

It replaces both literal value facts and the intermediate
`body.value <: definition.value` fact. The occurrence effect remains
`Bottom <: effect <: EmptyRow`. This is a directed stored fact, not assignment
to the root, equality, or a reverse edge.

`Known(Int)` has no constraint occurrence, receipt, or value-provenance edge.
The retained effect facts keep local slots `2` and `3`; the direct
`Int <: definition.value` fact keeps slot `4`. Slots `0` and `1` are
intentionally absent after the removed literal value facts, so source-local
cause/provenance identity remains stable rather than being densely renumbered.
Constraint admission continues in HIR source order and then increasing retained
local-slot order.

## Bounded expansion and projection authority

`ConstraintStore` is the only semantic authority for the admitted
`Int <: definition.value` fact. During the existing solve admission/fact pass,
the solver derives one inline positive marker for each definition root that has
an admitted canonical `Int` lower. The marker is a solve-workspace view, not a
new semantic fact, provenance edge, cache, map/set, or retained union node.

The logical rule is:

```text
expand+(alpha) = alpha | join(lower_bounds(alpha))
```

For the only R1 admitted value lower, it produces `alpha | Int`. Normalization
uses deterministic first-source order and flatten/dedup/identity rules, then
removes an eligible positive-only root variable, producing `Int`. One accepted
root lower causes at most one expansion and one simplification. Direct literals
cause neither. A duplicate source cause records another receipt for the same
canonical fact and does not repeat derived work.

`Unknown` is only the total-output result for an absent or failed root fact; it
is never the result of a valid one-sided `Int` lower. Malformed, unsupported,
and Name binding bodies have no value fact and therefore remain `Unknown`.
R1 stops rather than guessing if a distinct lower, recursion, a bipolar
variable, a protected variable, or a transitive variable graph needs handling.
General coalescing/union-find, persistent union nodes, generic closure, a
second full-store scan, per-root set/map, caching, invalidation, and a full
legacy compact/generalization port are out of scope.

Those unsupported value shapes are structurally unconstructable through the R1
collector/planner. A defensive encounter must return the named local
`UnsupportedValueExpansion` availability error before `SolvedModule` freezes;
it must not be silently ignored, projected as `Unknown`, or passed to a later
valid root.

The total R1 outcome partition is exact: malformed/unsupported source with no
planned value fact yields its retained `Unknown`; local `CrossKind` marks only
the failed component and later facts continue; artifact, receipt, and invariant
failures return their availability error with no frozen `SolvedModule`; and an
unsupported value expansion returns `UnsupportedValueExpansion` with no frozen
`SolvedModule`. No other admitted value shape exists in R1.

## Authority and lifecycle

| Fact family | Sole authority | Lifecycle |
| --- | --- | --- |
| canonical closed value | `ValueType::Int` in `yu-types` | immutable identity |
| known integer occurrence value | `ConstraintBatch` collection metadata | exact batch; frozen only through solved occurrence projection |
| open root value | artifact-branded definition root/component | exact batch/solve workspace |
| directed subtype fact | canonical `ConstraintStore` entry | admitted semantic fact and receipt provenance |
| root positive marker | solver's one-pass derived workspace | inline, one solve; no independent fact authority |
| expanded form | logical normalization step | transient; no retained node in R1 |
| solved occurrence/root value | `SolvedModule` | immutable exact-artifact result |

No HIR/CST rescan, HIR or parallel typed-tree copy, eager explanation, or
full-store replay per root/fact is allowed.

## Construction gates

### D0 — successor authority

This record replaces the rejected Reviewed candidate before construction. Fresh
M3 review and recorded user approval are required before R1. The retained
integer/binding documents stay historical authority outside the narrow clauses
above.

### R1 — direct value and bounded expansion kernel

In one compilable gate:

- replace polarized integer leaves with `ValueType::Int`;
- record direct integer values and remove their value component and two value
  facts;
- retain the effect component and its two pure-effect facts;
- replace the fifth integer-binding fact with `Int <: definition.value`;
- replace boolean exact-bound value projection with position-typed value terms
  and the one-pass root marker/expansion/simplification above;
- migrate batch/store/solution queries, receipts/provenance, counters, and
  focused tests together.

R1 must not leave a state where literal variables are removed but roots still
use exact interval matching.

### R2 — behavioral and resource recertification

Re-certify duplicate roots, malformed/Name isolation, foreign artifact
rejection, provenance, deterministic ordering, revised N/2N counters, and the
one-pass derived-work limits. It adds neither schemes nor names.

### R3 — separately approved scheme/name redesign

Scheme/name representation, instantiation edges, scheduling, value restriction,
lookup effects, source provenance, projection, and construction require a later
design and user approval. R1/R2 decide none of them.

## Required witnesses and measurements

- `42` has `Known(Int)`, no value component/fact, and solves to `Int` with its
  existing empty effect.
- `my x = 42` has one value fact `Int <: definition.value`; the root logically
  expands to `root | Int` and normalizes to `Int` without upper `Int`.
- duplicate causes retain receipts while derived root work remains once per
  canonical root lower; malformed/Name roots remain `Unknown`.
- a local cross-kind failure cannot affect a later valid occurrence; an
  unsupported recursive/bipolar/distinct-lower shape is structurally
  unconstructable or returns `UnsupportedValueExpansion` before freezing, never
  silently as `Unknown`.
- Direct `N` integer items use `N` effect components, `2N` facts/provenance
  edges, and `4N` endpoint incidences; they have zero root expansion and
  simplification work. Integer bindings use `2N` components (effect plus root),
  `3N` facts/provenance edges, and `6N` incidences; they have exactly `N`
  expansions and `N` simplifications.
- Count the `Known(Int)` collection metadata and root-marker workspace
  allocations, capacities, and retained bytes explicitly; include both in the
  aggregate workspace/retained-byte and less-than-2.5x assertions. Rebaseline
  all existing component/root/receipt/projection/fan-out/canonical index
  capacities, bytes, probes, and rebuilds. Count term/component/endpoint clones
  and copied payload bytes, or prove the relevant payload is `Copy`/Arc-only.
  Add explicit expansion/simplification counters. The 1,000/2,000 witnesses
  must retain linear logical work and retained bytes with less than 2.5x growth.

No timing experiment is initially justified. It becomes required only if the
counters expose a second scan, non-linear probes/bytes, unexpected hot-loop
allocation/clone growth, more than one derived operation per root, or a
cache/invalidation requirement.

## Stop conditions and approval choice

Stop before or roll back R1 if direct integer typing requires a hidden literal
value variable, the positive reduction needs equality/reverse edges/union-find,
a malformed root acquires `Int`, or the bounded one-hop rule needs generic
closure, a second full-store scan, or unrelated effect changes.

Recommended approval: authorize R1 then R2 exactly as above, retain the
existing effect model, and defer R3. Retaining canonical `Int` while requiring
an exact lower/upper interval, or retaining a hidden literal value variable,
conflicts with the controlling decision and is not an option.
