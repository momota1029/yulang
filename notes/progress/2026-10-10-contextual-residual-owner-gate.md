# Contextual effect residual owner: finite-admission gate

Date: 2026-10-10
Status: unreviewed research checkpoint; no implementation authority
Scope: successor owner inventory and conditional contextual-admission witnesses
Baseline: `f75c8d2fc27c8e5f61e13632b234d56314d2a62c`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Authority: selected annotation policy in
[`annotation-effect-hygiene-integration.md`](../design/2026-10-10-annotation-effect-hygiene-integration.md)

## Result boundary

The callback target remains exactly:

```text
(int -> ['b, io] 'c) -> int -> ['b] 'c
```

The successor at this baseline still rejects explicit concrete formal effects.
It has no contextual residual owner or contextual Value/Effect task identity.
This checkpoint records why the next implementation gate needs a reviewed
residual representation and a finite-admission policy. It does not select one,
prove source reachability, or claim the target is implemented.

## Successor owner inventory

The existing candidate carries endpoint bounds and ordinary effect views:

| Owner | Existing information | Missing contextual information |
|---|---|---|
| `EffectEndpointKey` in `yu-solver/src/lib.rs` | effect rows, contributions, support/allowance views, annotation members, bottom/empty | attachment identity and exact contextual weight/residual family |
| `TypedPairKey` and canonical pair keys in `lib.rs` | kind-qualified lower/upper endpoints | contextual word or weight |
| `BoundKey` in `candidate_effect.rs` | owner, side and endpoint | contextual weight/filter |
| `candidate_extrusion.rs` replay | endpoint-only typed tasks | context-preserving replay |
| `candidate_scheme.rs` captured bounds | kind, side and mapped endpoints | attachment/context records and fresh-use renaming |
| `candidate_intrusion.rs` SCC transfer | both endpoint bound sides, origins, generation and parent replay | exact contextual bounds, residual owners and filter registrations |

The operation-local effect-view remap is keyed by original view and mapped tail.
It copies support/allowance members unchanged and expires after that operation.
It is not a residual-row cache and cannot stand in for one.

Concrete source locations at the pinned baseline:

- `lib.rs:747–775`: canonical pair keys contain endpoints only.
- `candidate_effect.rs:34`: `BoundKey` has no contextual coordinate.
- `candidate_extrusion.rs:595–631`: replay creates endpoint-only tasks; `:675–677`
  omits equal canonical effect endpoints.
- `candidate_scheme.rs:79,416–506,710–864`: captured bounds and freshening
  preserve endpoints and mapped views, with no contextual record.
- `candidate_intrusion.rs:471–480,541–592`: SCC merge transfers endpoint
  bounds/origins and replays parent lowers.

## Conditional admission discriminators

These are source-owner or algebraic witnesses under explicit premises, not
accepted source programs or successor failures.

### Parent-copy equality must retain independent bound choices

For one attachment ID, suppose a merged class has lower and upper collections
`{U, R}`, where `U` is left PUSH and `R` is right POP. Pairwise replay yields
`U/U = PUSH²`, `R/R = POP²`, and both cross pairs yield identity. Selecting one
weight and copying it across the equality loses the cross-pair identity.
Intrusion therefore has to merge both sides as collections and replay their
Cartesian product while retaining the exact weight expression and attachment
identity. This conditional transport lemma does not establish a terminating
weight closure.

### Residual-key sharing can expose different future filters

The pinned Oracle residual constructor uses a key formed from source, retained
families, and residual LEFT weight. Right debt and tail are omitted. Under the
conditional demands

```text
a <: Row({E}, t) @ right POP_i
a <: Row({E}, t) @ right POP_j       where i != j
```

both demands can share a residual `gamma` while their emitted `gamma <: t`
tasks retain distinct right contexts. A later `PUSH_j[{E}]` distinguishes them:

```text
PUSH_j ; right POP_i  => active PUSH_j plus unmatched POP_i => reject Empty
PUSH_j ; right POP_j  => identity                              => pass Empty
```

The witness uses unit counts. Its premises include admission of both demands,
retention of both replay contexts, and absence of an independent lower that
already violates the `Empty` observation. No source derivation currently proves
those premises together.

A bounded inline enumeration covered 1–2 IDs, right POP counts through 3,
PUSH counts through 2, two-family subsets, and prefixes through 3: 1,248 row
cases and 144,264 continuation/filter comparisons in one Python process. It
minimized the two-owner witness under that finite token-mass ordering. The
checker used the inspected row/mix/filter transition rules; it was not an
independent Oracle or compiler execution. No timing, RSS, Cargo, or source
execution evidence was collected.

Oracle also has a narrower same-source/tail omission guard: it checks filters
first and omits only when the right weight is empty. This is not permission for
the successor to omit every equal-endpoint contextual task. Residual rebuilding
can change an attachment's active family while retaining its ID/count; rejoining
that residual with the original family violates the inspected directed-weight
merge precondition. Whether source construction excludes that schedule remains
open.

## Implementation gate and next evidence

No current successor owner supplies a finite canonical residual template with
an exact contextual parameter. Before enabling concrete contravariant formals,
the design must specify:

1. the residual identity and exact observation key;
2. when insertion filters are consumed and registered for future lowers;
3. contextual Value and Effect task/memo identity, including wrapper
   normalization before self-edge omission;
4. all four Function-port transformations and exact replay bracketing;
5. capture, freshening, extrusion, parent-copy equality and rollback transport;
6. the concrete head/residual consumer and independent same-family contributions;
7. an exact terminating admission procedure, or a deterministic resource
   envelope that fails atomically without publishing partial inference.

Exact finite closure remains an option but is not proved. Exact propagation
within a deterministic resource envelope is another candidate under the
repository's practical-envelope policy; no dimension, threshold, rejection
diagnostic or user-visible boundary is selected here. If it changes an
Authoritative supported-input contract, it needs independent review and explicit
user approval before implementation.

Do not implement a raw contextual-entry cap as the whole admission algorithm.
The independently source-reviewed
[`recursive-push-source-invariant.md`](2026-10-10-recursive-push-source-invariant.md)
has two paired-ascription source schemas with unbounded exact PUSH contexts,
but their complete pre-generalization recursive component is one-ID and
left-only. The proposed exact recursive full-pair observer in
[`recursive-push-observer-construction.md`](2026-10-10-recursive-push-observer-construction.md)
is the recorded candidate treatment for that bounded source class; its
mathematics is not independently reviewed. Rejecting these
ordinary source schemas merely because explicit context enumeration grows
without bound would work against the user's inference priority. That observer
does not cover the separate formal-lambda callback route or its mixed
right-debt/residual consumers. A future resource envelope must preserve any
already established exact source class or present that rejection as a reviewed
user decision; no finite cap has been selected.

The next research step is a source-grounded one/two-annotation construction and
admission trace for the conditional residual witness, including the complete
Effect SCC and parent-copy schedule. Only then can the review distinguish a
false source premise from a required context-sensitive consumer. Keep the
callback target and its returned `int ->` layer as an end-to-end regression
oracle once authentic `io` and `run_io` definitions are available.

## Verification and omissions

This is an unreviewed synthesis of pinned-source reads and two independent
bounded research reports. No repository code or tests changed. It does not
close contextual admission, effect hygiene, complete Call, soundness,
principality, public inference, or F5 cutover. No Git operations were performed
by the research producers. The primary must review this note and synchronize
shared task records separately.
