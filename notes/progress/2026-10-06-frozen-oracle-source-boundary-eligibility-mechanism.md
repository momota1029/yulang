# Frozen Oracle: source-boundary eligibility is downstream of production

Date: 2026-10-06
Status: frozen research-only historical characterization; spec-audited, one minor claim repair closed
Yulang3 baseline: `1a5596ac87bd7ff0f19ee83bd9f36142dae5dc59`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Semantic and implementation authority: none

## Question and result

The open Yulang3 constructor is source-owned original-signature applicability
and contribution licensing: it must expose the complete source-selected
profile and occurrence witnesses before the pending query, with both coverage
directions on the same original row. Earlier archaeology found old source
application producers, formal/frame grouping, and projected signature
collection. This pass asks whether Frozen Oracle also had a source-boundary
ownership mechanism that could be mistaken for that missing producer.

It did: an ordinary application allocates an `ApplicationArgument`
`SourceBoundaryId` and root `OriginId`, records application/callee/argument
spans, and tags the call Function-demand constraint with that origin. A later
eligibility classifier queries the derived explanation graph, propagates
boundary ownership through replay edges, and classifies a constraint as owned
by one eligible source boundary only when its proof has a complete explanation
and a coherent ownership witness. This is a historical producer-plus-later
classifier, not the current pre-query source relation. Its classifier consumes
the very derived proof graph that current source registration must precede.

The useful mechanism is a two-stage separation:

```text
source application -> stable session boundary/origin -> generated constraint
generated proof graph -> replay-aware source-ownership classification
```

The boundary preserves an origin for later explanation. It does not itself
license every source occurrence in an inferred Function profile or enumerate
the original `beta`/`Slots(beta)` inventory.

## Historical mechanism

All locators below are relative to the pinned Oracle checkout.

1. `crates/infer/src/lowering/expr/tail.rs:630–686` allocates a source
   boundary of kind `ApplicationArgument` before creating the application.
   `make_app_with_origin` receives its root origin. The lowerer separately
   records `ApplicationProvenance` keyed by the generated `ExprId`, including
   application and callee spans. When all three spans are available, a second
   table keyed by `SourceBoundaryId` records application, callee and argument
   spans.
2. `crates/infer/src/constraints/machine/entry.rs:433–451` allocates paired
   session-local boundary and origin IDs and links the origin record to the
   boundary. It conditionally accounts for body-requirement origins; source-
   location recording is a separate operation. The ID is diagnostic/provenance
   metadata; it is not a source binder, contract slot, or type identity.
3. In `tail.rs:535–563`, the call producer submits the negative Function
   demand against the resolved callee endpoint using that source origin. The
   ordinary call and its expected interface therefore retain a source root
   before later provenance export. The producer still does not construct the
   complete current original profile or a source-indexed licensing judgment.
4. `crates/infer/src/constraints/ocast_eligibility.rs:159–300` classifies a
   producer constraint by calling
   `why_constraint_without_scheme_instantiation`. Incomplete/truncated
   explanations, unknown-internal origins, imported subtract facts, or
   missing ownership witnesses yield `Incomplete`. Otherwise it builds
   contributor and owner maps over explanation nodes. A source boundary is
   `EligibleSourceBoundary` only when it is the sole eligible source boundary
   in the explanation, owns the producer node, and `find_eligible_evidence`
   finds a root/replay ownership path. The classifier can instead report an
   internal-only replay, including disjoint lower/upper parent sources.

The key temporal fact is structural: step 4 starts from a `ConstraintRecordId`
and an explanation query over the already generated constraint graph. It
cannot be the source constructor that generated step 3, and source-boundary
allocation in step 1 only names a source site. The eligibility classifier is
also explicitly fallible/incomplete when its proof view is incomplete. This
historical failure model offers a useful caution: source provenance and
proof-derived ownership are separate facts, and neither should silently stand
in for the other.

## Correspondence and limits

| Historical structure | Useful comparison | Does not establish for Yulang3 |
|---|---|---|
| Per-application source boundary and origin | Stable source-site handle attached before solving | Complete inferred-signature source applicability, `beta`/`Slots(beta)`, or exhaustive source coverage |
| Application/callee/argument span table | Recoverable source location for diagnostics/provenance | Parse-branded source occurrence identity or typed path/owner/receiver identity |
| Constraint root origin | Trace a generated Function demand back to a source site | Q-independent admission or one original joint `(nu,K,D)` assignment |
| Replay-aware explanation ownership | Separate some source-owned constraints from internal or disjoint replay | A generating source rule; it runs after constraint production and depends on proof completeness |

This result narrows, but does not close, the historical correspondence. Frozen
Oracle had a concrete source-origin bridge and a separate derived-ownership
classifier. Neither supplies both forward and reverse licensing coverage for
all original upper occurrences on one source row. No Oracle semantic behavior,
acceptance result, or test expectation is used as authority. Current
soundness, principality, source adequacy, shadow-to-production inclusion, and
production-cutover gates remain open and unchanged.

## Scope and checks

Read-only source inspection covered the cited lowerer, source-boundary
allocator, classifier and explanation traversal, plus the current bounded
source-licensing archaeology and governing source-construction clauses. A
spec auditor found one minor source-location accounting overstatement; the
note now distinguishes origin accounting from the separate location-recording
operation. No Oracle build or execution, tests, mutation, benchmark, compiler
edit, or Git operation was performed. This is not a repository-wide absence
claim; only the cited producer/classifier chain was inspected.
