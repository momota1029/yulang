# Current task: F5 general Function scheme foundation

Updated: 2026-09-24. Branch: `yulang3`; do not modify frozen `main`.

Resume handoff: [`2026-09-22 F5c scheme-closure handoff`](../notes/handoffs/2026-09-22-f5c-scheme-closure-handoff.md).

Latest status (2026-09-24): producer analysis, candidate replay, and the
generalization Q/R rewrite use iterative task/value worklists with dedicated
lanes in the existing physical walker ledger. Raw recursive bounds now move
through iterative materialization instead of being deeply cloned first. Deep
positive/negative boxed trees and Term chains pass on 64 KiB stacks, with DFS,
first-occurrence, polarity elimination, and product order preserved. The
focused `f5c_` filter passes 161 tests; full F5c/F5e
closure and the broader resource/public-observation gates remain open. The
latest slice is recorded at the end of the F5c handoff and this file. The
candidate-replay and iterative Q/R rewrite slices are pushed as `da9097db` and
`a41b9875`. The ownership-only materialization change is verified and being
checkpointed; keep the §24 finalizer callback/API unchanged.

## Active F5 gate

Latest continuation note (2026-09-24): the user selected option B for the
counter conflict: preserve §36 all-counter invariance with canonical
preordering while retaining the prescribed stable-mergesort comparison count.
That subgate is pushed in `fc34f127` and `e81b9e84`. Iterative boxed-tree
materialization is pushed in `68952716`; producer analysis is pushed in
`2366de39`; iterative candidate replay is pushed in `da9097db`. The Q/R
substitution rewrite is isolated in `f5c_binder_substitution.rs`, pushed in
`a41b9875`, with two accounted lanes and 4,096-deep small-stack tests. Raw
recursive-bound materialization now moves values through the iterative walker
instead of deep cloning; `lib.rs` is 27,416 lines.
The focused `f5c_` suite passes 161 tests in default and no-default-feature
configurations. Full F5c/F5e closure is not claimed: tree clone/drop, closed
finalization inside the §24 callback, and co-resident draft/output-tree
accounting remain open. Preserve §24/F5b; do not implement the unapproved
indexed `yu-types` API.
The design decision is recorded in
[`2026-09-24 F5c normalization counter invariance`](../design/2026-09-24-f5c-normalization-counter-invariance-addendum.md);
implementation details and residual gates are at the end of the
[handoff](../notes/handoffs/2026-09-22-f5c-scheme-closure-handoff.md).

### Live F5c resume status (2026-09-24)

F5a and F5b are complete; F5c and F5e are not. The base approved F5c working
set is preserved in checkpoint commit `bb1ec56c` on `yulang3`; this does not
close the active gates. Later coherent gate slices are checkpointed separately.
The base commit contains changes to `crates/yu-solver/src/lib.rs`,
`crates/yu-solver/src/term.rs`, `crates/yu-solver/src/incoming_sample_trace.rs`,
`crates/yu-solver/src/tests/f5c_scratch_reserve.rs`,
`crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs`, this task file,
the F5c handoff, `notes/design/INDEX.md`, the indexed-finalizer Draft, the
producer-order/failed-route-sampling addendum, and the 2026-09-23 and
2026-09-24 daily progress records.

The closed-DAG incoming traversal/scratch gate is closed. The last full
`f5c_`-filtered suite passed 93 tests before the Term-owner additions; the last
full `f5c_incoming_` subset passed 31 before those additions. The current
focused Term subset passes five tests. End-to-end per-use failure-injection
coverage includes `ExtrusionStack`, Bottom `RoutedUses` and
`RoutedUsePositions`, fresh-row `ValueBounds`, `ValueExactUpper`,
`ValueExactLower`, direct lower/upper value rows, `ValueLevels`,
`ValueMetadata`, and `ExtrusionValueMarks`. The incoming value-row witnesses
use changed post-reserve failures during `route_incoming`, match the event-time
lane sample before propagation, check RouteCheckpoint/public-route
restoration, verify the one conditional post-rollback sample and retained-ledger
reconciliation, then retry successfully. The `ValueLevels`, `ValueMetadata`,
and `ExtrusionValueMarks` witnesses prove exact aggregate growth and event-peak
preservation. The metadata and marks tests independently recompute
post-rollback totals from live capacities through a fresh independent ledger.
Focused M1 specification delta reviews are clean for these lanes.
This closes only the named lanes; the remaining owner-to-route witness matrix
still needs reconciliation. Pure Function effects remain limited to closed
`EmptyEffect`/`EffectBottom`, so live effect-row mutation lanes remain outside
the current per-use matrix. The earlier
direct-owner `ValueBounds` injection-site finding was closed after moving
injection inside its transaction. The incoming `FreshValueBounds` witness is
now `f5c_incoming_fresh_value_bounds_growth_samples_before_rollback_and_retries`
in the route sidecar; it checks exact event/sample deltas, rollback, an
independent retained ledger, and successful retry.
The `ExtrusionStack` witness is now also in that sidecar, with exact slot-byte
and event-peak evidence, transient-to-retained reconciliation, RouteCheckpoint
restoration, and retry publication.
The `ValueExactUpper` witness now distinguishes its temporary fresh-row upper
payload from the retained preexisting lower-row growth and reconciles both at
the post-rollback boundary. The `ValueExactLower` witness now ties its exact
event delta and peaks to the preexisting use row and independently reconciles
the retained allocation after rollback. The direct-row witness now gives both
`ValueDirectLower` and fresh-row `ValueDirectUpper` exact event/sample and
transient-versus-retained rollback evidence.

Per-use rollback remains open on full physical resource accounting. The nested
value/effect-bound capacity subgate is now independently reviewed and closed:
incoming capacity events are journaled before checked preflight; rollback
preserves event/rebuild counts, including repeated growth and failed preflight,
while retained bytes are reconciled only from surviving rows. Coverage includes
two successful growths on one existing lane, a mixed successful/failed
preflight event sequence across two existing rows, and repeated growth on a
fresh row that rollback drops. A real Function/recursive-bound route reaches
the checked preflight failure and proves one outer post-rollback sample plus
full RouteCheckpoint restoration. A consuming run witness reaches that same
preflight branch, attempts one outer sample, returns `IdentityExhausted`, and
publishes no `SolvedModule`.

An M3 compiler review questioned the missing event peak when checked preflight
totals are unrepresentable. Architect adjudication rejected that as a blocker:
the checked preflight is the failed event-accounting attempt, and publishing a
stale or partial peak would violate §3's atomic-overflow clause. The route marks
the failure, rolls back, takes the one conditional post-rollback sample, then
terminates with no result. Representable nested growth still has event-time
peak coverage. This adjudication does not close other resource lanes.

The typed-pair/diagnostic owner group now has event-time capacity hooks for the
typed-pair map and payload, worklist, diagnostic delta/index and completion
scratch, bucket candidates, errors/reported-errors, and the two corresponding
journal undo buffers. Checked diagnostic-edge accounting publishes atomically.
The incoming-Union witnesses prove a normalized, distinct Int/Function pair,
completion of all private members before representative-provenance failure,
failure in the later private member, complete RouteCheckpoint restoration,
event-time transient payload evidence, retained-ledger reconciliation, and one
conditional post-rollback sample. The primary accepted two major test-evidence
gaps from the first review; both were repaired, and the fresh post-repair M2
specification delta review found no remaining issue in this owner group.

The incoming route-sampling sidecar now also isolates changed-capacity failures
for `DiagnosticReverseEdges`, `DiagnosticBucketHeads`, `DiagnosticBucketTails`,
and `DiagnosticBucketCandidates` using an edge- and seed-producing normalized
Union fixture. Its independent post-rollback ledger recomputes retained typed-
pair child-edge payloads from the live memo entries. The first M1 review found
that retry linkage did not prove §44's representative projection; the witness
now checks the finalized Union's first member and the retried sole fact's
`Leaf::IntPositive` lower endpoint. A fresh M1 delta review is clean. This
closes only those four diagnostic scratch lanes, not the whole typed-pair /
diagnostic owner-to-route matrix.

The same shared witness now isolates `TypedWorklist` at zero capacity and
checks its exact `TypedWorkItem` slot-byte event delta, event peaks, rollback,
single post-rollback sample, independent retained ledger, and retry linkage.
The fresh M1 specification delta review is clean. The route sidecar now passes
14 tests; this closes only the named worklist lane.

The same witness now also isolates `TypedPairs` from a zero-capacity map and
checks `DiagnosticEdges` through an edge-producing normalized-Union fixture.
Both verify event-to-sample linkage, exact slot-byte delta and peaks, complete
checkpoint restoration, independent retained-ledger reconstruction, and retry;
the edge case preserves the first normalized member as the sole public
representative. A fresh M1 specification delta review is clean, and the route
sidecar passes 16 tests. These close only the named lanes; the rest of the
owner-to-route matrix and §3 accounting/measurement gate remain open.

End-to-end changed-reserve witnesses now also cover both journal undo-key
owners: `typed_pair_keys` and `reported_error_keys`. A cfg(test)-only skip
counter targets the journal Vec reserve after its matching data-owner reserve;
the witnesses verify event-time slot deltas/peaks, retained spare capacity,
rollback, independent ledger, one post-rollback sample, and retry linkage. A
fresh M1 spec review found only a missing canonical-index assertion; that
assertion is now present and the focused journal tests pass. The test seam adds
17 lines to `lib.rs`; the witness body stays in the existing sidecar.

The journal partial-setup witness now traces both `value_row_seen` and
`effect_row_seen` growth events. It checks per-event `u32` byte deltas and
peaks, failed-begin rollback, retained spare capacities, empty seen-vector
contents, one post-rollback sample, and an independently rebuilt retained
ledger. Its M1 specification review is clean. The three existing journal-seen
tests now live in the sidecar, keeping their bodies and expectations unchanged
while removing 91 test lines from `lib.rs`.

The `RouteMutationJournal.value_rows` undo owner now has a focused failed-route
witness in the sidecar: one traced capacity event is tied to its exact retained
and peak sample, the active journal's capacity survives in the spare owner after
rollback, and an independent post-rollback ledger matches retained session and
nested totals. The old witness was relocated from `lib.rs`, shrinking that file
by 67 lines. A fresh M1 specification delta review found no blocking or major
finding. The independent post-rollback ledger carries forward the already-
asserted event peak; it does not independently reconstruct the whole peak
history.

The four ConstraintStore changed-failed-reserve cases now trace every ordered
store-owner event through its exact sample. Their byte delta changes only the
session aggregate; semantic bytes remain unchanged. Rollback retains physical
capacity while restoring logical state, with monotone growth/rebuild counters
checked separately. The post-rollback ledger independently rebuilds retained
and nested totals, and each lane retries through canonical fact, consumed
receipt, provenance, and routed-use publication. The old test moved from
`lib.rs` into the sidecar, removing 46 lines. An M1 specification review's
minor §44 retry-link omission was closed by adding those assertions; no
production code changed.

Both routed-use owners now have exact changed-reserve witnesses. `RoutedUses`
is checked against its observed slot delta in both semantic and session totals;
`RoutedUsePositions` changes only session totals. Each event peak is derived
from the immediately preceding completed sample and observed lane delta, then
carried into the independent post-rollback retained-ledger check. The witness
asserts one conditional post-rollback sample, RouteCheckpoint restoration, and
successful fact/canonical/receipt/provenance/routed-use retry linkage. The old
test moved from `lib.rs`, removing 54 lines. The initial M1 review's two major
assertion gaps were closed; a fresh specification delta review found no
remaining issue. No production code changed.

The existing `ValueLevels` changed-reserve witness now captures the completed
post-rollback sample and reconciles semantic/session retained bytes, nested
bound bytes, and peaks against an independent ledger rebuilt from surviving
owners. Event peaks use the saved pre-attempt peaks, exact observed capacity
delta, and finish-output bytes. The witness keeps its one-event/one-final
sample distinction, RouteCheckpoint restoration, and successful retry. A
single specification review closed its initial missing-local compile blocker;
focused verification now passes. No production code changed.

Fresh value/effect outer-row reserves and extrusion-stack pushes now use the
same event-time capacity observer. End-to-end incoming failure witnesses prove
a post-reserve value-row growth sample, a later private-member failure with
retained row capacity, and zero-capacity extrusion-stack growth followed by
post-reserve failure. The tests assert the exact changed lane was sampled
before the reserve error propagated, full logical RouteCheckpoint restoration,
one successful post-rollback sample, no public route, and retained-byte ledger
reconciliation. The first M2 spec review found the event-time witness did not
distinguish the final sample; a test-only lane observer and reserve-failure
witness closed that finding, and fresh spec delta review found no remaining
issue. Closed-pure Function effects still exclude live effect-row creation from
the per-use route witness matrix; those lane hooks are not end-to-end certified.

The inference Term arena owner group is now implemented and independently
reviewed. It records event snapshots for all six counted owners; the test ledger
independently enumerates physical owner state, lengths, requests, capacities,
growths, bytes/peaks, and active/spare journal transfer. Dedicated post-growth
failure witnesses cover the interned and claimed-page journal lanes, proving
the event sample precedes rollback and retained spare capacity reconciles after
the single post-rollback sample. Checked-overflow coverage reaches both the
private route and consuming `run()` path. The initial M2 review found missing
journal-lane witnesses and non-independent aggregate-only Term ledger evidence;
both were repaired, and the fresh delta review found no remaining issue.
Successful-path event-sample cost remains part of the one bounded measurement
after the remaining owner hooks cohere.

The full §3 sampling gate remains open. The ConstraintStore and routed-use
owner group is now implemented and independently reviewed: facts, canonical
keys, consumed receipts, provenance, routed-use records, and routed-use
positions preserve event-time capacity evidence and post-rollback retained
state. Store lanes use checked growth/event counters and fallible reserves;
changed failed reserves are sampled before their errors propagate. The
independent ledger receives each fixed-size store snapshot. Focused witnesses
cover all four store lanes, changed failed reserves, local admission rollback,
retained capacities, retry, and counter overflow. Fresh M2 specification and
performance delta reviews found no blocking issue.

The changed-failed-reserve gap in all seven incoming-instantiation scratch
lanes is now closed. A reserve that changes physical capacity before returning
an error records checked growth evidence and marks the pending event; the
event-time aggregate sample runs while scratch is attached, followed by the
existing §26 scratch-exit sample and exactly one conditional post-rollback
sample. A trace test covers all seven lanes and distinguishes those three
sample roles; pre-reserve/no-growth failures do not take a post-rollback
sample. The trace now pairs batched Term owner events with their ordered
per-event snapshots. Fresh M2 specification review found no blocking issue.

Verification at this checkpoint: `cargo test -p yu-solver --lib -- --test-threads=1`
— 202 passed in 675.10s; the focused scratch-reserve tests,
pre-reserve failure test, and no-growth/no-outer-sample test pass. Format,
package test check, and whitespace checks pass. The aggregate sampler is
fixed-size/O(1), while successful event-time invocation count is O(G) for G
capacity-growth events. The required bounded successful-path measurement was
attempted but produced no valid result. The temporary no-sample control
bypassed 26 IncomingRoute aggregates while the measured sample counter still
advanced by 26, so the comparison did not isolate the target cost. The
conservative eight-process experiment budget is exhausted; no timing sample is
accepted. Do not call the full §3 accounting/measurement gate, F5c, or F5e
complete.

The two delegated design choices are now adjudicated in
[`F5c producer ordering and failed-route sampling`](../notes/design/2026-09-23-f5c-producer-order-and-failed-route-sampling-addendum.md):
Q/R assignment follows first surviving producer encounter, so cross-order
alpha/output equality is not required when that order changes; the full Union
relation and §44 first-normalized-member atomic projection remain. A failed
incoming route takes exactly one fixed-size O(1) post-rollback sample iff a
physical capacity or counted-owner/retention transition occurred. Architect
preflight and final M3 specification/compiler/performance delta reviews are
clean.

These choices authorize implementation, not completion. The typed-pair/
diagnostic, outer-row/extrusion, inference-Term, ConstraintStore/routed-use,
incoming-instantiation-scratch owner groups are implemented and independently
reviewed. The primary's 2026-09-24 owner-to-route crosswalk now closes the
per-use changed-capacity witness matrix for the approved closed-pure Function
routes. It matched each in-scope owner family to event-time samples, rollback
state, no-change/setup-failure behavior, and the independent ledger evidence
required by §3. The missing final-boundary overflow witness is now covered by
direct `route_incoming` and consuming `run()` tests in
`src/tests/f5c_value_exact_upper_route.rs`; live effect-row mutation remains
out of scope. This does not close the full §3 accounting/measurement gate.
The successful-path measurement also remains open: the eight-process attempt
above was invalid, and a new experiment must first isolate every IncomingRoute
sampling entrypoint. Test bodies stay in the sidecar; `lib.rs` receives only a
test-only probe variant and condition for this final-boundary failure case.
An independent mapping found a separate mechanical 63-line
`ResourceSampleChecked` extraction candidate, but it is deferred until the
accounting/measurement checkpoint closes to keep this diff focused.
Producer-ordered Q/R assignment and post-Q/R normalization are active again.
The mixed-height authority choice is resolved: §36 height-major order
supersedes §25 structural-first order only when child heights differ. The
latest code slice removes factorial alpha-label search from Q/R selection and
uses first-surviving trace order for R, then predicate-first and lower-before-
upper traversal for Q. Producer-order tests cover reversed encounters, shared
Q identity across predicate and multiple R bounds, and exact stored trace
order, plus explicit rejection of leftover live `Variable`/`Shared` nodes before
normalization. The `f5c_` library filter passes 136 tests; `cargo check -p yu-solver --tests`,
`cargo fmt --check`, and `git diff --check` pass. This is a partial
implementation checkpoint, not closure of the producer-order or normalization
gates. F5c stack-safe normalization, component sharing, finalizer traversal,
and F5e certification remain open. Candidate B's proposed §24 API is not
approved.

The selected normalization algorithm is still unimplemented: the current
post-Q/R pass compares recursive structural trees, does not rank mixed heights
by §36 descriptors, and remains stack-bound. The next slice must replace it
with bounded, stack-safe height-major ranking while retaining exact duplicate
elimination and the §44 first-member projection. The existing higher-ranked
finalizer callback and F5b accounting boundary must remain unchanged unless a
separate API/accounting decision is reviewed and approved. The per-use
owner-to-route audit is closed for the approved closed-pure Function scope;
full §3 sampling/accounting certification still lacks a valid successful-path
measurement.

Architect review resolved the accounting phase boundary for the separate
stack-safety slice: §§14/26/34 authorize private production accounting for
F5c generalizer/walker scratch now, with independent per-lane test-ledger
reconciliation and accurate existing aggregate retained/peak totals. Keep
root-local scratch distinct from `component_expansion_memo`; do not add the
public `generalization_scratch_*` family accessors or claim its F5e exposure
certified. The conditional failed-route sample is separately authorized under
the producer-order addendum §3 and is implemented; the per-use owner-to-route
matrix has since been reconciled for the current closed-pure route set. No
implementation change came from the first two bounded writer attempts. A later stack-safety
slice in `lib.rs` added an iterative row/Term walker, summary construction and
materialization, structural comparison, and eleven private scratch lanes.
Focused tests now include a 1,024-row ordinary-draft chain, a 2,048-level
walker-only alternating Function chain, same-memo failure/retry, and lane/peak
reconciliation. The focused F5c suite passes 75 tests; package check, format,
and whitespace checks pass. Independent specification review is clean for
that slice. Performance review keeps the overall stack-safety gate open:
recursive draft/replay/normalization/finalization and owned-tree operations
remain, and Union/Intersection part buffers are undercounted after ownership
transfers. Repeated structural dedup also needs a bounded indexed strategy.

Other open F5c work is iterative indexed draft processing through guarded
owner checks, replay, incidence/reference collection, normalization/key
construction, and finalization, plus transfer-aware scratch accounting and
fixed-point replay/rescan reduction. Keep the approved first-member normalized
Union representative. Do not claim F5c completion or F5e resource/scale
certification.

The 2026-09-23 indexed-draft scope check found no safe production seam for an
arena-only substrate pass: `walk` and summary registration currently emit
boxed `F5cPositive`/`F5cNegative`, which `build_inner` immediately consumes.
Reconstructing boxed trees at that seam would preserve the stack risk; a
shallow-only adapter could reject currently accepted deep inputs. The next
stack-safety implementation must keep IDs across summary registration and the
draft consumers, rather than stopping at a standalone arena. A subsequent
GPT-6 Sol architect review found that a useful production slice must carry IDs
through `walk`, summary registration, `build_inner`, and finalization. The
implementer made no edits because the complete vertical path also needs exact
root-scratch/closed-finalizer peak accounting. The narrower iterative-finalizer
attempt exposed an authority boundary: F5b §9 requires returning to design for
a cross-crate accounting callback; §6 also forbids solver-owned lane mutation
inside the callback. A `doc(hidden)` hook still changes §24's exact API. The
solver-owned callback-slot alternative is now rejected because invariant
transaction-lifetime handles cannot safely be stored in solver-owned slots.
No code or tests changed in these implementation attempts.

Fresh M2 specification and performance reviews of the indexed-finalizer draft
found Candidate B not ready for user approval. The spec review found no
producer-side pruning/compaction proof for a reachable, orphan-free graph and
an ambiguous error boundary. The performance review found the solver's current
pre-finalization baseline omits the simultaneously live indexed arrays and
member drafts, and the new scratch/growth ledger is incomplete. Both found
count inconsistencies; performance also required separating the indexed
linear-work target from F5 §34's closed-normalization `O(N + Σ k log₂(k+1))`
cost. A read-only architect adjudication confirmed that the current producer
still emits boxed trees and normalizes predicate and R bounds separately; no
end-to-end ID-preserving producer is established. A follow-up confirmed that
F5 §26 authorizes the all-drafts-coexist O(1) sample; the current call path
does not take it, and its exact per-lane ledger remains incomplete. Candidate B
remains a Draft and is not an implementation or user-approval gate.

The active stack-safety work is a bounded architecture repair of the
ID-preserving producer and complete capacity ledger. F5 §26 already authorizes
the all-drafts-coexist baseline sample; this design work does not authorize a
new §24 public API. Candidate B still needs a clean M2 review and explicit user
approval before implementation. If exact accounting requires a boundary
beyond §26's named sample and growth events, return with that precise authority
question. Do not use callback-side solver result slots or treat `doc(hidden)`
as private. Exact-alpha and failed-route sampling choices remain pending.

The accounting-boundary Draft now specifies an O(1) event-time ticket ledger,
the six physical-owner groups, the semantic/session class rationale, and the
authorized §26 all-drafts-coexist sample. A fresh independent M2 specification
and performance delta review found no remaining preapproval blocker within
that accounting-design slice. This closes only the design contract: exact
constructor/growth/error/unwind event proof, lane enumeration, and
`yu-types` same-time checkpoint proof remain implementation evidence.

The indexed producer is still not ready for approval. Architect review found
the current exact alpha key search evaluates `k!` label permutations for `k`
distinct non-owner variables; a path-expanded traversal of an O(d)-node shared
Function DAG can likewise visit `2^d` occurrence paths. These are concrete
counterexamples to the current method/bound, not proof that every exact bounded
algorithm is impossible. The user decision remains: preserve unrestricted
exact alpha with a revised worst-case contract; preserve the bound by
restricting/proving the production forest; or weaken alpha/order independence.
The separate failed-route accounting choice also remains open: approve a
narrow conditional post-rollback O(1) sample, keep the sample whitelist and
journal/reconcile every physical change, or defer that resource gate. Do not
implement Candidate B or change either contract by assumption. Resolve these
choices, then complete producer parity and a clean full-candidate M2 review
before presenting the new §24 API for explicit approval.

Verification on this candidate: `cargo test -p yu-solver --lib f5c_ --
--test-threads=1` — 75 passed; `cargo check -p yu-solver --tests`,
`cargo fmt -p yu-solver`, `cargo fmt --check`, and `git diff --check` passed.
No full solver suite, workspace check, benchmark, or F5e 1k/2k/4k matrix was
run in this continuation. The independent post-repair performance review
found the remaining stack/resource risks listed above; no benchmark was run.

The longer text below retains earlier F5 and syntax history; this live block
controls the current F5 navigation.

The reviewed proposal is
[`2026-09-21-f5-general-function-scheme-foundation-draft.md`](../notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md).
It carries the production source witness `my f x = x` through shared Pattern ML
application, one-parameter Lambda HIR, live polarized Function constraints,
SCC generalization, disjoint Q/R closure, and fresh incoming instantiation.

M3 architect, semantic, specification, and performance review is clean. The
user approved the atomic gate on 2026-09-21, with rollback to the design if
implementation contradicts it. The user also approved delimiter-scoped
non-binding Pattern evidence: `cast((f x)): A` is the production shared-grammar
witness, while direct Cast depth retains `PATTERN_STOP_ITEM` ownership. Immediate
next action: F5a is complete. Its focused syntax suite passed 1380 tests with
one ignored; `yu-hir` passed 46 unit/integration tests and five compile-fail
doctests; the focused `yu-solver` F5c suite passed 58 tests; workspace check, formatting, and diff
checks passed. Compiler-referee, specification, and regression review are
clean. F5b architecture inspection found two blocking API-lifecycle decisions
before its implementation may start:

1. `yu-types` must keep raw closed-arena mutation private, but downstream
   `yu-solver` must construct F4 Bottom/Int schemes and later F5c schemes after
   public `ClosedValueScheme::new` is removed. Select an inter-crate sealed
   high-level finalization gateway or change the ownership boundary; Rust has no
   friend-crate visibility.
2. The current standalone public `ConstraintStore::new(Arc<HirModule>)` admits
   Terms from an independently owned `ConstraintBatch`. The approved TermArena
   lifecycle instead moves that exact arena into the store during `solve`.
   Select removal/privatization, a batch-bound constructor, or an explicit
   transfer/share capability.

The user selected sealed finalization and a batch-bound store on 2026-09-22,
then approved logical Term-lineage clone ownership and fixed 256-slot Term
pages. The now-Authoritative amendment at
`notes/design/2026-09-22-f5b-closed-finalization-term-owner-draft.md` specifies
sparse branch storage, reusable closed-finalization staging, and deterministic
failure injection after clean M3 review. The independently authorized F5b
lifecycle substage is complete: `yu-types` owns the sealed generative
finalizer, transactional exact-capacity accounting, and fallible terminal
finish; `yu-solver` maps only the existing aggregate counters and publishes no
partial result on finalization failure. Collected `Term`s are now opaque,
batch/store-owned lineage handles; clone branches use disjoint sparse fixed
pages and standalone HIR-only store construction is removed. Immediate next
action: F5b is complete. `InferenceSession` now owns the checked dense live
value/effect rows, levels, origin/non-generic metadata, typed synchronous
frontier, one typed pair memo, delta-local canonical diagnostic completion,
and fallible workspace growth. `ConstraintBatch` retains immutable recipes
only, while final projections derive from live rows. The M3 semantic,
specification, and performance delta reviews are clean; retained F4 facts,
ordering, no-mutation, counter, and production-frontier contracts remain
covered. Next action: continue the already-approved F5c general-scheme closure
(polarity census, eligibility, Q/R closure, transactional component
publication, and fresh incoming instantiation). The F5c blocker around closed
`Top`/`Bottom` children is resolved by the user's choice on 2026-09-22:
introduce private closed-extreme Term nodes and extend the exact §32 TermView
surface as needed, preserving zero fresh Q/R allocation for structural
extremes. F5a continues to emit no source Function facts until F5d. F5e's
detailed public resource families and 1k/2k/4k certification remain deferred.

The current F5c implementation slice now has private closed-extreme Terms,
whole exact-bound Union/Intersection drafts, guarded self/opposite-polarity R
coverage, transactional all-member draft visibility, fresh R lower/upper
restoration, structured incoming routing with one public source route for a
normalized union whose public fact uses the canonical first-member
representative, and focused closure/round-trip tests. The user approved this
representative-fact policy on 2026-09-22. The first rollback repair now admits
all private union members before public publication and restores the bounded
private live algebra, diagnostic state, counters, public store, provenance,
route markers, and reusable term/session journals on later failure. Its
focused semantic, specification, and performance delta reviews are closed;
the generation-exhaustion witness also proves the preflight failure path is
atomic. Nested Union/Intersection products now expand through closed Function
children. Per-use rollback now covers internal, Bottom, Int, structured, and
normalized-Union routes under one transaction, including warm-spare begin
failures and validation-before-transaction precedence; its semantic and
performance delta closure reviews are clean. Component-scoped expansion
sharing and F5e certification remain open. F5 explicitly excludes effects beyond its closed
pure Function subset; non-pure Function effect endpoints are rejected and a
focused rollback witness covers them. The ineligible-variable rejection gate
is covered at FetchValue boundary zero in both polarities; the final
Q/R/eligibility rejection helper is exercised with isolated non-generic
targets in both polarities, with the closure interaction recorded in the
focused test.
The component memo now uses reverse parent/incidence/root-edge indexes,
generation-marked active-conflict propagation, admission without per-root
shared-DAG traversal, and five named resource lanes. A focused real expansion
asserts the active-ancestor exclusion under `cfg(test)`; the expensive
assertion is opt-in so scale tests do not acquire a test-only repeated walk.
Its focused witnesses cover active-transition
rollback, more-than-64 row collisions, cold/warm structure, guarded cycles, and
checked lane overflow.
The R-classification gate records owner-relative guarded traces,
keeps equal-key recursive owners, uses one shared predicate/R variable-label
namespace, collects Q occurrences from retained R bounds, checks missing rows,
and computes incidence after eligibility from the expanded draft. Its focused
F5c suite passes 58 tests, including a complete mutual trace, draft-bound
witness, mixed exact/direct row expansion, and dense/malformed finalizer
ordinal witnesses. Follow-up repairs index reentries by owner, use a new-only
reachability frontier, apply side-aware trace survival, restrict grouped keys
to final replayed/normalized candidates, cache survivor traces, and replay
each owner bound at most once per fixed-point iteration. Independent M3
semantic review found no new issue in the latest delta; the duplicate
trace-replay performance finding is closed. The R gate is not closed: the
exhaustive alpha-permutation key search remains incompatible with the §25/§34
bounded normalized index contract. Fixed-point replay/rescans, root-wide
closure reconstruction, component sharing, and recursive expansion depth
remain open performance/architecture work. A future computation-valued fetch
also needs its body-boundary level carried into eligibility and Q/R
classification.

The latest component resource repair and admission optimization raise the
focused F5c suite to 58 tests and close the old all-root invalidation, 64-bit collision, same-key rollback,
failed-memo recording, non-transactional-ledger, aggregate-peak, and later
sequential-reserve evidence hazards. Independent M3 resource/spec review is
clean. Admission no longer revisits the shared DAG per cached root, and a
focused active-ancestor witness covers the cacheability invariant. The
component gate remains open because row/Term expansion, summary conversion,
normalization, and owned-tree operations can still recurse with input depth.

The exact-alpha requirement over unrestricted commutative shared-variable
forests is equivalent to a graph-canonicalization problem, while the active
design requires O(N+S)-style normalization. This contract gap needs a user
decision before the key implementation can be replaced: retain exact alpha
ordering with a revised complexity contract, restrict/prove the production
forest class for the bounded contract, or weaken alpha/order independence.
The component memo now avoids per-root shared-DAG admission traversal, but
generalizer expansion/materialization still needs stack-safe indexed worklists.
The ineligible-variable rejection gate is closed. Effects beyond F5's approved
closed-pure subset remain outside scope; invalid effect endpoints are
rejected. Closed-DAG incoming instantiation and exact scratch accounting are
now closed after focused 63-test verification and independent specification
and performance delta reviews. Coverage includes per-use polarity memos,
shared-child single visits, disjoint fresh rows, Q/R restoration order, all
seven scratch reserve failures and retry, retained physical accounting across
later route failure, finish-time release, and canonical §44 representative
argument correspondence.

### Latest incoming route sampling evidence (2026-09-24)

The changed-failure incoming-route witnesses now cover `ValueLevels`,
`ValueMetadata`, `ExtrusionValueMarks`, `DiagnosticDelta`, and `Errors` in addition to
the previously closed exact/direct value-row lanes. The `ValueLevels` fixture isolates one capacity event, checks exact
event-time and post-rollback retained-byte deltas, proves the event peak rises
above baseline and survives rollback, then retries. The `ValueMetadata`
fixture pre-reserves earlier dense rows, isolates one metadata growth event,
and checks exact event-time totals/peaks plus the successful post-rollback
snapshot against a fresh `IndependentResourceLedger` enumeration of current
capacities and independently enumerated surviving nested bounds. Both restore
the logical/public route checkpoint and verify exactly one conditional
post-rollback sample. A third isolated fresh-row fixture now proves the
fourth-reserve `ExtrusionValueMarks` growth event with the same event-time,
independent post-rollback ledger, checkpoint, exactly-one-sample, and retry
assertions.

Fresh M1 specification delta reviews closed both lane witnesses. The
`ValueMetadata` review required two evidence repairs: first to isolate the
aggregate delta and preserve event-time peaks, then to recompute the
post-rollback snapshot from live capacities rather than relying only on a
baseline-plus-delta assertion. Named successful sample snapshots are now
captured by the cfg(test)-only `incoming_sample_trace` sidecar; production
sampling behavior is unchanged. The `DiagnosticDelta` witness records ordered
completed capacity events, requires an earlier `FreshValueBounds` growth event,
and derives the target lane's exact aggregate/peak changes from the immediately
preceding completed snapshot. It also checks the post-rollback ledger, route
checkpoint, one conditional final sample, and retry. Test bodies and the
independent post-state enumeration remain outside `lib.rs`. The `Errors` lane
witness injects after the error Vec grows during the second private Union member,
checks the exact event delta against its preceding event sample, complete
rollback and independent retained-ledger reconstruction, then confirms retry
publishes exactly the canonical Int representative while the Function member
remains private. Its fresh M1 review closed after adding that representative
assertion. The `ReportedErrors` witness separately pre-reserves `Errors` and
its journal key lane, injects after the reported-error set grows, and checks
the exact event delta/peaks, retained HashSet capacity, independent
post-rollback ledger, full route checkpoint restoration, and retry with the
same canonical representative. Fresh M1 specification reviews are clean for
both witnesses. The new `DiagnosticDeltaIndices` witness keeps the typed-pair
map, delta Vec, and journal key lane pre-reserved, then isolates index-map
growth from zero capacity. It checks the map-slot byte delta against the
previous completed event, event peaks, independent post-rollback accounting,
and retry linkage among the fact, provenance, consumed receipt, and routed-use
record. Its M1 review found a minor retry-identity gap, closed by those linkage
assertions. `lib.rs` is currently 28,456 lines and was not modified in these
lane slices. A `DiagnosticReverseOffsets` witness now isolates its zero-capacity
`Vec<usize>` after pre-reserving the earlier typed-pair/delta lanes and proves
the exact slot delta, event peak, rollback, independent retained-ledger
reconciliation, and retry identity. Its M1 review first raised a peak-ledger
concern, then withdrew it after confirming that the test derives event peaks
from the immediately preceding sample plus the observed capacity delta. The
common route/trace/rollback/retry assertions for `DiagnosticDelta`,
`DiagnosticDeltaIndices`, and `DiagnosticReverseOffsets` are now consolidated in
one private sidecar helper, while each lane's capacity setup and element-size
formula remain explicit. This removes 325 net lines from the three witnesses;
the M1 review found no weakened assertion. `DiagnosticReverseCursors` now uses
the same helper and isolates its vector while pre-reserving two reverse-offset
slots for the fixture's one pair plus terminal offset. A minor M1 review gap
about that exact predecessor capacity is closed by asserting capacity >= 2.
The tests remain outside `lib.rs`.
The same helper now covers eight more one-pair diagnostic scratch reserves:
DFS stack, finish order, SCC indices/nodes/offsets/pending-children/worklist,
and node witnesses. The M1 specification delta review found no issue. The
former simple-fixture gap for `DiagnosticReverseEdges` and the bucket lanes
is closed by the edge/seed-producing Union cases above. `TypedWorklist`,
`TypedPairs`, and `DiagnosticEdges` now each have exact changed-capacity route
trace witnesses; aggregate coverage in older Union tests did not by itself
certify each lane's event-to-sample linkage. Continue with the remaining
owner-to-route and per-use rollback matrix.
Keep the separate 63-line
`ResourceSampleChecked` extraction deferred until the accounting/measurement
checkpoint closes.

Verification for this slice: the focused incoming value-route sidecar passed
all fourteen tests, `cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`,
and `git diff --check` passed. The last completed full `yu-solver` library run
remains 202 passed. A new 209-test single-threaded run was interrupted after
more than six minutes in the F4 scale tests; before interruption,
`direct_root_n_and_2n_counters_remain_linear` was reported failed. Its isolated
rerun passed 1/1; the adjacent filtered pair of linearity tests also passed
2/2. An independent performance audit found randomized HashMap probe variation
plausible and no direct F5c path, but the failed assertion values were not
captured, so the cause remains open and the full suite is not certified. No benchmark or resource
matrix was run. The successful-path sampler-cost budget remains consumed
without accepted timing data. The `ValueLevels` retained-ledger slice is
checkpointed as `38d40b01` and pushed to `origin/yulang3`. The incoming
`FreshValueBounds` witness is now consolidated in the existing route sidecar;
it checks exact observed outer-row capacity deltas and event peaks, exactly
one post-rollback sample, independent retained/nested reconciliation, complete
RouteCheckpoint restoration, and retry publication. Its old test body was
moved out of `lib.rs`, which shrank by 75 lines. The M1 test-only slice is
checkpointed as `e226f8b4` and pushed to `origin/yulang3`.
The primary handled it directly per the user's no-subagent instruction, so no
independent reviewer was used. The corresponding `ExtrusionStack` witness now
derives its exact event delta and peak, proves post-rollback transient-capacity
release against the independent retained ledger, and retries through public
route records; that test has been moved from `lib.rs` into the same sidecar.
The `ValueExactUpper` witness now checks the exact `ValueEndpointKey` event
delta/peak in a fresh row, its removal at rollback, retained `ValueExactLower`
capacity, the independent post-rollback ledger, and canonical/receipt/
provenance/routed-use retry links. This M1 test-only slice is checkpointed as
`7c07b7af` and pushed to `origin/yulang3`. The paired `ValueExactLower`
witness now binds its exact event delta/peaks to the preexisting use row,
proves that capacity survives rollback through the independent ledger and
post-rollback sample, and checks canonical fact, receipt, provenance, and
routed-use retry links. This M1 slice is checkpointed as `f69dbb76` and pushed
to `origin/yulang3`. The `ValueDirectLower`/`ValueDirectUpper` witness now
checks exact row identity and slot deltas, event-time retained/nested totals
and peaks, the independent post-rollback ledger, RouteCheckpoint restoration,
and canonical/receipt/provenance/routed-use retry links. This M1 slice is
checkpointed as `8b118260` and pushed to `origin/yulang3`. Then audit the
residual owner-to-route lanes against the complete §3 list. Keep sampler-cost
remeasurement deferred: its previous process budget was consumed without an
accepted comparison, so another run needs a fresh budget and an isolating
method. Do not call the complete §3 sampling/accounting gate closed. The F5c
working set is preserved by checkpoint commits; inspect branch synchronization
before any push.

Mixed-height authority is resolved and recorded in the 2026-09-24 addendum.
The current code removes factorial alpha-key ranking from binder selection:
R owners follow first surviving `self.reentries` encounter, and Q owners
follow first occurrence through the retained predicate and then each selected
R lower/upper bound. A shared-identity fixture and an exact stored-trace-order
fixture cover those rules. The code remains in the working checkpoint until
the selected normalization is implemented; no §24 API or F5b callback change
is authorized. `lib.rs` is 27,892 lines after this slice (200 fewer than the
28,092-line resume point), with the factorial key/permutation implementation
removed. Checks: `cargo fmt --check`, `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (136 passed), and
`git diff --check`. No benchmark or F5e resource matrix ran. Next: implement
the bounded, stack-safe §36 height-major normalizer and preserve §44's
first-member projection; if that cannot fit the existing callback/accounting
boundary, stop with the exact separate decision required. Fixed-point replay
and component rescan limits, full §3 successful-path sampling/accounting
certification, and F5e public-observation/scale certification also remain
open. The current per-use owner-to-route audit is closed for the approved
pure-Function route set; do not widen into live effect-row mutation. A
subsequent full single-threaded library run was stopped during
`f4_unbounded_cycle_scale_4k_keeps_direct_frontier_linear` after more than
seven minutes and is not a passing result.

The older syntax-v0 vertical-implementation record below remains historical
context and does not override this active F5 gate.

## F5c iterative summary-to-draft materialization slice (2026-09-24)

`F5cSummaryStore::materialize_summary` and `node_iterative` were already
iterative. The remaining `F5cGeneralizer::materialize_positive` and
`materialize_negative` recursion over boxed Function/Union/Intersection trees
is now an explicit task/value walk in `crates/yu-solver/src/f5c_materialization.rs`.
Its task and value Vec capacities use two new entries in the existing
generalization-walker accounting/independent-ledger arrays. `lib.rs` delegates
these methods and is 27,700 lines, 112 fewer than the prior checkpoint; tests
remain in the sidecar. Implementation checkpoint: `68952716`.

Alternating Function chains of depths 2,048 (positive root) and 2,049
(negative root) pass on a 64 KiB thread stack and reconcile requested slots,
growths, peaks,
and release against the independent walker ledger. The full focused
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` passes 153 tests;
`cargo check --workspace`, format, and diff checks pass. This is only the
summary-to-draft materialization subgate. `term_value_rows`, guarded-owner
search, fixed-point replay, owner/reference/incidence/occurrence traversals,
and boxed-tree cloning/dropping still contain recursive paths. The finalizer's
positive/negative constructors recurse inside the §24 higher-ranked callback;
F5b §6 bars allocation/mutation of solver-owned scratch there, and the
indexed `yu-types` API remains an unapproved Draft. No full library-suite run
was repeated: the last attempt stopped after more than seven minutes in the
known F4 scale test, so that suite remains uncertified. No benchmark or F5e
matrix ran. Primary-only, with no independent reviewer; F5c/F5e are not
complete.

## Current user decision

The user's 2026-09-17 instruction closes the previous exhaustive per-slot CST-schema prerequisite and adopts the implementation-first completion policy in
[`2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md`](../notes/design/2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md).

The old loop of selecting the next bounded unmapped `Missing`/`Error`/`Invalid` candidate solely because catalog coverage remains open is finished. Do not restart it.

The current accepted grammar and direct Rowan topology are frozen as `syntax-v0` for the next implementation phase. Syntax may reopen only for a concrete structural collision, accepted-input/recovery bug, requirement exposed by the active vertical slice, or an explicitly approved new language feature.

## Governing authority

- Completion policy and freeze: [`2026-09-17 syntax freeze amendment`](../notes/design/2026-09-17-syntax-freeze-and-vertical-implementation-amendment.md).
- CST-derived diagnostic destination architecture: [`2026-09-09 CST-derived diagnostics amendment`](../notes/design/2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md), narrowly superseded by the 2026-09-17 completion policy.
- Accepted input and recovery authority: [`2026-09-08 successor recovery authority`](../notes/design/2026-09-08-successor-recovery-authority-amendment.md).
- Direct Rowan CST and recovery topology: [`Rowan CST-only amendment`](../notes/design/2026-09-09-successor-rowan-cst-only-amendment-draft.md) and [`Error/Invalid topology addendum`](../notes/design/2026-09-09-successor-error-invalid-topology-ordering-addendum.md).
- Catalog/evidence: [`successor CST slot schema catalog`](../notes/design/2026-09-10-successor-cst-slot-schema-catalog.md) and [`coverage record`](../notes/progress/successor-cst-slot-schema-coverage.md). These are evidence and later certification inputs, not an automatic blocking queue.

## Retained hard invariants

- Parsing has one durable lossless Rowan CST. Do not introduce an AST/materializer, second syntax tree, opaque Error replay/relexing, or hidden recovery classifier.
- `Missing`, raw `Error`, and structured `Invalid` remain the structural recovery facts. Environment-only facts do not mutate the CST.
- Final diagnostics are CST/environment-derived. The existing parser diagnostic ledger is temporary migration state only.
- Preserve accepted syntax, UTF-8/CRLF source ownership, current-Item ownership, retry/continuation, caller and fence handoff, and effect-free rejection unless a concrete separately approved correction requires otherwise.
- Do not add CST wrappers or nodes merely to improve diagnostic wording. A new structural distinction needs a real information-preservation requirement.

## Phase status

### Syntax-design prerequisite

Closed for ordinary implementation.

The existing evidence spans multiple independent structures: declarations, expressions, patterns, Rule/String literals, Item/Separator/Close sequences, raw Error retry, nested/same-offset Missing, foreign-close/caller boundaries and fence handoff. That is sufficient representative proof that the CST-only architecture is viable.

Remaining unmapped owner/caller/trivia/nested/fence permutations are not individually blocking. They become work only when a concrete trigger requires them.

### Direct Rowan state

Direct Rowan construction and Error-token/structured-Invalid topology are already implemented. The legacy public parser cutover is complete. The temporary recovery/diagnostic machinery still exists: `HeaderInfo` retains recoveries and `ParsedFile::diagnostics` has not yet been retired.

Do not delete that temporary machinery before the new shadow interpreter is exercised. Also do not treat its continued presence as permission to make it a final dependency.

## Gate 1: shadow CST diagnostic interpreter

Status: implemented (2026-09-18). The production whole-tree walk lives in
`crates/yu-syntax/src/structural_diagnostic.rs`; its focused witnesses are in
`crates/yu-syntax/src/tests/structural_diagnostic.rs`. The temporary parser
ledger is untouched. See `notes/progress/daily/2026-09-18.md`.

The walk derives zero-width `Missing`, maximal adjacent same-immediate-parent
raw `Error` groups, and structured `Invalid` preorder from the CST alone. It
emits precise schema information for the mapped expression-delimited `Missing`
and raw-`Error` rows, and a deterministic generic fallback (kind, range,
ordinal, ancestor path) for every other occurrence. It does not consult parser
recovery records, replay parsing, relex `Error`, or synthesize recovery nodes.

Known deferred items, not blockers:

- the two mapped structured `Invalid` owners still take the generic fallback;
- trivia-interleaved forms of the mapped delimited row are classified by the
  nearest structural sibling and are fixed by a focused witness rather than by
  a separate catalog row.

## Gate 2: effective syntax-table unification

Status: implemented (2026-09-18). The planner in
`crates/yu-syntax/src/operator_compilation.rs` builds the effective table without
diagnostics (`effective_full_parse_operators`), and `conflicting_local_operators`
derives conflicts by reading the accepted site in that same table. `ParsedFile`
retains the exact table the parser used and exposes it through `operators()`.
The temporary diagnostic ledger is unchanged. See
`notes/progress/daily/2026-09-18.md`.

Known limitation, not a blocker: the operator-chain CST is flat and binding
powers do not change it, so "parse and analysis consult the same accepted site"
is proved by the shared table instance plus analysis agreement rather than by a
tree-shape difference.

## After the shadow interpreter

Immediate next action: Gate 3, the approved first `yu-hir` slice. The user
approved `notes/design/2026-09-18-hir-operator-association-first-slice-draft.md`
on 2026-09-18 (D1a/D2b/D3a/D4a): a whole-CST operator-chain association pass
producing a minimal pre-HIR product, with no type. `yu-types` remains empty.

Gate 3 is implemented (2026-09-19). `yu-hir` now associates every encountered
`OperatorChain` from the exact `ParsedFile` operator table into the minimal
owned pre-HIR product. Nested chains are associated exactly once and retained
only through their enclosing `HirExpr`; `AssociatedChains` retains top-level
chains only, under the user-approved ownership amendment at
`notes/design/2026-09-19-hir-associated-chains-ownership-amendment.md`.
Focused M2 verification and final delta review are clean. No type, declaration,
name-resolution, `DefId`, diagnostic-publication, CST, or `yu-types` work was
introduced.

The approved simple module-resolution slice is implemented (2026-09-19).
`lower_module` now produces a total immutable `HirModule` for direct-root simple
bindings, plans stable module-local identities before body lowering, and resolves
identifier bodies against that completed namespace. It consumes one exact-table
association result per body and one CST-derived structural recovery projection;
no whole-file associated-tree copy or parser-ledger dependency is retained.
`yu-types` remains empty and no type attachment, imports, module graph, parameter
patterns, application syntax, or core IR entered the slice.

Immediate next action: perform the coherent parser-ledger/API retirement
migration now that the CST-derived structural interpreter has real frontend
exercise through `lower_module`. Preserve syntax diagnostics' public behavior
while removing the temporary parser recovery ledger as a final dependency; do
not combine that migration with type attachment or a new HIR feature.

Gate 4 repair decision (user-approved 2026-09-20): the proven BracketRow
Item/Close structural collision is a concrete `syntax-v0` reopen trigger. The
Authoritative `2026-09-20-successor-bracket-row-close-topology-supersession`
selects direct `BracketRow > Error+` for Item and
`BracketRow > TypeDelimitedForeignClose > Error+` for each local Close retry.
It preserves accepted input, recovery continuation, current-Item ownership,
fence handoff, and lossless source without Error-text inspection or
parser-private state.

Gate 4 parser-ledger/API retirement is implemented and verified on 2026-09-20:
`ParsedFile::syntax_diagnostics()` now derives the public syntax projection from
the lossless CST plus the retained syntax environment, and the temporary
`recovery_record` module and all parser-private recovery classification plumbing
are removed. Parser-local construction phases remain only where they preserve
retry/continuation control; they are not diagnostic metadata. The public
diagnostic payload exposes schema-owned occurrence identity, path, ordinal,
slot, and expectations. Test contracts now distinguish coarse recovery censuses
from exact CST/public-schema assertions and retain TypeML context-restoration and
effect-free selector witnesses.

Verification: `cargo check -p yu-syntax --tests` is warning-free;
`cargo test -p yu-syntax --lib -- --test-threads=1` passes 1368 tests with one
intentional ignore; `cargo test -p yu-hir -- --test-threads=1` passes 26 tests.
Gate 4 is complete: the approved BracketRow close wrapper is implemented,
generic CST-derived diagnostics retain distinct occurrence paths, M2
recovery/spec delta reviews are clean, and final verification passes. The next
frontend work must be selected by a new concrete vertical-slice trigger; do not
reopen completed parser-ledger retirement or the BracketRow topology without a
new contradiction or scope expansion. The next approved vertical slice is
direct-root `OperatorChain` HIR lowering under
`2026-09-20-hir-direct-root-expression-slice.md`; that neutral expression-owner
boundary is complete. The proposed next gate is the separately designed
`ConstraintBatch` collection boundary. Its exact expression-identity/type
semantics are Authoritative in
`notes/design/2026-09-20-directed-subtyping-integer-slice-draft.md`: the user
approved integrated choice 1 on 2026-09-20, and its M3 construction is complete.
The direct-root decimal-integer slice now ends at a total `SolvedModule` with
directed value/effect bounds and local `Unknown` results. Do not broaden it to
names, bindings, equality relations, generalization, annotations, or Core IR
without a new approved gate. Immediate next action: select the next concrete
vertical semantic slice from existing accepted input and the established
subtyping model.

The next binding-body-to-definition-root semantic gate is Authoritative in
`notes/design/2026-09-20-binding-body-definition-root-directed-subtype-draft.md`.
The user approved its recommended integrated choice on 2026-09-20 and its M3
construction is complete. Admitted bindings now own artifact-branded definition
roots; recovery-free integer bodies emit the value-only fifth relation, while
definition roots remain `Unknown`. Definition effects, name propagation,
equality, and generalization remain deferred. Immediate next action: select a
new approved vertical semantic gate; do not extend this relation implicitly.

Fixture-led identity inference is withdrawn as the active implementation
sequence. The active Authoritative design is
`2026-09-20-constraint-collection-scc-foundation-draft.md`: first collect the
complete definition/root/constraint/use structure, then build a sealed static
SCC/condensation plan and integrate its artifact-checked queries into the batch.
The frozen Yulang lifecycle is the semantic oracle; its superlinear incremental
graph mechanism is evidence rather than a code template. Identity-function
polarity remains later evidence. Open-root connection, closed-scheme
instantiation, generalization, and publication remain later gates. Immediate
F0 immutable collected definitions and dependency-only resolved binding-body
uses are complete with clean M3 implementation review. Collection remains one
HIR traversal plus one collected-endpoint pass; Name type/effect projections
and integer fact counts are unchanged. F1's standalone static SCC kernel is
also complete after three bounded M3 review/repair rounds. It uses iterative
Kosaraju over `parent -> target` arcs and freezes deterministic dependency-sink-first
components with exact internal/incoming use partitions. F2 batch integration is
complete after two bounded M3 review rounds: `ConstraintBatch` now owns one plan
frozen only after complete F0 endpoint resolution and exposes crate-private,
artifact-checked indexed queries without executing component semantics. The
F0-F2 foundation is complete. Immediate next action: design the first semantic
SCC execution gate over internal open uses, dependency-closed instantiation,
and atomic component publication before implementing any of them. Scheme/generalization
representation, recursive-cycle result,
Function syntax/types, application, methods/roles, and Core IR remain later
structure gates rather than fixture-specific extensions.

The F4 candidate is now drafted in
`notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md`. A user
correction and direct Simple-Sub/Yulang2 audit rejected the intermediate
`Bottom | IntQueued | IntDrained` model: live inference retains exact
lower/upper bounds and propagates canonical constraint pairs; only
generalization performs positive coalescing, polar-variable elimination, and
the final `Bottom | Int` simplification. The revised delta has no remaining
blocking or major compiler-referee finding. The user approved the corrected
complete gate on 2026-09-21; F4 is now Authoritative and its atomic
implementation is active.

F4 implementation reached a material performance rollback condition: the
required 4,000-member unbounded-cycle debug witness remained active beyond 80
seconds because every root recursively re-expanded the same cycle. The narrow
draft addendum
`notes/design/2026-09-21-f4-bound-membership-summary-addendum.md` proposes an
exact `IntPositive` lower-bound membership bit owned and updated only by the
canonical `constrain` path. It adds no graph/worklist or second type authority.
Implementation of that summary was paused for M3 review and user approval; the
safe F4 core and complete synthetic scale matrix remain uncommitted while the
approved repair is applied.

The remaining pair-cache decision is resolved: the user selected fixed-size
session-local endpoint keys on 2026-09-21. The cache will use only integer leaf
tags and dense value-row ordinals; `Term`, definition spelling, and module-path
hash/equality are excluded. The addendum completed clean M3 semantic,
specification, and performance review and is now Authoritative. Implementation
may resume against the exact private classification, value-only counter split,
peak accounting, and staged 1k/2k/4k measurement contract.

The authorized summary/key implementation hit its explicit rollback gate: the
exact 1,000-definition unbounded-cycle test did not complete within 30 seconds,
so 2k/4k and broad tests were not run. Static audit derived the owner as cubic
opposite-row replay over an alternating 2N-row cycle, not summary or hashing.
The new draft
`notes/design/2026-09-21-f4-direct-bound-frontier-addendum.md` replaces only
physical transitive Var-pair materialization with synchronous direct adjacency
and generic atom-bound frontier transmission. Existing uncommitted F4 work is
preserved. The addendum completed clean M3 semantic, specification, and
performance review. The user approved it on 2026-09-21, so it is now
Authoritative; implementation, exhaustive reference evidence, and staged scale
certification are active.

F4 implementation and certification are complete on 2026-09-21. The solver
now executes the frozen dependency-sink-first SCC plan with exact lower/upper
Simple-Sub bounds, synchronous direct adjacency plus atom-frontier propagation,
atomic component scheme publication, and incoming instantiation. Finalized
definition roots project through their closed `Bottom | Int` schemes; resolved
binding-body Name occurrences remain exact `(Unknown, Empty)`. `Never` remains
ordinary bottom. The private fact-store rebuild lane contributes to the public
aggregate without expanding the approved counter API.

The final scale evidence uses isolated single-size 1k/2k/4k capped processes
and a separate actual-observation ratio witness over all listed fields. Final
semantic, specification, and performance reviews are clean. Immediate next
action: select and design the next structure-first type-inference gate; do not
extend F4 implicitly to direct-root Name, Function/application, local
parameters, methods/roles, imports, Core IR, or dynamic dependencies.

Direct frozen-oracle inspection superseded the user-approved R2 executor model
on 2026-09-21. R2's Failed/Blocked SCC outcomes, dependency blocking, generic
backend, completed-session conversion, lifecycle query, added availability API,
and tests are withdrawn in full. The Authoritative successor is
`notes/design/2026-09-21-oracle-aligned-static-scc-inference-session-draft.md`:
Yulang3 will use one concrete inference session, retain F2 as the static
dependency-sink-first scheduler, and continue erroneous definitions through
ordinary SCC closure/generalization as Yulang2 does. `Never` is ordinary bottom,
not an error sentinel. F3a safely archived and removed the uncommitted R2 code,
restoring the exact F0-F2 solver baseline. F3b is complete: the unchanged solve
state and admission/result-building path now live in one private concrete
`InferenceSession`, with no component traversal, placeholder executor, public
API change, or extra source-sized work. F4 now implements the approved scheme
payload, occurrence components, generalization, and instantiation under the
fixed ordering obligations.

The broader associated-expression type attachment question remains open in
`notes/design/2026-09-18-hir-type-attachment-open-questions.md`; this foundation
does not attach inferred types to HIR.

For the active SCC-foundation successor, the user's explicit structure-first
direction overrides the older existing-fixture-only ordering below. F0-F2 use
definition-use records and a static plan over current resolved-name HIR; do not add Pattern ML
application merely to obtain a surface witness for these gates.

Proceed in this order for work outside the SCC foundation unless a concrete blocker
changes it:

1. Select the smallest **existing accepted** fixture that can exercise a useful valid-program path from source -> Rowan CST -> HIR/type analysis. Do not design new syntax for this slice.
2. Build that vertical frontend slice. Let implementation expose missing design information instead of pre-enumerating it.
3. Refine only the schema/recovery cases that the vertical slice or failing tests actually require.
4. Once the shadow interpreter has real frontend exercise and total CST-derived handling, perform the coherent parser-ledger/API retirement migration.
5. Reserve broad catalog completion, fuzz/property matrices and presentation specialization for explicit release/certification work.

## Concrete triggers that may reopen syntax/schema design

A new bounded schema or topology investigation needs one named trigger:

- a CST occurrence cannot be interpreted safely by the precise or generic path;
- two required facts are structurally indistinguishable in the CST;
- accepted input or required recovery continuation regresses;
- the active vertical implementation needs a precise distinction not currently present;
- explicit release/final certification requests exhaustive coverage;
- the user explicitly approves a new language feature or grammar change.

An unmapped catalog row by itself is not a trigger.

## Work-budget rule

Do not measure progress by schema coverage percentage during this phase. Do not select a new owner merely because the previous owner closed cleanly. Each syntax/recovery investigation must name what concrete implementation/release work it unblocks.

Use the lightest existing M0-M3 mode that covers the actual change. A repair
round that makes no material progress returns to root-cause or design
reconsideration; it does not justify an expanding reviewer panel or an
expanding malformed-input permutation table. Numeric review/repair round
limits do not apply.

## Historical navigation

The former `tasks/current.md` exhaustive-gate log remains available in git history before this 2026-09-17 reset. Durable older evidence also remains under `notes/progress/`, especially `successor-cst-slot-schema-coverage.md`, `successor-typed-recovery-ledger.md`, daily records, and the 2026-09-12 handoff/navigation snapshot.

Do not copy that history back into this current-task file. Keep this file focused on the active gate, blockers, and immediate next action.

## Completion criterion for this task

The current task is complete when the shadow CST diagnostic interpreter is total over encountered recovery structure, the representative focused checks pass, and the next valid-program vertical frontend slice is selected from existing accepted fixtures. Full per-slot catalog completion is explicitly not part of this task.
