# F5c shared producer walker with a flat candidate sink

Status: User-approved staged implementation; production cutover and resource probes remain unauthorized
Scope: Candidate-side flat values at the existing F5c row/term producer task boundary
Related authority: `2026-09-25-f5c-flat-indexed-stack-independent-draft.md` §§2–8, 15, 17–21; F5 §§22, 24–25, 32–36, 43–44
Approved staged decision: Keep one `F5cWalkTask` interpreter and parameterize its value construction through a boxed sink and a non-shipping flat sink; move F5c generalization ownership out of `lib.rs`; make no production caller cutover in this gate
Reviewed-by: M3 `compiler_referee`, `spec_auditor`, and `performance_auditor`; blocking/major findings closed by focused delta reviews on 2026-09-26
Supersedes: none

## 1. Why this design gate exists

The current `F5cGeneralizer::walk` owns row/term traversal, active-state
tracking, reentry discovery, cache decisions, task order, and frame cleanup. Its
`F5cWalkValue` carries recursive `F5cPositive` / `F5cNegative` trees. The exit
tasks structurally deduplicate those trees, then successful cache admission
converts them into the already-flat component summary memo. A module-local
caller cannot receive leaf/exit decisions as flat IDs through the existing
interface. Calling `walk` and converting its result retains the boxed source;
copying the task machine creates a second producer implementation.

The proposed shared interpreter changes internal production code and its
potentially hot path, even while the flat sink has no production caller. This
draft therefore requires a fresh focused M3 review and explicit user approval
before implementation. It does not authorize a production cutover or close
the separate §15 resource-measurement gate.

## 2. Shared interpreter and module ownership

Put the F5c generalizer, its component-summary memo and transaction, raw-root
forest coordination, shared task interpreter, and boxed/flat sinks under one
solver-owned `f5c_generalization.rs`. The existing `f5c_replay`,
`f5c_materialization`, `f5c_binder_substitution`, `f5c_tree_analysis`,
`f5c_normalization`, and `f5c_draft` modules keep their corresponding
operations. `lib.rs` retains the call site that requests a component draft and
the surrounding solver/fact installation orchestration; it does not own the
F5c memo, producer traversal, sink arena, or rollback algorithm.

This moves the F5c implementation cluster currently around the summary memo
through `F5cGeneralizer::build_inner`, not only the task interpreter. Keep the
exported-to-siblings surface `pub(super)` and narrow. Move or expose only the
unit-test helpers needed by existing test modules; do not broaden the crate
API. This is a substantial ownership move whose exact item/test list must be
confirmed before editing. It should reduce `lib.rs`; it does not claim an
immediate reduction in total source or binary size while the temporary flat
candidate and boxed compatibility sink coexist.

One generic `walk_with<S: F5cWalkSink>` interpreter schedules the exact same
`F5cWalkTask` sequence for either sink. The boxed sink remains the compatibility
adapter used by all current production callers. The candidate flat sink is
uncalled by production. The walker, not either sink, retains responsibility
for:

- direct/exact endpoint visitation order and Function field order;
- active rows, frames, path hops, taint, reentry recording, and invalid-effect
  detection;
- warm-cache lookup, active-conflict handling, cacheability propagation,
  successful admission order, and component-level rollback ownership;
- lane observation and checked availability errors.

The sink owns only value representation and operations whose semantics depend
on it: leaves, ordered Function construction, first-seen Union/Intersection
deduplication, structural equality, and flat-summary promotion. The walker
owns the transaction boundary: it prepares admission, commits the memo key,
records the undo event, and only then performs any later fallible observation.
The boxed sink keeps the existing boxed equality and memo conversion behavior.
Generic value-slot accounting uses the actual sink value size; no separate
task interpreter or copied row-order logic is added.

## 3. Candidate flat value and cache bridge

`FlatDraft` alone cannot represent a warm `Shared(summary_id)` result. The
walker compares two shared summaries by ID as atomic values; eagerly expanding
one into ordinary draft nodes could change deduplication and move incidence
marks. Use one temporary tagged flat source arena for the complete raw
component-root phase (predicate plus every dynamically discovered reentry
owner's lower and upper root):

```text
WalkValue {
    ref: Local(positive_or_negative_id) | Shared(summary_id),
    polarity,
    cacheable,
}
```

Local nodes have polarity-specific IDs, scalar leaves, child spans, and pure
Function fields. Their child entries use the same tagged local/shared
reference. No node or child owns a `Box` or recursive `Vec`. A Local reference
compares structurally only with another Local reference; Shared references
compare equal only when their summary IDs match, preserving the current
`F5cPositive::Shared` / `F5cNegative::Shared` behavior. First-seen duplicate
survivors alone contribute to the parent's cacheability, exactly as today.

On an untainted cacheable row exit, the flat sink prepares promotion of the
reachable Local subgraph child-before-parent into `F5cComponentExpansionMemo`,
linking existing Shared references directly to memo IDs and adding the same
row/polarity incidence to the promoted root (an alias when the root value
itself is Shared). The walker then commits the expansion key through the
component transaction and returns the resulting Shared ID. An uncacheable row
remains Local and is never copied into the long-lived memo. This keeps
temporary candidate nodes out of memo retention while preserving the memo's
reverse-parent invalidation graph and active-row conflict behavior.

Do not materialize roots as each walk returns. Retain the raw forest in the
flat source arena while the shared producer orchestration performs all walks:
predicate first, then each unique reentry owner in first `self.reentries`
encounter order, with lower then upper roots and the same missing-bound
Bottom/Top defaults. Keep an explicit `raw_owner_order` vector alongside the
owner-keyed bounds map; use the map only for lookup. After the last walk, apply
the existing invalid-effect rejection point. On success, materialize the
predicate, then visit owners in `raw_owner_order`, lower before upper. Do not
use `HashMap::values_mut` or a `HashSet` to choose traversal order. This
defines a stable callback sequence consistent with the producer-order
authority; it does not redefine final R order, which remains the first
surviving trace sequence, or Q order, which remains first encounter in the
retained predicate/R-root traversal. It must not add a second callback for
Local nodes. Run the same pre-pruning incidence census over the completed raw
forest, then preserve the existing R-survival, retained-owner encounter
order, Q encounter order, and substitution sequence. A candidate root-forest
test must compare the complete callback trace and resulting Q/R ordinals,
including a warm Shared in the predicate and a row first encountered in a
later bound; varying bounds-map insertion/hash order must not alter them.

The current boxed helper iterates its owner-keyed bounds map during
materialization. That container iteration is not the F5 producer-order
contract: the authoritative addendum forbids map iteration from selecting
output order, and Q/R assignment already derives from the ordered retained
forest rather than `self.order`'s incidental insertion sequence. The shared
producer refactor must replace that incidental raw-bound iteration with the
explicit owner sequence for both sinks. If source review shows a public or
authoritative counter depends on the incidental order, return to design rather
than preserving a hash-selected result.

Once materialized, the temporary source arena can be dropped; ordinary drop is
flat. The cumulative `FlatDraft` remains the owner for replay and later flat
passes. Root and bound values are retained by indexed roots, not copied boxed
trees.

This is a proposed representation boundary, not yet a proven equivalent
implementation. In particular, implementation review must verify promotion
incidence and transitive counts, Shared-vs-Local duplicate behavior, callback
order, reverse-parent edges, and repeated Shared occurrences. No resource
margin follows: the retained source forest, promoted memo nodes, and the
occurrence-expanded `FlatDraft` may coexist and can grow substantially. The
candidate must charge source node/edge creation, promotion visits and copies,
Shared occurrence expansion, and temporary/worklist admissions under the
approved solve-wide work meter. Its physical peak must sum the simultaneously
retained source, memo, draft, and scratch capacities. This records accounting
categories only; numeric limits, probe approval, and measured margins remain
in §§5/15.

## 4. Error atomicity and rollback ownership

Each sink operation uses checked, fallible lane growth. A failed producer
component truncates every temporary source-arena lane and every appended
`FlatDraft` lane to its entry lengths; retained capacity and monotonic work /
attempt accounting remain truthful. The component transaction restores
semantic memo roots, root edges/heads, memo nodes/children,
incidence/reverse-parent edges, and producer-owned order/reentry state.
Require an idle component-entry state: no active rows, active conflicts, or
pending conflict-journal entries. Visit-epoch and traversal scratch must
return to the documented idle checkpoint or be reset as one component-owned
lane.
`build_component` is the transaction boundary; a failed component is not
reused as a successful draft.

Replace the separate admission-key and invalidated-edge rollback batches with
one chronological component undo log keyed by stable root-edge indices. Each
logical root mutation has a prepared log slot and all required map/vector
capacity before mutation; after mutation, append its event immediately with no
fallible operation between. Record `Admit(edge)` and `Invalidate(edge)` events
and replay them in strict reverse order before truncating component-created
nodes. This handles both new admission → invalidation of that edge → failure
and old-key invalidation → same-key re-admission → failure without confusing
equal keys or popped edge indices. `Invalidate` undo restores only the
persistent root edge and root lookup. It does not restore an `active_conflicts`
count captured from a transient row active inside the failed component. After
reversing persistent root events, reset transient active/conflict/work scratch
to the required idle-entry state; this prevents an invalidated root's old
active conflict from being resurrected after its active row has been removed.
On success, assert that active rows and conflicts have returned to idle before
committing the log.

Undo must not allocate: preflight root-map capacity and prove that reverse
replay never exceeds the greatest live-map length already admitted. All
reserves and checked arithmetic in `memo.admit` happen before publishing the
root edge; a reserve failure leaves semantic roots unchanged while retained
capacity and charged attempt counters are reconciled, not rolled back. Any
post-publication observation failure is covered by the already recorded event.

Make active transitions atomic with their local walk mirrors. Before
`enter_active`, reserve active/frame/set lanes and preflight memo changes; a
failed `enter_active` changes no semantic active state. After successful
entry, update `active` and `active_set` before any fallible observation. On
exit, `leave_active` either fails without mutation or succeeds; after success,
remove the local active mirror before any fallible observation. Cleanup then
undoes each completed active transition exactly once. Audit all checked peak
accounting inside enter/leave so no error can escape after mutation without a
registered undo token. Walk failure aborts the component; component rollback
owns memo and invalidation restoration. This does not promise that a failed
walk may be resumed in-place.

The boxed and flat sinks share this transaction ordering. Add failure
witnesses for each reserve/observation boundary, active enter/leave, new
admission then invalidation, old invalidation then same-key re-admission, and
an active-row conflict followed by invalidation and later failure. After
rollback, compare every persistent semantic memo lane to its complete
pre-state, verify transient lanes are idle, then retry the same warm lookup
and prove it is not spuriously conflicted. Prove cleanup does not panic or
allocate. This producer rollback does not replace the still-open §44
transaction across private constraints and public representative admission.

## 5. Design-review outcome and implementation evidence

The focused M3 design review converged on 2026-09-26 after two focused
repair/delta rounds, with no accepted blocking or major findings. The
independent reviewers were `compiler_referee`, `spec_auditor`, and
`performance_auditor`; their scopes were:

- `compiler_referee`: exact traversal and dedup semantics, reentry/taint,
  admission and invalidation, full error/unwind cleanup, and no recursive flat
  success/error drop;
- `spec_auditor`: §§2–8 and §17 contract fit, Q/R and owner ordering,
  incidence/counter meaning, existing boxed-call compatibility, and exact
  candidate/non-production boundary;
- `performance_auditor`: boxed successful-path overhead, generic code growth,
  temporary and promoted lane coexistence, repeated conversion/work, and
  `lib.rs`/module ownership cost.

These are implementation obligations, not prerequisites to the user's
decision to authorize work on this reviewed non-shipping proposal. Before
calling the producer candidate slice coherent, shallow witnesses must compare
boxed and candidate values, ordered
incidences, cache hits, duplicate selection, Q/R source-owner ordering,
failure cleanup, and the complete raw predicate/bound forest before any lossy
transform. Include warm Shared roots nested below both Function polarities,
distinct Shared IDs, identical Local subgraphs, mixed Local/Shared children,
cacheable and tainted rows, valid pure effects and invalid effects after
partial producer work, empty-side defaults, R-before-elimination and Q
encounter ordinals, later-member promotion failure, and failure after memo
admission but before the walk returns. Compare separately: memo incidence
metadata and transitive counts; per-occurrence incidence callback sequence;
and the shared-summary-hit logical counter. A small-stack correctness witness
must exercise the flat candidate's producer and drop; it is not a
resource/scale measurement.

The generic boxed instantiation must not introduce a virtual call or allocate
the candidate source arena. Static dispatch is not proof of zero successful-
path cost: compare sink call frequency, actual value-slot size, optimization
and code-size effects, first-seen structural comparison task counts, summary
promotion/copy work, and source+memo+draft co-residency in the reviewed §15
plan. Flat IDs do not remove the current worst-case quadratic number of
first-seen member comparisons or the cost of comparing compound members.
No numeric resource limit or successful-path margin is selected here.

The user approved this reviewed proposal on 2026-09-26. Approval authorizes the
staged internal implementation, not production cutover, numeric resource
limits, resource probes, or F5c/F5e acceptance. A green build or test does not
authorize those later gates. Any unresolved interface or rollback finding
returns to this draft. The implementation remains staged: first relocate the
F5c generalization owner with no intended behavior change; then close its
transaction/active-state rollback gaps; then add the shared sink and ordered
flat raw-root forest; then the remaining flat transformations and indexed
finalizer. Avoid adding a second algorithm for Q/R owner discovery. Before the
first resource probe, prepare and independently review the exact §15 plan.

## 6. Explicit non-goals

- No change to Oracle-observable schemes, Q/R policy/order, normalization,
  effects, counters, public routing, or §44's representative/transaction.
- No depth cap, numeric size/work cap, benchmark, or resource probe.
- No production caller change, release acceptance, `yu-types` API, or claim of
  F5c/F5e completion.
- No copied task walker and no second producer source of truth.
- No unrelated `lib.rs` cleanup. Moving the F5c generalization cluster is in
  scope because it establishes the requested ownership boundary. The boxed
  compatibility sink is temporary; once the flat path replaces it and passes
  its gates, remove the recursive boxed draft and adapter rather than keeping
  two permanent producer authorities.
- No claim that explicit stacks alone bound allocations or make path-expanded
  Shared summaries cheap; those costs remain visible success-path/resource
  tradeoffs under the user's Oracle-and-lightweight priority.

## 7. First implementation slice (2026-09-26)

The first approved slice is implemented in the solver-owned
`crates/yu-solver/src/f5c_generalization.rs`. It relocates the boxed F5c
positive/negative draft,
component expansion memo and transaction, task walker, and `build_inner`
generalization owner out of `lib.rs`. `lib.rs` retains the component-draft
invocation and surrounding solver/fact orchestration. Production callers still
use the boxed path; no flat sink, shared generic walker, behavior change, or
caller cutover was added.

The M2 exact-conformance review found one minor visibility issue: unused
`visit_epoch` and walker transaction/checkpoint state had been exposed to the
parent module. Those fields are now private; `active_set` remains
crate-internal because the materialization sibling and existing tests use it.
The regression review found no issue. Focused primary verification passed:
`cargo fmt --check`, `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (183 passed, 1
ignored), and `git diff --check`. No benchmark, resource probe, or workspace
test suite ran. The next slice is the memo transaction/active-state rollback
repair and failure witnesses; the flat sink and §15 resource plan remain later
gates.

## 8. Memo transaction and active-state rollback slice (2026-09-26)

The second approved implementation slice closes the component expansion memo's
transaction/active-state rollback gate in `f5c_generalization.rs`. Persistent
root admission and invalidation events use one chronological undo log; failure
replays events in reverse publication order, then resets transient active
rows/conflicts, work, visit marks, and local mirrors before truncating appended
summary nodes. Cleanup reuses preflighted root capacity and does not allocate.

Fallible `push_children` now propagates a reserve error before extending the
child lane. If a failed reserve nevertheless retained capacity, the actual
capacity and growth accounting are reconciled before returning. Simultaneous
memo/generalizer scratch capacity samples are captured only on actual lane
growth. The independent test ledger computes its peak by folding those
snapshots and exact element sizes, rather than reading the production aggregate
peak.

Focused tests cover complete persistent-state restoration, idle transient
state, a warm raw `Shared(summary_id)` lookup and retry, nonzero marks on
failure entry, interleaved admit/invalidate undo, and no partial child append
after reserve failure. The latest M2 `compiler_referee` and
`performance_auditor` delta review found no blocking or major finding.
Verification passed: `cargo fmt --check`; the F5c filter (192 passed, 1
ignored); the single-threaded no-default-feature `yu-solver` library suite
(277 passed, 1 ignored); and `git diff --check`. The broad suite took 717.77
seconds. No benchmark or §15 resource probe ran; measurement budget remains
zero.

The boxed sink remains the sole production path. Summary sharing, owner/order
decisions, Q/R, schemes, and public routing are preserved. The flat sink is
still uncalled; this slice does not close §44 route atomicity or authorize a
production cutover. Next is the uncalled flat candidate sink through the
shared producer walker, followed by its remaining parity/rollback gates.
Indexed finalization, complete ineligible/effect rejection, closed-DAG
memoization/resource accounting, §44 end-to-end per-use rollback, and §15
evidence remain open. Do not claim F5c/F5e completion.

## 9. Solve-wide checked logical-work meter subgate (2026-09-26)

The implementation now carries one `F5cDraftWorkMeter` for the lifetime of an
inference session and shares it with each component's F5c memo/generalizer.
Charges use checked arithmetic; arithmetic exhaustion returns
`IdentityExhausted` rather than wrapping. There is no chosen work limit. The
counter is logical repeat-work accounting, not a depth limit, allocation
budget, physical-capacity ledger, wall-time guarantee, or §15 peak estimate.

Its lifetime is intentionally broader than component rollback: a rejected or
failed component has still consumed solve work, so charges remain, while the
component memo's published roots, edges, transient marks, and appended nodes
continue to restore transactionally. Charges cover the boxed producer and the
currently exercised analysis/materialization/replay/substitution paths,
including task scheduling and visits, inspected/emitted edges, owner/Q/R work,
and bulk typed drains. Charges that guard boxed output construction and drains
precede those operations. First-observation order registration counts the
lookup, set insertion, and vector append; a revisit counts its lookup.

Overflow witnesses assert rejection before Function construction or any of
the five finish/drain owner families mutate their lanes, for both polarities,
and assert a clean successful retry. The F5c filter passes (207 passed, 1
ignored); the dedicated work-meter filter passes (15). `cargo check -p
yu-solver --lib` passes without warnings, as do `cargo fmt --check` and
`git diff --check`. The single-threaded no-default-feature library suite
passed (292 passed, 1 ignored; 952.91 seconds).

Static performance review found only constant-factor meter-update and lookup
costs; no timing or successful-path margin is claimed. No benchmark or §15
resource probe ran, and measurement budget remains zero. This closes the
logical repeat-work subgate only. Physical retained capacity/co-resident peak,
the reviewed §15 plan and measurements, the uncalled flat sink, indexed
finalization, production cutover, §44 per-use rollback, F5e, and overall F5c
closure remain open.

## 10. FlatDraft tree-analysis adapter slice (2026-09-26)

The existing explicit-stack analysis walker now has a test-only FlatDraft-ID
input path through the same event scheduler used for boxed values. It preserves
polarity, Function argument/result guard changes, ordered depth-first events,
and repeated-edge occurrence visits. Existing boxed analysis callers and the
production producer remain unchanged.

Focused witnesses compare full `(owner, polarity, guarded)` traces for
positive and negative repeated child IDs, early termination, unique occurrence
order, incidence/reference sets, and guarded-bound results. Invalid root/child
IDs and overflowing/out-of-array spans return `IdentityExhausted`, clear
pending tasks, and allow a valid retry. Repeated-edge work charges are equal
for the boxed and indexed inputs. M1 `spec_auditor` review initially found
missing event/invalid-input witnesses; a batched repair and focused delta review
closed both findings. The existing 4,096-depth 64 KiB stack witness also passes
after heap-owning its large captured store before worker creation.

Verification passed: the new FlatDraft trace/failure test, the small-stack
analysis test, `cargo check -p yu-solver --tests --message-format short`,
`cargo fmt --check`, and `git diff --check`. No broad suite, benchmark, or §15
probe ran. The production path remains boxed. Next: route FlatDraft roots
through the same incidence/R/Q ordering core as boxed roots, and keep the
candidate component memo transaction open through every subsequent fallible
stage. Full callback/Q/R parity, late rollback, resource certification,
indexed finalization, and production cutover remain open.

## 11. Raw-forest memo transaction precursor (2026-09-26)

The test-only ordered raw-forest builder leaves its memo root transaction open
after materialization. Releasing a forest commits the root transaction and
advances the memo checkpoints; aborting releases the forest lanes and rolls
back root admission/invalidation events plus appended nodes. Any rollback error
poisons the candidate generalizer at the shared abort owner, including errors
from construction-failure and flat-walk exits, and both flat entrypoints reject
reuse afterward.

The M2 compiler-referee/spec-auditor delta reviews closed after the abort
witness was expanded to start from a warm root, invalidate and re-admit its
key, compare every persistent semantic root/node/edge/head/undo/incidence lane
after abort, verify transient state is idle, and retry the same forest.
Separate injected corruption witnesses cover explicit-abort and construction
rollback errors. Focused raw-forest tests (8), solver library and test-target
checks, formatting, and diff checks pass.

This is a raw-forest transaction precursor only. The FlatDraft forest is not
yet connected to the shared incidence/Q/R, replay, substitution, and
normalization stages. Full callback/Q/R order parity and a failure from an
actual later fallible stage must still prove rollback through the same open
transaction. Production remains boxed; no resource probe, numeric boundary,
§44 closure, F5e acceptance, or overall F5c completion is authorized.

## 12. Shared raw-incidence census slice (2026-09-26)

The boxed `build_inner` producer and the test-only FlatDraft raw-forest path now
call one `raw_forest_incidences` implementation. It visits the predicate first,
then unique raw owners in their recorded order, charging one raw-bound-owner
unit before visiting each lower root and then upper root. Both representation
adapters use the existing Walker event scheduler and return the same positive
and negative incidence sets for the focused parity fixture.

The paired witness covers predicate contributions, two owners whose declared
order differs from map insertion order, positive lower roots, negative upper
roots, and Function guard traversal. FlatDraft has no Shared node form, so the
warm Shared raw-forest callback witness remains separate. M3 compiler-referee,
spec-auditor, and static performance reviews found no blocking or major issue.
The minor parity evidence gap closed with the exact-set fixture and primary
diff review. Nine focused raw-forest tests, solver library/test-target checks,
formatting, and diff checks passed. No benchmark or §15 probe ran.

This slice shares only the pre-pruning incidence census. The R fixed point,
retained-occurrence pass, Q/R binder assignment, flat replay/substitution/
normalization, full callback/Q/R parity, and rollback after an actual later
fallible stage remain open. Production still calls the boxed producer and
remains the only production path. No resource certification, numeric boundary,
§44 closure, F5e acceptance, or overall F5c completion is authorized.

## 13. Shared R fixed-point slice (2026-09-26)

The boxed producer and test-only FlatDraft adapter now use one `r_candidates`
loop for candidate eligibility, bound replay and guarded-bound filtering,
guarded trace pruning, predicate replay, raw-bound reference reachability, and
fixed-point convergence. The boxed adapter preserves the prior replay order,
work-charge sites, and candidate behavior. The FlatDraft adapter replays into
its retained output arena and uses the same Walker analysis operations.

The raw-forest test wrapper owns the open memo transaction across R filtering.
On any R error it aborts the forest, rolls back root mutations and appended
memo state, resets transient lanes, and poisons the candidate on rollback
failure. The failure witness allows one replay to emit output before a later
replay fails, compares persistent roots, edge/index/node lanes and visit state,
verifies idle transient state and monotonic work, then retries a warm lookup.

Flat replay charges initialization for both source-wide active arrays before
allocation. The arrays and the five retained output lanes have distinct
capacity accounting and participate in co-resident observations with source,
memo, and forest storage. Replay drops temporary arrays before releasing their
lanes; the R owner drops output before releasing its five lanes. Direct replay
fixtures use the same release lifecycle.

The M3 compiler-referee, spec-auditor, and performance-auditor delta reviews
found no remaining blocking or major issue. A minor rollback assertion gap was
closed by checking all five output lanes; a minor error-path drop-order gap was
closed by dropping the second active array before releasing its lane. Focused
flat-walker (25), replay (6), generalization-transaction (11), and composed
replay/substitution/normalization (1) tests pass, as do solver library and
test-target checks, formatting, and diff checks. No resource measurement or
§15 probe ran.

This slice shares only the R fixed-point filter. Post-convergence retained-R
assembly and order, Q/R ordinal assignment, flat substitution and
normalization integration, complete callback/Q/R parity, and rollback through
those later fallible stages remain open. Production remains boxed. No resource
certification, numeric boundary, §44 closure, F5e acceptance, or overall F5c
completion is authorized.

## 14. Shared post-convergence retained-R and Q/R slice (2026-09-26)

The boxed producer and test-only FlatDraft adapter now use one post-R selector
for retained-bound replay, guarded-bound survival, guarded-trace survival,
recursive-owner order, retained occurrence traversal, Q/R ordinals, and
unclassified-row rejection. Retained replay and guard checks follow the
recorded `raw_owner_order`. R owners follow the first surviving trace for each
owner, preserving trace encounter order while removing duplicate owners. Q
first occurrences follow the retained predicate, then each R owner's lower
bound before upper bound. HashMap/HashSet iteration does not choose emitted
ordinals.

The FlatDraft adapter grows every post-R collection fallibly and records its
capacity in a distinct lane: retained bounds, surviving bound owners,
surviving trace indices, recursive owner vector and set, occurrence order and
seen set, and Q/R maps. The occurrence adapter uses the existing explicit-stack
Walker scheduler with a fallible event callback. Temporary collections drop
before their lanes release; retained selection collections stay accounted with
replay output and the open raw forest until explicit release or abort. On
error, the wrapper releases output and post-R lanes before aborting the memo
transaction.

Paired boxed/flat tests cover raw owner order `[1,2]` versus surviving trace
order `[2,1,2]`, first-trace deduplication, Q order across predicate and lower/
upper bounds for both owners, R offsets, and rejection when a candidate lacks
a raw owner. The late-failure witness injects an error after R convergence,
lets the first post-R bound replay emit output, fails on the next replay, and
checks persistent memo restoration, output and all post-R lane capacities,
idle transient state, and warm retry.

M3 compiler-referee, spec-auditor, and performance-auditor delta reviews found
no remaining actionable finding. Focused `post_r_` tests (4) and
`f5c_tree_analysis` tests (4) pass, as do `cargo check -p yu-solver --tests
--message-format short`, `cargo fmt --all --check`, and `git diff --check`.
No broad suite, benchmark, resource probe, or §15 measurement ran; measurement
budget remains zero.

This closes only the shared post-convergence R/Q selector. Flat substitution
and normalization integration, full callback/Q/R parity, rollback through all
later fallible stages, physical resource certification, and the reviewed §15
measurement gate remain open. Production remains boxed; no numeric boundary,
production cutover, §44 closure, F5e acceptance, or overall F5c completion is
authorized by this slice.
