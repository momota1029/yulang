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
