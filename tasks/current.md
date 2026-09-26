# Current task: F5 general Function scheme foundation

Updated: 2026-09-27. Branch: `yulang3`; do not modify frozen `main`.

Resume handoff: [`2026-09-22 F5c scheme-closure handoff`](../notes/handoffs/2026-09-22-f5c-scheme-closure-handoff.md).

### Latest continuation (2026-09-27): persistent producer-state lanes

The next seven persistent `F5cGeneralizer` states now use typed lanes in the
existing `F5cWalkerResources`: uncacheable and provisional-row sets, path,
ordered rows and its seen set, outer guarded reentries, and the aggregate
capacities of nested reentry trace paths. Growth uses fallible reserves and
observes actual capacities; a copied path's peak includes the source path and
all retained traces. Component success and failure drop these collections
before returning their lanes to idle while retaining request/growth/peak
history. Focused witnesses cover a failure after the order-seen lane grows,
trace-copy failure and retry, co-resident path capacity, and memo restoration.

The M2 compiler-referee and performance-auditor reviews found no blocking or
major issue. The performance review noted that the current aggregate test partly
reconstructs live bytes from the mirrored lane ledger rather than enumerating
every physical collection; complete independent physical-lane reconciliation
remains a required later §15 gate. Focused checks passed: solver test-target
check; transaction tests (14), work-meter tests (13), flat-walk tests (36),
and the nested-path test (1); `cargo fmt --check`; `git diff --check`. No
resource probe, benchmark, or broad suite ran.

This closes only persistent producer state. Next account the remaining
`build_inner`/R-selection local collections, then the boxed normalizer failed-
reserve path and solver/draft/finalizer same-time peak in their existing owners.
Only after that physical ledger is complete should a fresh §15 plan receive
independent review before any probe. Production remains boxed; no producer
admission, numeric boundary, cutover, §44 closure, F5e acceptance, or overall
F5c completion is claimed.

### Latest continuation (2026-09-27): closure and raw-incidence resource lanes

The first solver-side physical-lane slice now accounts `non_generic_closure`
adjacency storage, its aggregate nested HashSet buckets, reusable connected
set, returned closure set, and frontier, plus both raw-incidence polarity sets.
All seven lanes live in the existing `F5cWalkerResources` family. Growth is
fallible, capacity and memo co-peak are observed after reserve results, and
lane release follows collection drop on success/error paths. Boxed and flat
incidence walks share the same accounting owner. Duplicate insertion attempts
remain counted but do not trigger needless growth; the full-table novelty
check runs once.

M2 compiler-referee and performance reviews converged after two focused
performance repairs. The claim that HashSet control bytes were missing was
rejected under F5 §34, which explicitly excludes allocator metadata/control
bytes from its `capacity * size_of::<slot>()` model. The accepted duplicate
reserve and repeated-probe findings were repaired and passed fresh delta
review. Focused witnesses cover closure parity, boxed/flat incidence parity,
per-lane capacity reconstruction, duplicate-at-capacity, failure cleanup, and
retry.

Checks passed: `RUSTC_WRAPPER= cargo test -p yu-solver --lib
f5c_flat_walk_sink -- --test-threads=1` (36), the `f5c_non_generic_closure`
filter (2), `RUSTC_WRAPPER= cargo check -p yu-solver --lib --message-format
short`, `cargo fmt --all --check`, and `git diff --check`. The package check
initially exposed pre-existing production-only unused fields
`F5cPostRSelection::{retained_bounds, retained_predicate}`. A separate M0
follow-up marks their test-only use at the owning fields; `cargo check` now
passes without warnings. No resource probe, benchmark, or broad suite ran.

This closes only the closure/raw-incidence lane slice. The next implementation
gate is the remaining `build_inner`/R-selection locals, followed by boxed
normalizer failed-reserve observation and the solver/draft/finalizer same-time
peak. Only after those owner gates close should a fresh §15 plan receive
independent review.
Producer incidence admission, numeric support boundary, production cutover,
§44 closure, F5e acceptance, and overall F5c completion remain open. No user
decision arose in this slice.

### Latest continuation (2026-09-26): `yu-types` indexed finalizer

The approved §3 `yu-types` indexed transaction now has an implementation and
focused M3 closure. It validates checked IDs/spans/Q/R ordinals and the full
structural graph with iterative three-color DFS, constructs in prescribed
bound/root/Function/product order, uses the handles returned by the active
finalizer, and bypasses the quadratic callback validator only on the validated
indexed path. Eleven callback-scoped temporary lanes use checked geometric
growth and reconcile actual capacities into the existing arena/Scratch peak;
indexed child/effect/Q/R and bound lanes are pre-reserved from checked input
counts. No public item beyond the approved method and seven §3 types was added.

The M3 compiler-referee, spec-auditor, and performance-auditor delta reviews
converged after repairs. Witnesses compare callback/indexed alpha-equivalence
and complete ordered event traces for positive/negative Functions, Q/R,
shared/repeated Union and Intersection edges, and bound roots. Focused tests
cover malformed IDs/spans/Q/R, cycles/orphans, every indexed temp lane,
validation/before-handle/planning/reservation/commit failures, retained-capacity
retry, terminal poison/short-circuit, panic-preserving unwind, exact lane/peak
accounting, and 64 KiB positive/negative Function-chain success/error/drop.

Checks passed: `RUSTC_WRAPPER= cargo test -p yu-types --lib indexed_ --
--test-threads=1` (13), `RUSTC_WRAPPER= cargo test -p yu-types --lib --
--test-threads=1` (28), `RUSTC_WRAPPER= cargo check -p yu-types --tests
--message-format short`, `cargo fmt --all --check`, and `git diff --check`.
No benchmark or §15 probe ran; the measurement budget remains zero.

This closes only the non-shipping `yu-types` indexed-finalizer gate. Production
still uses the boxed path. Before any resource probe, complete the solver-side
physical-lane and same-time peak reconciliation in existing owners, including
the `non_generic_closure` temporary sets/frontier and raw-incidence sets, then
obtain independent review of the fresh §15 plan. Producer incidence admission,
numeric support boundary, production cutover, §44 closure, F5e acceptance, and
overall F5c completion remain open. No user decision arose in this slice.

### Previous continuation (2026-09-26): end-to-end callback and Q/R parity

The selected FlatDraft candidate now has a paired root-forest witness with two
raw recursive owners. The fixture contains a prewarmed Shared occurrence
repeated in the predicate roots and a negative-polarity Shared row first
encountered in a later bound. It compares the complete callback sequence and
polarity with the boxed materializer, compares Shared-hit counts separately,
and checks Q/R maps and ordinals, normalized structure, and all five
normalization counters.

The same raw bound entries are inserted in both owner orders while the explicit
root-owner order stays fixed. Both variants produce identical callback traces,
hit counts, and Q/R assignments. Test-only capture is at the existing
materialization callback site; the producer algorithm and production path do
not change.

M1 spec-auditor review found the first witness used only one owner and could not
cover the approved map-order invariant. The repaired two-owner fixture closes
that finding. Checks passed: `RUSTC_WRAPPER= cargo test -p yu-solver --lib
selected_flat_candidate_matches_boxed_q_r_and_normalization_counters
-- --test-threads=1` (1), `RUSTC_WRAPPER= cargo check -p yu-solver --tests
--message-format short`, `cargo fmt --all --check`, and `git diff --check`. No
broader suite or measurement ran.

The bounded non-shipping FlatDraft producer/normalizer fixture gate now closes,
including end-to-end callback/Q/R parity. The next implementation gate is the
already-approved `yu-types` indexed finalizer (§3); the existing producer
fixture supplies its bounded flat-input evidence. Before any resource probe,
the candidate still needs complete physical-lane reconciliation, including
`non_generic_closure` temporary sets/frontier, raw-incidence sets, failed
reserve observations, and the solver/finalizer simultaneous peak, followed by
the independently reviewed §15 plan and campaign. A static source audit found
these accounting gaps; no probe ran. Keep accounting in the existing owners
and families. Production remains boxed; no numeric support boundary,
production cutover, §44 closure, F5e acceptance, or overall F5c completion is
authorized by this slice.

### Latest continuation (2026-09-26): selected FlatDraft substitution and normalization

The shared post-convergence selector now feeds the test-only FlatDraft
substitution and selected-root normalization stages. Recursive bounds are
assembled in R-owner order; substitution applies R, then Q, then
polarity-specific elimination. The normalizer processes the selected predicate
and bounds, and a paired fixture matches boxed structure, Q/R assignment, and
all five normalization counters. Orphan Variable scratch is absent from the
normalized result.

The component memo transaction remains open through substitution,
normalization, and normalized-output capacity observation. The late failure
witness checks persistent memo restoration, idle lanes, and warm retry.
Successful output stays retained and capacity-accounted until explicit release.

The candidate tracks requested slots in 27 observer lanes: 13 normalizer
lanes, eight additional scratch lanes, and six emitted-output lanes. Their
counters merge atomically and contribute to the aggregate. Publishing the same
six output vectors records retained capacity without counting their requests
again. M2 compiler-referee review found no semantic or rollback issue. The
performance requested-slot gap and duplicate-publication count are closed by
the implementation repair and primary diff review.

Checks passed: RUSTC_WRAPPER= cargo test -p yu-solver --lib selected_flat_ --
--test-threads=1 (5); RUSTC_WRAPPER= cargo test -p yu-solver --lib flat_tests
-- --test-threads=1 (15); RUSTC_WRAPPER= cargo check -p yu-solver --tests
--message-format short; cargo fmt --all --check; git diff --check. No broad
suite, benchmark, resource probe, or §15 measurement ran.

This closes substitution and normalization composition only. Full callback/Q/R
parity, remaining physical resource reconciliation, the reviewed §15
measurement plan, indexed finalization, and production cutover remain open.
Production remains boxed; no numeric support boundary, §44 closure, F5e
acceptance, or overall F5c completion is authorized by this slice.

### Latest continuation (2026-09-26): shared post-convergence R/Q assembly

Boxed production and the test-only FlatDraft path now share post-convergence
retained-bound replay, guarded-bound and trace survival, recursive-owner
ordering, retained occurrence traversal, and Q/R ordinal assignment. Replay and
guard checks follow `raw_owner_order`; R follows the first surviving trace for
each owner; Q follows the retained predicate, then recursive owners in R order
with lower before upper. No set/map iteration chooses output ordinals.

The FlatDraft candidate uses fallible growth and distinct physical lanes for
the retained owner bounds, survivor sets, recursive owner order/set, occurrence
order/seen set, and Q/R maps. Temporary lanes release after their collections
drop; selected lanes remain live with replay output and raw forest until the
candidate wrapper releases or aborts them. A paired witness distinguishes raw
owner order `[1,2]` from trace order `[2,1,2]`, checks duplicate-trace removal,
predicate/lower/upper Q order and R offsets, and rejects a missing raw owner.
The rollback witness injects failure after R convergence and after post-R bound
output, then checks memo restoration, all output/post-R lane releases, idle
scratch, and warm retry.

M3 compiler-referee, spec-auditor, and performance-auditor delta reviews found
no remaining actionable issue. `cargo test -p yu-solver --lib post_r_ --
--test-threads=1` passes (4); `cargo test -p yu-solver --lib
f5c_tree_analysis -- --test-threads=1` passes (4); solver test-target check,
formatting, and diff checks pass. No broad suite, resource probe, or §15
measurement ran; measurement budget remains zero.

Only post-convergence retained-R and Q/R assembly is shared. Flat substitution
and normalization integration, full callback/Q/R parity, rollback through all
later fallible stages, §5 resource certification, and the reviewed §15
measurement gate remain open. Production remains boxed; no numeric resource
boundary, production cutover, §44 closure, F5e acceptance, or overall F5c
completion is authorized by this implementation slice.

### Latest continuation (2026-09-26): shared R fixed-point slice

Boxed production and the test-only FlatDraft adapter now use one R-candidate
fixed-point loop for eligibility, guarded-bound replay, trace pruning,
predicate replay, raw-bound reachability, and convergence. Production remains
boxed. The FlatDraft raw-forest wrapper owns the live memo transaction and
aborts it on R failure. Its failure witness completes a replay that emitted
nodes, fails on the next replay, compares persistent memo state, checks idle
scratch and monotonic work, then retries a warm lookup.

Replay charges source-wide active-array initialization before allocating, and
accounts both active arrays plus all five retained replay-output lanes while
source, memo, and forest remain live. It drops output before releasing those
lanes; direct replay fixtures follow the same lifecycle.

M3 compiler-referee/spec-auditor/performance delta reviews found no blocker or
major issue. Two minor evidence/lifecycle points were closed with additional
lane assertions and drop-order cleanup. Focused checks pass: flat-walker tests
(25), replay tests (6), generalization-transaction tests (11), the composed
replay/substitution/normalization witness (1), solver lib/test-target checks,
formatting, and diff checks. No broad suite or resource measurement ran;
measurement budget remains zero.

Only the R fixed-point loop is shared. Post-convergence retained-R assembly,
Q/R ordinal assignment, flat substitution/normalization integration, full
callback/Q/R parity, and rollback through those later fallible stages remain
open. Next: carry the same boxed ordering through retained-R assembly and Q/R
ordinal assignment while retaining the candidate memo transaction through
all later fallible stages. Production remains boxed; no resource probe,
numeric boundary, §44 closure, F5e acceptance, or overall F5c completion is
authorized.

### Latest continuation (2026-09-26): shared raw-incidence census slice

Boxed `build_inner` and the test-only FlatDraft raw forest now call one
predicate-first incidence census through the existing Walker event scheduler.
Both visit raw owners in declared order and lower before upper; the existing
raw-bound-owner charge stays at the same point. An exact-set parity witness
covers predicate roots, two ordered owners, both polarities, and guarded
Function edges. A warm Shared callback remains covered by the separate raw
forest fixture because FlatDraft has no Shared node form.

M3 compiler-referee/spec-auditor/performance delta reviews found no blocker or
major issue. The minor parity-evidence gap closed with the focused exact-set
witness and primary diff review. Nine focused raw-forest tests, solver library
and test-target checks, formatting, and diff checks pass. No broad suite or
measurement ran; performance measurement budget remains zero.

This shares only the pre-pruning incidence census. R fixed-point filtering,
retained occurrence order, Q/R binder assignment, flat replay/substitution/
normalization, full callback/Q/R parity, and rollback after an actual later
stage remain open. Next: carry the single shared core through the R and Q
ordering loops while keeping the candidate memo transaction open through all
fallible stages. Production remains boxed.

### Latest continuation (2026-09-26): raw-forest memo transaction precursor

The test-only ordered raw-forest builder now keeps its memo root transaction
open after materialization. Releasing the forest commits it; aborting drops
the candidate output lanes and rolls back root admissions/invalidations and
appended memo nodes. Any root/node rollback error poisons the candidate
generalizer at the shared rollback owner, and both flat candidate entrypoints
reject reuse. A warm-root witness compares persistent root, edge, node,
reverse-parent, and incidence lanes after invalidation/re-admission and abort,
checks idle transient state, and retries the same forest. Separate witnesses
cover rollback failure from explicit abort and raw-forest construction.

M2 compiler-referee and spec-auditor delta reviews closed after repairs.
Focused raw-forest tests (8), solver library and test-target checks, formatting,
and diff checks pass. No broad suite, benchmark, or §15 resource probe ran.
This proves rollback only at the raw-forest boundary: the builder is not yet
connected to the shared Q/R/replay/substitution/normalization path, so actual
later-stage failure rollback and full callback/Q/R parity remain open.
Production remains boxed.

Next: factor the existing boxed incidence/Q/R algorithm over boxed and
FlatDraft operations without duplicating its ordering or work accounting, then
keep the candidate memo transaction open through every fallible downstream
stage. No production cutover, numeric resource boundary, §44 closure, F5e
acceptance, or overall F5c completion is authorized.

### Latest continuation (2026-09-26): FlatDraft tree-analysis adapter

The existing explicit-stack tree-analysis walker now accepts test-only
FlatDraft IDs through the same event scheduler used by boxed values. New
witnesses compare full `(owner, polarity, guarded)` event traces for repeated
positive and negative child IDs, early exits, incidence/reference/first-
occurrence results, and guarded-bound results. Invalid IDs and child spans
return `IdentityExhausted`, clear pending tasks, and permit retry; repeated
edge work charges match the boxed path exactly.

The M1 `spec_auditor` delta review closed after repairing trace multiplicity,
malformed-input, cleanup, and work-charge gaps. Focused analysis and 4,096-deep
small-stack checks pass, solver test targets compile, and format/diff checks
pass. A separate compile-fix commit restored non-test `yu-solver` library
compilation for the already-approved candidate helpers. No broad suite or
resource probe ran. Production remains boxed.

Next: share the existing boxed incidence/Q/R orchestration with FlatDraft
roots, keep the component memo transaction open through replay, Q/R assignment,
substitution, and normalization, and add full callback/Q/R parity plus late
failure rollback evidence. The candidate remains test-only; no production
cutover, numeric resource limit, §15 measurement, §44 closure, F5e acceptance,
or overall F5c completion is authorized.

### Latest continuation (2026-09-26): candidate flat sink over shared walker

An uncalled `F5cFlatWalkSink` now uses the same `walk_with` task interpreter
as the boxed compatibility sink. Its source arena is owned by the
generalizer, so Local IDs remain live across successive walks; no API can
commit/release the arena before a future full-forest materialization boundary.
The candidate implements polarity-tagged Local/Shared equality, ordered first
survivors, cacheability propagation, Function construction, and
child-before-parent promotion into existing memo lanes. Candidate failures
roll back memo roots/nodes and source lengths, restore result counters, and
retain solve-wide work charges. A same-time promotion witness accounts for
memo, source, and both promotion worklists; reverse-parent construction no
longer clones child IDs into an untracked temporary vector.

M2 compiler-referee/performance delta reviews converged after repairs. Focused
checks pass: `cargo fmt --check`, `cargo test -p yu-solver --lib
f5c_flat_walk_sink -- --test-threads=1` (13), `cargo check -p yu-solver
--tests`, and `git diff --check`. No benchmark or §15 probe ran.

This is not the complete flat candidate gate. The candidate remains
test-only; ordered whole-component predicate/bounds orchestration,
Local/Shared-to-FlatDraft materialization, complete callback and Q/R parity,
FlatDraft co-resident accounting, and overall §5 witness closure remain next.
Production stays boxed; no production cutover, numeric resource limit, §44
closure, F5e acceptance, or overall F5c completion is authorized.

### Latest continuation (2026-09-26): checked Shared-to-FlatDraft materializer

Added a candidate-only iterative Shared-summary occurrence materializer with
a fallible incidence callback and transactional rollback of all six
FlatDraft lanes. It preserves child and Function order, expands repeated
Shared occurrences separately, pre-reserves and accounts task/value plus all
FlatDraft lanes using exact element sizes, and observes simultaneous live
source/memo/draft/scratch capacity. Union/Intersection drain work is charged
before moving any child; positive and negative overflow witnesses verify no
partial move and retry.

M2 spec/performance delta review found no remaining blocker. Focused checks
passed: the `f5c_materialization::` filter (17), the flat sink filter (14),
the co-resident materializer witness, `cargo check -p yu-solver --tests`,
formatting, and diff checks. No benchmark or §15 probe ran.

This helper covers Shared materialization only. The test-only Local/Shared raw
forest builder, source Local materialization, ordered owner-bound append,
whole-component draft/memo rollback, callback/Q/R parity, and final
source/memo/FlatDraft lifecycle remain open.

### Latest continuation (2026-09-26): checked Local/Shared batch materializer

Added an iterative, candidate-only materializer for ordered Local and Shared
roots. Local Functions, Unions, and Intersections preserve child order and
polarity; Shared occurrences reuse the checked summary expansion path. A batch
failure restores all six FlatDraft lengths and the caller's root-output length,
while retaining the source arena and monotonic work charges. New task/value/root
lanes account exact element sizes; an output vector's capacity stays accounted
until the caller drops it and calls the documented release method, including
for an empty batch with preallocated capacity.

M2 spec/performance delta reviews found no remaining blocker after the output
lane lifecycle repair. The focused materialization tests passed (3), solver
test targets compile, and fmt/diff checks pass. No benchmark or §15 probe ran.
The ordered whole-component root forest, callback/Q/R parity, component-wide
memo rollback, and production cutover remain open; production stays boxed.

### Latest continuation (2026-09-26): test-only ordered raw forest

Added a non-production `F5cGeneralizer` path that gathers the predicate first,
then unique reentry owners in encounter order with lower before upper bounds
and the existing Bottom/Top defaults. It retains tagged roots through every
walk, rejects invalid effects before the single ordered materialization batch,
and returns raw source-owner IDs separately from final binder ordinals. Five
tracked lanes cover owner order, bounds, seen owners, raw roots, and Shared
callback trace. Checked callback accounting receives the current memo and
capacity context so trace growth joins the simultaneous source/memo/draft/
scratch observation.

The candidate limits one returned forest at a time; releasing it advances memo
checkpoints and resets producer state. Failure/retry witnesses cover callback
and table-counter overflow, plus a successful forest followed by a later
failure while retaining an earlier warm memo root. M2 spec-auditor and
compiler-referee delta reviews found no remaining defect after two focused
repairs. Verification passed: flat sink tests (19), materialization tests
(17), `cargo check -p yu-solver --tests`, `cargo fmt --check`, and
`git diff --check`. No benchmark or §15 probe ran.

This closes only the raw predicate/bounds materialization subgate. Complete
boxed-versus-flat callback and Q/R ordinal parity, direct invalid-effect timing
witness, downstream memo rollback through Q/R, indexed FlatDraft analysis,
production cutover, and remaining §5 witnesses stay open; production remains
boxed. Immediate next: map the existing boxed incidence/Q/R traversal onto
FlatDraft IDs without a duplicate algorithm, then test full callback/Q/R order
parity while retaining the component memo transaction through all later
fallible stages.

### Latest continuation (2026-09-26): explicit raw reentry-owner order

The boxed producer now retains first-encounter order for unique raw reentry
owners and uses it for recursive-bound materialization and the pre-pruning
incidence census. The owner-keyed bounds map is lookup-only; materialization
visits predicate first, then owners in encounter order, lower before upper.
The new owner-order lane charges checked logical work, reserves fallibly before
mutation, and participates in simultaneous and independent retained/peak
capacity accounting. A reserve-failure witness verifies component rollback and
successful retry.

The helper-level test verifies lower/upper callback ordering is independent of
map insertion order. The complete producer callback/Q/R witness with a warm
Shared predicate and a row first encountered in a later bound remains open for
the flat raw-forest candidate gate. M1 `spec_auditor` review and its focused
delta review found no remaining issue. Focused checks passed: materialization
tests (12), the owner-order and rollback/reserve tests, `cargo fmt --check`,
and `git diff --check`. No broad library suite, benchmark, or §15 probe ran.

Next: add the boxed compatibility sink behind the single shared task
interpreter, then implement the uncalled tagged flat sink and ordered raw-root
forest. Production cutover, resource probing, numeric limits, indexed
finalization, §44 rollback, F5e, and overall F5c closure remain open.

### Latest continuation (2026-09-26): fallible sink constructors

The five value-construction methods on `F5cWalkSink` now return
`Result<Value, SolveAvailabilityError>`, and the shared interpreter
propagates errors through its existing cleanup and component rollback path.
The boxed sink returns the same previous values inside `Ok`; task ordering and
work charges are unchanged. M1 `compiler_referee` delta review found no issue.
`cargo fmt --check`, `cargo check -p yu-solver --lib`, and `git diff --check`
passed. No test was added because the boxed sink cannot produce a constructor
error; the flat sink's injected growth-failure witnesses remain required.

Next: build the checked Local/Shared source arena and its promotion/materialize
bridge, then connect it through `walk_with` and the ordered forest. This
interface preparation does not close the flat-sink gate.

### Latest continuation (2026-09-26): sink construction context

The five `F5cWalkSink` value constructors now receive mutable generalizer
context so a future flat sink can charge source creation and reserve/account
its own lanes at construction. `cacheable` remains value-only. The boxed sink
ignores the context and creates the same values; the M1 `spec_auditor` delta
review found no issue. `cargo check -q -p yu-solver` and `git diff --check`
passed. The candidate sink must still respect the design's sink ownership and
component rollback boundaries; no flat arena or runtime behavior was added.

Next: add the checked tagged source arena with explicit node/edge lanes and
independent accounting, then connect those operations to the sink.

### Latest continuation (2026-09-26): tagged flat source arena substrate

A non-production source arena now stores polarity-specific Local IDs and
Shared summary IDs, scalar/Function nodes, and ordered tagged child spans in
four flat lanes. It stores no recursive boxes or child vectors. Append checks
IDs and spans, reserves all needed lanes, charges solve-wide work, and only
then publishes nodes/edges. Rollback truncates every lane; release drops the
lanes and resets live capacity. The four capacities are included in the
walker ledger and simultaneous memo peak.

The independent spec and performance audits found no blocking issue. Four
focused tests cover tags/order/Functions, overflow/no-publication, partial
reserve failure, and rollback. `cargo test -p yu-solver --lib
flat_source_arena -- --test-threads=1`, `cargo check -p yu-solver --lib`,
`cargo fmt --check`, and `git diff --check` passed. The arena remains uncalled
by the walker; sink construction, Local structural comparison/dedup,
child-before-parent memo promotion, the full raw forest, and source/memo/draft
co-resident peak evidence remain open.

Next: implement Local/Shared sink semantics on this substrate, first closing
structural equality/dedup and promotion without production cutover.

### Latest continuation (2026-09-26): boxed sink on shared interpreter

The existing producer task machine now runs through one generic
`walk_with<S: F5cWalkSink>` interpreter. `F5cBoxedWalkSink` contains the former
boxed construction, first-seen deduplication, structural comparison, and memo
promotion operations. Existing `walk` wrappers and all production callers still
select this boxed sink. The generic Values lane records the concrete value
slot size for capacity accounting. No flat sink or candidate raw-root forest
is present yet.

M2 `spec_auditor` and `performance_auditor` reviews found no confirmed defect
in this intermediate extraction. Static dispatch and existing allocation
shape remain; optimized code size and successful-path timing are unmeasured
and remain under the reviewed §15 plan. Focused checks passed: `cargo fmt`,
`cargo check -p yu-solver --lib`, the generalization filter (17), the F5c
filter (209 passed, 1 ignored), and `git diff --check`.

Next: add the uncalled tagged flat sink and keep source Local/Shared references
alive across the full ordered predicate/bounds forest. The full callback/Q/R
witness and candidate parity/rollback gates remain open. No production
cutover, resource probe, numeric boundary, §44 closure, F5e acceptance, or
overall F5c completion is authorized.

### Latest continuation (2026-09-26): solve-wide checked work-meter subgate

Added a session-owned checked logical-work meter and threaded it through the
F5c producer, memo, analysis, materialization, replay, and substitution work
that is currently exercised by the boxed route and flat candidates. It counts
repeatable logical operations; it has no selected numeric limit and is not a
physical allocation/peak-capacity ledger. Checked arithmetic failure returns
`IdentityExhausted` instead of wrapping. The solve-wide total deliberately
persists across failed component attempts because attempted work still
happened, while each component memo's own published state continues to roll
back transactionally.

Overflow witnesses cover scheduling before boxed output construction, owner
ordering, and all five boxed finish/drain owner families in both polarities;
they verify no construction/drain past the rejected charge and successful
retry. M2 compiler/specification/performance review convergence found no open
blocking finding after repairs. `lib.rs` only contains session wiring and test
registration; accounting remains in owning F5c modules.

Focused checks pass: the work-meter filter (15), the F5c filter (207 passed,
1 ignored), `cargo check -p yu-solver --lib` without warnings,
`cargo fmt --check`, and `git diff --check`. The single-threaded
no-default-feature `yu-solver` library suite passed (292 passed, 1 ignored;
952.91 seconds). No benchmark or §15 resource probe ran; measurement budget
remains zero. This closes only the logical repeat-work accounting
prerequisite. It does not bound depth, allocations, capacity, or wall time and
does not certify physical peak resources. Next: checkpoint this subgate, then
continue the uncalled flat sink through the shared walker.
Production cutover, §15 measurement, indexed finalization, remaining §44
rollback, F5e, and overall F5c/F5e closure remain open.

### Latest continuation (2026-09-26): memo rollback gate closed

The approved producer-owner move and memo transaction/active-state rollback
gate are complete. In `f5c_generalization.rs`, persistent root admissions and
invalidations now share one chronological undo log; rollback replays it in
reverse and resets transient active/conflict/work/visit scratch to idle before
truncating appended nodes. A failed child-lane reserve is propagated before
append, while any capacity it actually retained is still charged. Same-time
capacity samples now include the live generalizer mirror lanes, and the
independent test ledger folds those samples rather than trusting the production
peak scalar.

Preserved behavior: the boxed producer remains the only production sink;
summary sharing, root order, Q/R, scheme results, and public routing are
unchanged. `lib.rs` still owns outer orchestration/resource aggregation; the
transaction tests live in `src/tests/f5c_generalization_transactions.rs`.
Latest M2 compiler-referee and performance-auditor delta review found no
blocking or major issue.

Verification passed: `cargo fmt --check`; `cargo test -p yu-solver --lib f5c_
-- --test-threads=1` (192 passed, 1 ignored); and
`cargo test -p yu-solver --lib --no-default-features -- --test-threads=1`
(277 passed, 1 ignored; 717.77 seconds). No benchmark or resource probe ran;
measurement budget remains zero. Next is the uncalled flat sink sharing the
real producer walker. Production cutover, §15 measurement, indexed
finalization, remaining §44 route atomicity, F5e, and overall F5c/F5e closure
remain open.

### Previous continuation (2026-09-26): shared producer owner moved

The current `F5cGeneralizer::walk` owns the producer task decisions but returns
boxed `F5cPositive` / `F5cNegative` values, so an isolated flat sink cannot
emit IDs at leaf/exit tasks without copying the walker. A focused M3 proposal
now puts the F5c generalizer, summary memo/transaction, ordered raw-root
coordination, and shared walker under `f5c_generalization.rs`; `lib.rs` keeps
component invocation and solver/fact installation orchestration. The boxed
sink remains the current production path; the tagged Local/Shared flat sink
remains uncalled.

Three M3 reviewers converged after two focused design-repair rounds. They
closed rollback interleavings (including active-conflict scratch restoration),
raw-root order, complete raw-forest/effect witnesses, and module/resource
accounting. The user approved staged internal implementation on 2026-09-26.

The first slice moved the boxed F5c generalizer, component memo/transaction,
walker, and `build_inner` into `f5c_generalization.rs`; `lib.rs` retains
component draft invocation and outer orchestration. Production callers and
behavior are unchanged, the boxed path remains active, and the flat sink is
uncalled. M2 `spec_auditor` review found one minor visibility issue; the primary
made unused epoch/checkpoint/walker-state fields private. M2
`regression_auditor` found no issue.

Focused checks pass: `cargo fmt --check`, `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (183 passed, 1
ignored), and `git diff --check`. No workspace-wide suite, benchmark, or
resource probe ran. The next active slice is memo transaction/active-state
rollback repair with focused failure witnesses. The §15 resource plan remains
required before any resource probe. Indexed finalization, F5e, §44 rollback,
and overall F5c/F5e closure remain open.

### Latest continuation (2026-09-26): pre-replay producer roots into FlatDraft

A new shallow guarded-self fixture follows the real `F5cGeneralizer` pre-replay
path: predicate root, dynamically discovered reentry owners, lower/upper
expansion, and Bottom/Top defaults for absent sides. It materializes the raw
predicate and recursive-bound endpoints through the boxed path, then encodes
those complete roots into one `FlatDraft`, including its predicate and
owner-ordered bound root fields.

The test compares every root structurally against both the boxed summary
materializer and the pre-replay boxed tree, preserving polarity, Function
fields/effects, and ordered members. It also compares complete incidence
callback sequences. A nested positive row must be an admitted `Shared` ID
referenced exactly once in both predicate and lower roots, and produce one
matching incidence mark. The flat draft stores source owner ordinals; it stops
before replay, Q/R substitution, normalization, and finalization. This is a
boxed-to-summary-to-flat bridge, not yet direct flat construction from solver
tasks. `lib.rs` remains unchanged.

Compiler-referee review confirmed the owner/default path and found a minor gap
in proving that the nested summary was actually referenced. The fixture now
checks the exact Shared-ID occurrence and incidence count and wires all roots
into the FlatDraft. `cargo test -p yu-solver --lib f5c_materialization:: --
--test-threads=1` passed (9), with `cargo fmt --check` and `git diff --check`.
No broad library suite, benchmark, or resource probe ran; measurement budget
remains zero.

Next: do a code-level design review for an uncalled, module-local flat sink
that shares actual producer traversal and emits flat IDs at leaf/exit tasks,
carrying cacheability metadata. Do not copy the walker or refactor the active
boxed sink before the interface is understood. Preserve active-state taint,
memo admission, reentry discovery, owner order, incidence, and append/state
rollback. If this requires changing the active production path, stop for
independent M3 review and explicit user approval. Resource probing remains
behind reviewed §15. §7/§15, indexed finalization, F5e, §44 rollback, and
F5c/F5e closure remain open.

### Previous continuation (2026-09-26): actual F5c producer memo bridge

The composed fixture's source now uses `F5cComponentExpansionMemo::positive_node`
and `negative_node` instead of directly filling summary node arrays. Repeated
`Shared` references still become distinct flat occurrence IDs, then replay,
substitution, and normalization remain checked against the boxed oracle.

A separate module-owned fixture now drives `F5cGeneralizer::positive_row` and
`negative_row` to produce real cached summary roots for a pure Function with
both polarities. It materializes those memo roots into flat drafts and compares
them before downstream transforms with boxed `positive_value_with` /
`negative_value_with`. The complete incidence callback sequences must match in
order, and a separate explicit-worklist comparison checks polarity, fields,
effects, and ordered Union/Intersection members. Scope is deliberately narrow:
these are internal memo roots, not the complete `build_component` draft or
finalized scheme. The parity helper is for shallow fixtures and does not certify
ordinary deep boxed-value drop safety. No `lib.rs` edit was needed.

M1 compiler-referee review found incomplete internal incidence coverage and a
deep-drop caveat; both were addressed, and fresh spec-auditor delta review was
clean. Verification: `cargo test -p yu-solver --lib f5c_materialization:: --
--test-threads=1` passed (8), along with `cargo fmt --check` and
`git diff --check`. No broad library suite, benchmark, or resource probe ran;
measurement budget remains zero.

Next: extend the non-shipping source bridge toward full producer predicate and
bound roots without routing through boxed `GeneralizationDraft`. Keep `lib.rs`
orchestration-only, production callers unchanged, and resource probing behind
the separately reviewed §15 plan. §7/§15, indexed finalization, F5e, §44
rollback, and F5c/F5e closure remain open.

### Previous continuation (2026-09-26): summary-to-flat composed fixture

The composed fixture now starts from a synthetic `F5cSummaryNode` DAG and
materializes predicate, lower-bound, and upper-bound roots with
`materialize_summary_flat` before flat replay, substitution, and normalization.
Before downstream processing, each materialized root is expanded and compared
directly with the summary memo's boxed positive/negative value. The DAG repeats
edges in both polarities; checks confirm those occurrences initially receive
distinct flat IDs. The final scheme and normalization counters still match the
boxed oracle, with all normalized nodes/child entries reachable, dense IDs,
duplicate removal, and shared canonical R1 IDs across roots.

M2 spec-auditor review found no issue. Compiler-referee review caught a test
gap: parity only after replay/substitution could hide a root-variable
misassociation. The fixture now checks all three raw materialized roots against
the boxed summary values before replay; focused delta review closed the finding.
The prior normalizer repair remains one O(N) representative pass reusing
`sort_scratch`, with no new allocation. This is candidate-fixture evidence,
not resource evidence or production integration.

Verification: the focused composed test passed; `flat_tests` passed (10);
`cargo check -p yu-solver --tests --message-format short`, `cargo fmt --check`,
and `git diff --check` passed. No broad suite, benchmark, or resource probe
ran; measurement budget remains zero.

Next: continue the producer/downstream candidate bridge and keep every source
root checked against the boxed oracle before lossy replay/substitution. Keep
production callers unchanged; inspect §15 before any resource probe. Indexed
finalization, §5/§15 certification, F5e, §44 rollback, and F5c/F5e closure
remain open.

### Previous continuation (2026-09-26): composed flat downstream pipeline

The fixture-only pipeline now composes `replay_flat` for predicate/lower/upper
roots, `substitute_flat`, and `normalize_flat`, then compares scheme fields
and all five normalization counters with the boxed oracle. It checks repeated
source edges have distinct IDs before normalization; Q2→Q0, R3→R1, and
polarity-specific substitution elimination; every normalized node/child entry
is reachable from retained roots; and duplicate members collapse while
canonical R1 nodes share IDs across roots.

The composition exposed a real candidate issue: equal normalized `(height,
rank)` keys were rebuilt as separate flat output nodes. The normalizer now
reuses an already allocated sort-scratch vector for a representative lookup
and remaps equal keys to one output ID across roots. This adds one O(N) pass
without new allocation. The older selected-root fixture now expects this
canonical sharing. M2 compiler/performance review found no actionable delta.

Verification: `cargo test -p yu-solver --lib flat_tests --
--test-threads=1` passed (10); `cargo test -p yu-solver --lib f5c_replay --
--test-threads=1` passed (6); `cargo test -p yu-solver --lib
f5c_binder_substitution -- --test-threads=1` passed (7). `cargo check -p
yu-solver --tests --message-format short`, `cargo fmt --check`, and
`git diff --check` passed. No measurement ran; the broad suite remains
unverified.

Next: compose flat summary materialization with this pipeline. Keep production
callers unchanged until the required design/resource gates; review §15 before
any resource probe. Indexed finalization, §5/§15 certification, F5e, §44, and
F5c/F5e closure remain open.

### Previous continuation (2026-09-26): fixture-only flat replay candidate

Added uncalled `replay_flat` in `crates/yu-solver/src/f5c_replay.rs`, with
tests in the matching replay module. The immutable source supports repeated
candidate-mask runs; explicit work/finish/leave tasks preserve polarity and
child order, copy each occurrence of shared edges, and reject reachable
cycles. Failure truncates every appended node/child/order lane. Both root
polarities match boxed replay on the fixture, including repeated-edge
occurrences and polarity elimination. A reachable positive↔negative Function
cycle after a completed child Union verifies restoration of every FlatDraft
field. A 4,096-deep replay passes on a 64 KiB thread stack. `lib.rs` and
production callers remain unchanged.

M2 compiler/performance delta reviews closed the fixture-local test findings;
no blocker remains for this disconnected candidate. Production resource gates
remain open: each invocation initializes source-sized active arrays, shared
DAG occurrence expansion may be exponential and repeats across masks, task /
value counters omit active-array and output-draft growth, and truncation keeps
capacity. These costs must enter §5 admission and §15 peak evidence before
wiring; no benchmark or numeric boundary was selected.

Verification: `cargo test -p yu-solver --lib f5c_flat_replay --
--test-threads=1` passed (4); the complete `f5c_replay` filter passed (6);
`cargo fmt --check` and `git diff --check` passed. Measurement budget used is
zero; the broad suite remains unverified.

Next: compose replay with flat substitution and selected-root normalization
against the boxed oracle before production wiring. Continue in module-owned
slices; do not claim completion of the first §7 producer gate, §5/§15, indexed
finalization, production acceptance, F5c/F5e, or §44 rollback.

### Previous continuation (2026-09-26): selected-root normalization handoff

`normalize_flat` now accepts the composed fixture-only flat substitution
candidate without admitting unreachable raw Variable scratch into canonical
ranking. It seeds the predicate and all recursive-bound endpoints, then uses a
reverse insertion-order pass to mark their topological children in the same
per-polarity maps later used for normalizer IDs. Its forward pass validates all
source insertion IDs and edges, including orphan topology, before skipping
unselected nodes. Reachable Variables still reject. Post-normalization
compaction remains intact; `lib.rs` and production callers are unchanged.

The composed fixture includes a two-member normalized Union, both Function
polarities at bound endpoints, and orphan compound/Variable scratch. It
compares all five logical counters and asserts complete flat output, root, and
bound mappings against the boxed selected-root oracle. Malformed orphan and
selected spans and both Function polarities have focused rejection witnesses.
M2 compiler/performance delta review found no blocking or major issue. The
static successful path is O(N+E+B); its two per-polarity source maps still
scale with all raw nodes, so physical peak and work admission remain open
under §§5/15. The helper remains fixture-only and is not a resource-margin
claim.

Verification: `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` passed
(176 passed, 1 ignored); `cargo test -p yu-solver flat_tests --lib --
--test-threads=1` passed (9); `cargo test -p yu-solver
f5c_binder_substitution --lib -- --test-threads=1` passed (7);
`cargo check -p yu-solver --tests --message-format short`, `cargo fmt --check`,
and `git diff --check` passed. A full single-threaded yu-solver library run
reached the unrelated F4 scale matrices; the 4k bounded-cycle case passed, then
the run was interrupted as the F4 chain matrix began. No earlier failure was
reported; the full suite remains unverified. No benchmark or resource probe
ran; measurement budget used is zero.

Next: add a fixture-only flat replay candidate and compare it with boxed replay
before producer wiring. Keep `lib.rs` orchestration-only and remove old boxed
routes only after parity. The first §7 producer gate, §5/§15 resource gate,
indexed finalizer, production acceptance, F5e Function products, and §44
rollback remain open.

### Previous continuation (2026-09-26): flat binder substitution candidate

Added an uncalled, module-owned `FlatDraft` binder-substitution candidate in
`crates/yu-solver/src/f5c_binder_substitution.rs`; focused tests live in the
matching `tests/` module. It visits the predicate and every retained bound
root iteratively, preflights reachable Variables before mutation, preserves
IDs/spans/root/order metadata, and keeps R → Q → polarity-specific elimination
precedence. It leaves unreachable scratch untouched and does not rebuild boxed
trees. `lib.rs` and production callers are unchanged.

M2 compiler/performance review closed the candidate-local findings after
repair: unmapped orphan Variables no longer reject a selected root forest;
bound-only positive/negative roots are compared with the boxed oracle; shared
nodes are scheduled once; and ID-to-`usize` conversion is checked. The helper
uses per-polarity seen flags and an explicit stack; this is not resource
certification. A remaining integration blocker is concrete: `normalize_flat`
scans all inserted nodes and rejects any raw Variable, including an orphan
left untouched here. Before connecting the helper, isolate/compact the selected
root forest before normalization while preserving boxed-path normalization
counter behavior. Keep the existing post-normalization compaction too.

Verification: `cargo test -p yu-solver f5c_binder_substitution --lib --
--test-threads=1` passed (6); `cargo fmt --check`, `git diff --check`, and
`cargo check -p yu-solver --message-format short` passed without warnings. No
broad suite, scale/resource/capacity probe, or benchmark ran; measurement
budget used is zero. Next: close the selected-root pre-normalization
isolation/normalizer handoff, then continue the producer-side flat migration.
The §5/§15 resource gate, indexed finalizer, production acceptance, F5c/F5e
closure, Function-product behavior, and §44 rollback remain open.

### Current continuation (2026-09-25): flat indexed stack-independent design

The user chose to explore deep F5c support via explicit work stacks rather
than a fixed structural-depth cap. The active design proposal is
[`flat indexed stack-independent F5c draft`](../notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md).
Sol's pre-write architecture report recommends flat solver-owned drafts from
the first deep producer through normalization and error cleanup, paired with
a `yu-types`-owned indexed finalization transaction. Merely making the
finalizer iterative over boxed drafts is insufficient because recursive
success/error destruction and callback-local peak accounting remain.

The earlier architecture portion received M3 review after the initial review
and two focused delta rounds; that review does not certify the later source-map
extension. Its focused review found one blocking and multiple major findings;
the resulting documentation repair passed a fresh focused M3 delta review
with no findings. That review does not certify the full proposal. The user
approved first-stage investigation on
2026-09-25: inspect practical source inputs, map charge sites, and gather
focused scale/resource evidence. The corpus/charge-site audit is recorded in
the design draft and handoff. It found repository-sized surface examples but
no link from source to expanded solver work. The ignored test-only probe now
covers current normalization, shared-summary materialization, and replay. At
shared-DAG depth 12, 13 memo nodes / 24 stored edges materialize to 8,191 nodes
and 8,190 edges; this exposes path expansion but is synthetic, not a practical
input limit. At replay depth 4,096, existing lanes record 12,289 task-slot
requests and 8,193 value-slot requests. The largest normalizer tracked-lane
peak remains 1,972,544 bytes at Function depth 4,096. All these lane bytes
omit some recursively boxed payloads and do not estimate the proposed flat
path.

Static inspection shows replay lanes aggregate repeated replay scheduling.
The R fixed-point candidate set only shrinks, so its loop has at most C+1
rounds for C initial candidates; that is a source proof, not a measurement.
Existing counters do not count its per-round candidate clone/retain work,
owner and trace checks, or reachability-frontier visits. A primary source audit
now maps those operations, direct-bound structural deduplication, summary memo
maintenance, tree analysis, replay/substitution, normalization, and indexed
finalization to explicit logical-work and separate storage-admission units.
It also separates the post-finalization Function product in `closed_parts`
(F5e) and §44 per-use rollback (separate gate) from the F5c draft meter.

The meter's accumulation lifetime remains unapproved. A read-only architect
consultation and primary adjudication recommend solve-wide accumulation: it
gives a ceiling on charged F5c draft work across components and prevents
component-count bypass, but can reject many individually small components.
Per-component reset admits those workloads but leaves aggregate charged F5c
draft work proportional to component count. Indexed-finalizer-local work, F5e
Function products, §44 per-use routing, and physical peak/storage remain
separately scoped and accounted; this meter caps neither total invocation work
nor peak memory. This recommendation has no numeric cap and is
not an approved durable choice. The second focused M3 delta review accepted
the stale §34 correction and `O(N+W+C)` boundary, then found new BLOCKING/major
omissions in epoch scans, reentry, normalization work, rollback, and peak
evidence. Later repairs addressed the source-map wording; its latest focused
M3 delta review found no blocking, major, or minor issue. Current probes
measure neither the co-resident peak nor repeated R-round work; `C + 1` caps
rounds alone. Restoration allocation and peak remain unverified.
The F5c filter passed 162 tests with the manual probe ignored. The diagnostic
was run seven times (five completed captures, two fixed compile attempts); no
timing or process-memory measurement was taken. No production behavior or API
changed.

The third focused M3 source-map delta round found no new charge-map omission
and accepted the mutation-to-journal visibility gap as an open implementation
requirement. The documentation repair records the current `memo.admit` →
`observe_walker()?` → `admitted_keys` boundary and requires a focused
failure/exhaustion witness. Undo-journal admission is separate from final graph
size; recovery without fallible allocation, invalidation/reinsertion capacity,
and the unmeasured co-resident peak remain open. The follow-up documentation
repair then passed a fresh focused M3 delta review with no blocking, major, or
minor findings; the full design remains a proposal without implementation
authority.

The latest focused M3 review of the separate meter-lifetime recommendation
found major scope and approval-sequencing issues plus a minor wording issue.
The batched repair then passed a fresh focused M3 delta review with no
remaining blocking, major, or minor finding; the minor historical wording was
corrected. The source-map repair's fourth focused review remains clean. A later
full-slice review found one unresolved major gate-sequencing issue; the user
approved solve-wide accumulation for
charged F5c draft work across components on 2026-09-25. This chooses no numeric
cap. At that checkpoint, the next step was to continue the resource subgate
with scale and practical-input evidence; the later full-slice review below
supersedes that next step. A concrete supported boundary still needs focused
independent review and separate user approval before production acceptance.
At that earlier checkpoint, the first-stage investigation authorization
excluded candidate code, API implementation, semantic/support-limit changes,
and F5 clause supersession. The later explicit §15 decision supersedes only the
candidate-code restriction; the semantic scope and production-acceptance gates
remain. Keep `lib.rs` as orchestration and any flat producer/finalizer bridge
in dedicated modules.

Latest full-slice M3 review (2026-09-25) found the resource gate sequence
circular: the draft required numeric support approval before code, but the
actual co-resident physical lane ledger exists only after implementation. The
user approved the recommended non-shipping candidate-before-boundary sequence
on 2026-09-25. This removes the sequencing blocker without selecting numeric
limits or approving production acceptance. Its focused M3 delta review is now
clean: the architect found no issue; one minor historical-authorization wording
issue and one major probe-plan ambiguity were repaired; fresh spec/performance
delta review found no remaining issue. The first fixture-backed flat-
normalization slice is now implemented in `crates/yu-solver/src/f5c_draft.rs`
and `f5c_normalization.rs`; `lib.rs` only adds the module declaration. It
exercises canonical ordering, deduplication, root/bound remapping and
compaction without rebuilding boxed F5c nodes. Focused review closed the ID
mapping and stats-surface defects; specification and performance review accept
this non-shipping slice. The compiler review's isolated-raw-node counter
objection was rejected by primary against §2/§36; fixtures keep the raw graph
rooted before normalization and test only specified post-dedup pruning. This
does not complete §7's first producer-boundary gate: production callers,
replay/substitution/materialization, and error/drop paths still use the
recursive representation.

Verification: `cargo test -p yu-solver flat_tests --lib -- --test-threads=1`
passed (3 tests), `cargo fmt --check` passed, and `git diff --check` passed.
No resource, scale, capacity, or benchmark probe ran; measurement budget used
is zero. `FlatNormalizationStats` is logical-only; physical lane/co-resident
peak reconciliation remains open. Next: continue producer-side flat migration
in module-owned steps, keeping `lib.rs` orchestration-only; complete this first
§7 gate before implementing the `yu-types` indexed transaction. Before the
first candidate resource probe, prepare and review the fresh §15 plan. Numeric
limits, production acceptance, F5c/F5e closure, F5e Function-product behavior,
and §44 route rollback remain open.

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
`a41b9875`. The ownership-only materialization change is verified and pushed
as `992df956`; keep the §24 finalizer callback/API unchanged.

### Previous continuation (2026-09-25): depth-bound probe

The user approved narrowing the compiler's deep-type support envelope and
asked to try a 256-node structural-depth candidate, then reduce unnecessary
code if the bounded path works. A focused raw-draft witness now finalizes and
normally drops positive and negative depth-256 trees on a 512 KiB thread stack.
The same debug witness overflows at 64 KiB and 256 KiB; an optimized release
build passes it at 64 KiB. This makes stack behavior profile/environment
dependent, so an arbitrary-stack guarantee is not established. No production
depth rejection is implemented. The exact stack floor remains an open user
decision: accept the bounded route for ordinary stacks, lower the supported
depth, or retain stack-independent support with a larger iterative rewrite.
See the latest section of the F5c handoff for commands and scope.

Latest continuation (2026-09-24): a primary-only map confirmed that successful
iterative replay, substitution, materialization, and normalization still return
ordinary recursively dropped boxed trees, while checked error exits can drop
partial task/value trees recursively. The component path also calls the
recursive `finalize_generalization_draft_raw` before its normalized drafts are
destroyed. Existing 4,096-deep tests intentionally forget those outputs, so
they prove traversal but not destruction safety. No isolated cleanup helper
was added: a fallible iterative drain would need an approved/accounted
worklist and a safe partial-drain failure contract, and would not bypass the
recursive §24 finalizer. The indexed finalizer remains an unapproved,
not-approval-ready Draft. Exact evidence and the next boundary decision are in
the handoff's “Owned boxed-draft destruction boundary map” section. Do not
claim stack-safe destruction or F5c/F5e closure.

The follow-up audit found callback-local iterative worklists could keep
transaction-branded IDs inside the existing HRTB lifetime and preserve overlay
rollback, but their heap capacity has no exact co-resident accounting path:
F5b freezes solver lanes during the callback and the result checkpoint omits
caller-local scratch. A successful iterative finalizer would also leave the
owned boxed input to recursively drop. No code was added; a reviewed design
decision on joint accounting plus draft destruction is still required.

Latest continuation (2026-09-24): the indexed-finalization Draft now has a
proposal-only property comparison of the current callback, callback-local
worklists, and a `yu-types`-owned indexed transaction. It makes the distinction
explicit: iterative visitation alone does not prevent recursive destruction
of the boxed draft. A source check also found callback-local Q/R handle arrays,
recursive-bound storage, and product-child vectors overlapping the `yu-types`
call; F5b's checkpoint has no joint peak field, and the authority gives no
explicit exclusion for these capacities. This is an accounting question, not
an approved F5b change. The property map is primary-authored and has no
independent review; no code or API changed. See §8 of the indexed-finalization
Draft and the end of the handoff. The earlier choice between preserving §24
and continuing Candidate C was superseded by the user's product direction
below: choose the lightest route preserving Oracle behavior for practical
inputs, with deterministic rejection permitted for pathological inputs.

User direction (2026-09-24): prioritize Oracle-compatible behavior on
practical inputs and a lightweight implementation/success path; deterministic
rejection of pathologically deep, large, or resource-intensive files is
acceptable when basic safety and atomic publication remain intact. This is
recorded in `rules/design-authority.md` and passed a focused independent policy
review. A Sol architect review recommends first testing a bounded current-§24
path instead of the indexed API: enforce a conservative depth limit before
constructing an over-limit boxed tree, and add a work/node budget only if the
source audit requires one. This is provisional, not implementation approval.
The audit must cover all tree-producing/error paths and reconcile the callback-
local allocations identified above. Candidate C remains fallback if the
bounded route cannot meet those conditions cheaply. Immediate next step:
the source audit found recursive finalization/drop of boxed drafts plus possible
repeated shared-summary expansion. A first revised Draft proposed depth 128,
65,536 output commits, and per-lane caps; independent spec/performance review
rejected it as insufficiently owned and pre-enforced. Sol's adjudication now
recommends a narrower partial gate: cap structural depth at 128 before any
over-depth parent is built, keep the §24 callback and boxed representation, and
leave shallow width/shared-summary resource amplification explicitly open.
This is stack-safety progress only, not F5c/F5e resource closure. The earlier
focused M2 spec/performance delta review found no blocking/major findings. A
primary source audit then caught one precision issue: current `Node.height`
gives childless nodes (including an empty product, if present) depth zero. The
first focused spec delta review found one major inconsistency: §3's inductive
safety invariant still applied the nonempty-parent formula to empty products.
The primary repaired it, and a fresh focused spec delta review found no
remaining blocking/major findings; its minor stale-status wording was also
closed. Only explicit user approval of the exact depth/error boundary remains
before implementation.
See
[`F5c bounded boxed-draft gate`](../notes/design/2026-09-24-f5c-bounded-boxed-draft-gate-draft.md)
and the appended handoff section.

§23's ineligible-variable rejection subgate is now reconciled closed for the
represented F5c row sources: eligibility gates both one-sided elimination and
Q/R assignment, the pre-rewrite census rejects remaining unclassified rows,
and binder substitution independently rejects unmapped variables. Tests cover
level-zero and non-generic variables in both polarities plus component failure
without scheme/candidate installation. The full `f5c_` filter passes 161 tests
in default and no-default-feature configurations. This does not close the
remaining F5c/F5e gates; details and exact commands are at the end of the
handoff.

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
accounting remain open. The raw-bound materialization change is pushed in
`992df956`. Preserve §24/F5b; do not implement the unapproved indexed
`yu-types` API.
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
Focused M1 specification delta reviews are clean for these lanes. The later
§3 crosswalk at the end of the handoff reconciles the owner-to-route witness
matrix for the current approved closed-pure Function route set, including the
conditional final-sample overflow case. Live effect-row mutation remains
outside this route set. The full §3 accounting/measurement gate is still open:
the successful-path sampler-cost comparison was invalid and its conservative
process budget is exhausted. The earlier
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

### Active F5c flat-candidate checkpoint (2026-09-25)

The fixture-only `FlatDraft` normalizer checkpoint is followed by a private,
production-unused summary-to-flat materializer in
`crates/yu-solver/src/f5c_materialization.rs`. It uses an explicit worklist,
expands each shared-summary occurrence to preserve existing scheme shape,
incidence order, and normalization counters, and rejects non-topological
summary edges. Raw row Variables are represented explicitly and rejected by
closed normalization until producer substitution resolves them. `lib.rs`
remains unchanged. The independent compiler/performance delta review found no
blocking or major issue in this non-shipping slice; exact fixture parity covers
the boxed materializer and all five logical normalization counters.

This does not close the first §7 producer-boundary gate. Path expansion can be
exponential in the compact summary DAG; flat output, task/value scratch,
normalizer overlap, failure-retained capacities, and solve-wide §5 size/repeat-
work admission still require the separately reviewed §15 measurement gate
before any production call. No numeric threshold, production acceptance, or
F5c/F5e completion is claimed. Immediate next: continue flat producer-side
construction in module-owned slices, keeping `lib.rs` orchestration-only; do
not add a depth cap or run candidate resource probes before the fresh plan is
reviewed.

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
