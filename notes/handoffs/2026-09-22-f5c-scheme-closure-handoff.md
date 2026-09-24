# F5c scheme-closure handoff — 2026-09-23

## Resume point

The approved F5c working set is preserved in checkpoint commit `bb1ec56c` on
`yulang3`. This is a preservation boundary, not F5c gate completion. Check the
current branch status for remote synchronization before resuming; do not treat
the gate as complete.

The latest user decision keeps normalized-union option 1: an incoming closed
positive Union uses its canonical first normalized member as the one public
source-fact representative, while all remaining members are private live
decomposition constraints under the same occurrence cause.

The latest resume point is recorded in the final section of this handoff; that
entry supersedes earlier “next action” text below.

## Latest state and immediate resume (2026-09-23)

The closed-DAG incoming traversal/scratch gate is closed. The last full
`f5c_`-filtered suite passed 93 tests before the two latest route witnesses;
the current `f5c_incoming_` subset passes 31 tests. The per-use reserve audit
added production-route failure witnesses for structured `ExtrusionStack` and Bottom
`RoutedUses`/`RoutedUsePositions`, plus direct in-transaction owner witnesses
for fresh-row `ValueBounds` and `ValueExactUpper`. A specification delta review
found that the first `ValueBounds` witness injected before transaction begin;
the injection now occurs inside the closure immediately before the fresh-row
reserve, and the independent follow-up review passes. Closed pure Function
effects use only `EmptyEffect`/`EffectBottom`; live effect-row mutation lanes
are out of this per-use incoming matrix.

The nested value/effect-bound capacity subgate is closed: incoming growth and
failed-preflight events are journaled, surviving nested capacities are
reconciled after rollback, and dropped fresh-row payload contributes to the
event peak but not retained bytes. The typed-pair/diagnostic subgate is also
implemented and independently reviewed. It covers typed-pair/worklist,
diagnostic edges and scratch, errors/reported-errors, and the corresponding
journal undo buffers. Tests prove distinct normalized Int/Function Union
members, completion of all private members before representative-provenance
failure, failure in the later private member, full logical checkpoint restore,
transient diagnostic-edge growth, diagnostic scratch growth, retained-ledger
reconciliation, and one conditional post-rollback sample.

Fresh value/effect outer-row reserves and extrusion-stack pushes now use the
event-time capacity observer. Incoming-route tests prove sampled post-reserve
outer value-row growth, a later private-member failure with capacity retained
through rollback, and an extrusion-stack growth from zero capacity followed by
post-reserve failure. A test-only exact-lane observer proves the event sample
succeeded before each injected reserve error escaped. Both witnesses assert
complete logical checkpoint restoration, one successful post-rollback sample,
no public route, and retained-byte reconciliation. The first M2 specification
review found the value-row evidence did not distinguish event and final
samples; a focused repair closed it, and fresh spec delta review found no
remaining issue. Live effect-row creation remains unreachable from current
closed-pure Function schemes, so those hooks are not end-to-end proven.

The inference Term owner group is now implemented and independently reviewed.
All six counted Term owners have event snapshots and direct per-owner test-ledger
reconciliation, including lengths, requests, capacities, growths, bytes/peaks,
and active/spare journal transfer. Dedicated post-growth failure witnesses
cover the interned and claimed-page journals, verify event sampling before
rollback, retained spare capacity, and exactly one conditional post-rollback
sample. The consuming-run overflow witness also proves terminal failure without
a `SolvedModule`. The first M2 review's two major findings (missing direct
journal-lane witnesses and aggregate-only/non-independent Term ledger evidence)
were repaired; a fresh spec delta review found no remaining issue.

The full §3 sampling gate remains open. The performance delta review found the
aggregate sampler fixed-size/O(1), but the number of event-time samples is
O(G), where G is the actual capacity-growth count, with no fixed per-route
bound. A bounded successful-path measurement is still required; none has run.
Store/provenance/receipts/routed uses and remaining active/spare journal
ownership transitions still need complete hooks and independent witnesses. Do
not call failed-route resource accounting complete.

The alpha/order and failed-route sampling decisions have since been
adjudicated in the authoritative producer-order addendum recorded in the final
section below. The implementation gates remain open, and the approved
first-member normalized-Union projection remains unchanged. F5c and F5e remain
incomplete.

Immediate continuation: audit the remaining per-use failure-lane witnesses at
the exact changed-capacity event/sample boundary. `TypedWorklist`, `TypedPairs`,
`DiagnosticEdges`, both journal undo-key Vecs (`typed_pair_keys`,
`reported_error_keys`), the `value_row_seen` and `effect_row_seen` setup vectors,
the `RouteMutationJournal.value_rows` undo owner, all four ConstraintStore
lanes, and both routed-use owners now have focused
event/rollback/independent-retained-ledger witnesses.
The store trace distinguishes session-only store bytes from semantic bytes;
rollback preserves exact physical growth/rebuild evidence while logical state
is restored. The M1 review's minor §44 retry-link gap is closed by assertions
for the canonical fact, receipt, provenance, and routed-use records. The
`ValueLevels` witness now independently checks the completed post-rollback
retained/nested totals and peaks. Next consolidate the split `FreshValueBounds`
incoming-route witnesses into exact event/sample, rollback, retained-ledger,
and retry evidence.
Keep live effect-row mutation outside the approved pure-Function scope. The
successful-path sampling attempt consumed its prior process budget without a
valid comparison; do not repeat it without a new budget and an isolating
method. These closures do not close the full sampling/resource gate.

An architect review resolved the stack-safety scratch-accounting phase
boundary: §§14/26/34 authorize private production accounting for root-local
generalizer and walker scratch during F5c, with independent per-lane test-ledger
reconciliation and accurate existing aggregate retained/peak totals. Keep
these lanes distinct from the component memo family. Public
`generalization_scratch_*` accessors and family certification remain F5e; the
separate failed-route sample is authorized only by the later producer-order
addendum. A later implementation added an
iterative positive/negative row and Term walker, iterative summary-node
construction/materialization and structural equality, plus eleven private
walker lanes. Focused coverage includes 1,024 direct rows through ordinary
draft construction, a 2,048-level alternating Function walker/comparison case,
failure/retry, duplicate ordering, and per-lane/aggregate reconciliation. The
focused suite passes 75 tests; package check, formatting, and diff checks pass.
The independent specification delta review is clean for this slice. The
performance delta review keeps the full gate open: recursive guarded-owner,
replay/reference/incidence, normalization/key, and finalizer paths remain;
owned-tree clone/drop are still recursive; transferred Union/Intersection
buffers remain undercounted; and repeated structural dedup needs a bounded
indexed representation.

## Indexed-draft scope check (2026-09-23)

A read-only architect review and a GPT-6 Sol implementer pass checked whether
the indexed arena substrate could be implemented as a bounded production
change. The implementer made no edits: `walk` and component-summary
registration currently produce boxed `F5cPositive`/`F5cNegative` trees, then
`build_inner` immediately materializes and consumes those trees. Rebuilding a
deep boxed tree at that seam would retain the same stack risk; limiting
conversion to shallow values could reject previously accepted inputs.

The implementation must therefore carry indexed IDs across summary
registration and the downstream draft consumers. A follow-up architect review
found that the first useful production slice must continue through
`finalize_generalization_draft_raw`; stopping at `build_inner` would need a
recursive reconstruction for finalization. Two GPT-6 Sol writer attempts made
no code edits: the first confirmed the substrate seam is unusable, and the
second found the iterative finalizer's external frame/value scratch cannot be
combined exactly with closed-finalizer peak storage using the current callback
result alone.

The governing F5b closed-finalization accounting amendment makes this an
authority boundary. Its §9 says to return to design if implementation needs a
cross-crate accounting callback; §6 requires the solver callback to read a
prepared draft without mutating, clearing, or allocating solver-owned lanes.
A `doc(hidden)` hook still changes the exact API in §24. The user must approve
an accounting-boundary addendum before that hook is implemented, or defer the
affected stack-safety gate. Preparing all traversal/index storage before the
callback may avoid the hook, but mapping/handle ownership feasibility remains
unproven. No code or tests changed in these implementation attempts. The
exact-alpha and failed-route sample-boundary choices also remain pending.

The solver-owned callback-slot candidate is rejected: the transaction-scoped
draft IDs cannot safely live in solver storage across the higher-ranked
callback. Candidate B, a `yu-types`-owned indexed operation, is a genuine §24
public API change despite `doc(hidden)` and still requires user approval. Its
first M2 specification and performance reviews found it not ready for approval;
the producer graph/compaction and exact solver-side sample sequence are not
specified. See the later M2 review record below.

## Governing authority

- `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
  §§22, 24, 25, 32, 33, 43, and 44.
- §43 records the approved private closed-extreme Term nodes and zero fresh
  Q/R allocation for structural extremes.
- §44 records the approved normalized-union representative fact and retains
  the requirement that representative publication plus every private member
  constraint be one transactional route operation.
- `tasks/current.md` is navigation only; this handoff is the active resume
  record for the current F5c slice.

## Completed in this slice

`crates/yu-solver/src/term.rs` now has private `PositiveBottom`, `NegativeTop`,
and `NegativeBottom` nodes and the exact corresponding `TermView` variants.
They are structural closed extremes, not fresh live variables.

`crates/yu-solver/src/lib.rs` now includes:

- polarity census and normalized Union/Intersection generalization drafts;
- bipolar Q and guarded self/opposite-polarity R witnesses;
- draft-before-install component publication ordering;
- fresh Q/R incoming substitution and lower-before-upper R restoration;
- one public representative route/fact for a normalized positive Union;
- private member constraints under the source occurrence/cause;
- public-store fact/canonical-key cleanup when representative admission or
  provenance injection fails;
- recursive product expansion through nested positive Union and negative
  Intersection Function children.
- direct iterative incoming traversal of closed value IDs with per-use,
  polarity-specific ordered-part memos; shared closed children are visited
  once per use, and fresh Q rows remain disjoint across uses;
- seven checked instantiation scratch lanes sampled at actual capacity growth,
  with simultaneous session capacities included in independent semantic and
  session peaks;
- physical scratch requests/capacity/retention/peak/growth accounting retained
  across route rollback while logical mutations restore, and transient scratch
  handles released at finish;
- canonical §44 Union-member argument assertions proving the public fact uses
  the normalized first member while each remaining member keeps its private
  decomposition constraint.

The focused F5c coverage includes bipolar census, direct and multiple bounds,
guarded R, finalizer round-trip, normalized-union routing, representative
failure cleanup, nested product instantiation, mixed exact/direct row
expansion, and malformed/dense finalizer ordinal handling.

## Confirmed review state

The post-repair semantic delta review closes the previous nested product
instantiation blocker: positive Function children distribute
negative-argument parts × positive-result parts, and the negative dual does
the same with polarity preserved. The performance delta review found no
material successful-path regression in the localized public-store rollback or
route staging.

The component memo continuation now has reverse parent/incidence/root-edge
indexes, generation-marked active-conflict propagation, admission without a
per-root shared-DAG traversal, and five named resource lanes. A focused real
expansion checks active-ancestor exclusion with an opt-in `cfg(test)` assertion,
so scale tests avoid a repeated test-only DAG walk. Focused witnesses cover active-transition
rollback, more-than-64 row collisions, cold/warm structure, guarded cycles,
same-key invalidation/re-admission restoration, and checked lane overflow.
Failed memo builds now record resource effects before the generalizer's early
error return, independent-ledger updates are transactional, aggregate peaks
use the maximum simultaneous retained total, and later sequential-reserve
failure effects remain physically accounted while logical state rolls back.
Independent M3 resource/spec review is clean. Admission no longer revisits
shared DAGs per cached root, but the component gate remains open because row
and Term expansion, summary conversion, normalization, and owned-tree
operations remain stack-bound.

The earlier specification blocker about private live-state restoration during
normalized-Union route failure is closed by the transaction/journal repair and
its focused generation-exhaustion and private-member failure witnesses.

The latest R-classification repair records owner-relative guarded traces,
forest-local variable sharing, non-generic closure, normalized Q occurrence
ordering, symmetric recursive-owner retention, and fallible traversal cleanup.
The follow-up repair now uses one shared predicate/R key namespace, collects Q
occurrences from retained R lower/upper bounds, rejects missing reachable rows,
computes incidence after eligibility from the expanded normalized draft, and
asserts the complete mutual guarded trace plus its draft recursive bound. Its
focused F5c suite passes 58 tests. The finalizer now rejects non-dense
recursive ordinals before binder construction, with focused gap, duplicate,
reorder, and dense Q/R round-trip witnesses. A bounded follow-up indexes reentries by
owner, enqueues only newly discovered reachable owners, makes direct-hop
survival side-aware, restricts grouped keys to final replayed/normalized
candidates, and caches final survivor traces. A further local repair replays
each candidate owner's bounds at most once per fixed-point iteration and reuses
the retained normalized bounds for final survivor filtering. Independent M3
semantic review found no new finding in the latest delta; performance review
closed the duplicate trace-replay finding.

The reviews also establish an authority gap: exact alpha-invariant ordering of
unrestricted commutative shared-variable forests is graph canonical labeling,
while §§25/34 require an O(N+S)-style normalized index. No implementation
choice can close both contracts without a user-approved design addendum.

Other open F5c gates remain:

- resolution of the exact-alpha versus bounded-normalization contract;
- fixed-point replay/rescan and stack-safe expansion/materialization;
- end-to-end per-use failure rollback across every availability lane.

F5's approved scope is the closed pure Function subset. Broader non-pure
Function effects are explicitly excluded; live non-pure effect endpoints are
rejected, with a focused rollback witness. Computation-valued fetch boundary
propagation is conditional future work because F5 has no such source form.

Do not claim F5c completion or F5e resource/public-observation certification.

## Next resume action

The ineligible-variable rejection gate is covered at boundary zero in both
polarities, and the production Q/R/eligibility rejection helper is tested with
isolated non-generic targets in both polarities. Closed-DAG incoming
instantiation and exact scratch accounting are closed after the focused 70-test
run and independent specification/performance reviews; growth-time sampling
reattaches live scratch for O(1) aggregate samples, route rollback preserves
scratch physical metrics, and canonical first-member/public versus
private-member argument correspondence is asserted. The closed child-DAG
invariant is confirmed by child-before-parent finalizer IDs; recursive binder
IDs are leaves.

The availability-lane audit now has focused per-use evidence through the
route-journal key and seen-vector owners. The current next step is to reconcile
any remaining owner-to-route lanes against the complete §3 list. The prior
sampler-cost attempt produced no valid comparison and exhausted its process
budget; a new measurement needs an isolating method and fresh budget. Keep
stack-safety residuals separate, and do not alter exact-alpha behavior before
the user's decision.

Stack safety remains open beyond the completed walker sub-slice. Expansion,
postorder summary construction/materialization, and structural comparison now
use explicit frames. The ordinary draft path still recurses through guarded
owner checks, replay, references/incidences, normalization/key processing,
and finalization; cloning and dropping a deep owned tree remain recursive.
Private output-vector accounting also needs to follow Union/Intersection
buffers after ownership transfers. The next slice is an indexed draft
representation retained through those operations, with transfer-aware physical
accounting and exact structural dedup. Do not claim stack-safety closure after
the walker-only witnesses. Admission no longer rescans shared DAGs per root;
its test-only invariant assertion is opt-in and has a focused active-ancestor
witness. The exact-alpha/complexity contract still needs a user decision; do
not alter its key search or §44 projection here.
The available choices are: retain exact unrestricted alpha ordering and
approve a revised canonical-search complexity contract; retain the bounded
contract and add/prove a restricted production forest class; or explicitly
weaken alpha/order independence. Preserve the approved first-member
representative projection; do not introduce a live Union Term or silently
weaken §44. Continue effects, closed-DAG, and remaining F5c gates independently
where that alpha decision is not required.

Use focused semantic checks first. Do not claim F5c completion or F5e
resource/public-observation certification while the listed gates remain open.

## Verification

- `cargo fmt --check`
- `cargo check -p yu-solver --tests`
- `cargo check --workspace`
- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1`
- `cargo test -p yu-solver --lib --no-default-features -- --test-threads=1`
  — historical pre-repair evidence: 91 passed
- `git diff --check`

Latest continuation checks:

- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` — 58 passed
- `cargo check -p yu-solver --tests`
- `cargo check --workspace` — passed after the warning cleanup
- `cargo fmt --check`
- `git diff --check`

Latest test-only gate checks:

- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` — 58 passed
- `cargo fmt --check`
- `git diff --check`
- Fresh specification delta review closed the ineligible-root masking
  finding; no new finding.

Latest closed-DAG incoming-instantiation/resource repair:

- `cargo test -p yu-solver --lib f5c_incoming_ -- --test-threads=1` — 11 passed
- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` — 63 passed
- `cargo fmt --check`
- `git diff --check`
- Independent specification and performance delta reviews — no findings
- `cargo check --workspace` was not rerun after the final sampling repair; it
  passed on the preceding candidate. No full `yu-solver` library rerun,
  benchmark, or F5e 1k/2k/4k resource matrix was run.

Latest per-use availability-lane extension:

- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` — 70 passed
- `cargo fmt --check`
- `git diff --check`
- Independent specification delta review closed the fresh-row `ValueBounds`
  injection-site finding; the test now injects inside the transaction closure.
- Production incoming witnesses cover `ExtrusionStack` and Bottom publication
  reserves; `ValueBounds` and `ValueExactUpper` remain owner-only tests.
- Independent performance review found that route rollback's nested capacity
  reconciliation does not yet synchronize aggregate retained/peak counters and
  independent ledger. An exact-conformance review says a separate
  post-rollback sample needs a narrow user-approved addendum. The design choice
  is pending; no broad suite, workspace check, benchmark, or F5e matrix ran.

`cargo test -p yu-solver --lib -- --test-threads=1` passed 136 tests in
1416.03 seconds before the final `cfg(test)` warning-only cleanup; the focused
suite was rerun afterward and now passes 58 focused tests. The no-default full
library suite was not rerun after the latest repair; its historical pre-repair
evidence remains 91 passed. No benchmark or F5e 1k/2k/4k resource matrix was
run.

The latest independent M3 resource/spec delta review closed transactional
ledger mutation, failed-memo recording, same-key rollback ordering, aggregate
peak reconciliation, later sequential-reserve accounting, and the warning
cleanup. A later admission optimization removes per-root shared-DAG traversal;
focused semantic/performance reviews found no major issue, and an opt-in test
postcondition checks active-incidence exclusion on a real expansion. No scale
benchmark or F5e certification has been run.

## Repository-policy note

`AGENTS.md` now explicitly states that subagents are the primary working
mechanism for bounded role-shaped exploration, implementation, and review,
while the primary retains authority, user interaction, adjudication, records,
and git integration.

## Indexed finalizer M2 review and adjudication (2026-09-23)

The Candidate B draft is
[`2026-09-23 F5c indexed finalization/accounting boundary`](../design/2026-09-23-f5c-indexed-finalization-accounting-boundary-draft.md).
Independent M2 specification and performance reviews both found it not ready
for user approval. The primary accepted the findings; a read-only architect
adjudication confirmed the producer and lane-accounting gaps.

The current production generalizer still emits boxed trees, normalizes the
predicate and recursive bounds separately, assigns Q/R per root, and sends
boxed terms into recursive finalization. The draft does not define the
ID-preserving producer, pruning/remapping/compaction, or prove that valid input
is reachable and orphan-free. A finalizer-only indexed adapter would preserve
the deep boxed-tree stack risk.

The current closed-finalization baseline comes from a prior F4 sample and does
not include all simultaneously live indexed input arrays and member drafts.
F5 §26 explicitly authorizes an O(1) sample when all drafts coexist. An exact
successful-call sequence can use it: account actual growths, record the
component-memo peak and let `clear()` release its lanes, sample all remaining
owners before the first finalization, then use each successful `DraftMember`
sample as the next call's baseline. The exact ledger still must cover the local
`members` vector, outer draft vector, five arrays per member, and each
temporary/transfer. Do not add post-failure sampling without an explicit
§26/§34/F5b decision. The draft also had inconsistent public item/array
counts, conflated indexed linear traversal with §34 closed-normalization cost,
and incomplete scratch growth/reconciliation details; its known count and cost
wording is corrected, but blockers remain.

Continue one bounded architecture round for the ID-preserving producer and
complete capacity ledger; this does not approve Candidate B. Any new §24 API
still needs a clean M2 review and explicit user approval before code. If exact
accounting requires a boundary beyond §26's all-drafts-coexist sample and
growth events, return with that narrow authority choice. The exact-alpha and
failed-route physical-accounting decisions remain separate blockers. No code,
tests, measurements, commits, or pushes came from this design-review round.

## Indexed producer follow-up (2026-09-23)

A bounded architect pass proposed this producer path, but did not certify it:

1. Carry polarity-specific node IDs and child spans from the iterative walk.
   Keep component-summary IDs in a separate namespace; import only completed,
   binder-free summary DAGs through root-local ID maps while preserving the
   existing exact-bound/direct-row, Function, and first-seen traversal order.
2. Store predicate and provisional R-bound roots as IDs. Replace boxed guarded
   trace, incidence, non-generic closure, replay, and fixed-point walks with
   explicit graph worklists while preserving existing candidate semantics.
   Keep the raw graph intact while candidate R owners are tested.
3. Preserve the existing alpha/permutation ranking and separate predicate/R
   normalization. Assign Q by the same first-occurrence paths, rewrite live
   leaves to Q/R/extremes, and reject unclassified rows.
4. Mark from the rewritten predicate and every retained R lower/upper root;
   compact in deterministic postorder, remap all typed child edges/spans, and
   rebuild child arrays so unreachable nodes/edges are omitted before the
   proposed `yu-types` indexed call.

Root-local alpha ordering remains distinct from F5 §34 closed normalization.
The unresolved invariant is parity between the current unfolded alpha-normal
trees / owner-context R ranking / Q occurrence paths and one shared indexed
graph. One graph key or visitation may not preserve paths across owners and
commutative permutations. The current R fixed-point, structural dedup, and
alpha-key costs also have no proven linear bound. Do not implement or approve
the indexed API until that parity and the complete per-lane accounting are
reviewed. The §26 all-drafts-coexist sample path is authorized; only the
exact lane ledger is unresolved. The separate exact-alpha and failed-route
sampling decisions remain open.

## Latest restart point after accounting-design review (2026-09-23)

The accounting design slice is now closed at the design/review level. The
Draft specifies checked event-time semantic/session totals and peaks, per-lane
capacity tickets with transfer/release gateways, six physical-owner groups,
closed-world allocation rules, overflow/unwind handling, and the §26-authorized
all-drafts-coexist sample sequence. Fresh independent M2 specification and
performance delta reviews found no preapproval blocker within this accounting
slice. This is not source or test proof: constructor hooks, every physical
lane/event, failed-reserve and unwind reconciliation, and the `yu-types`
same-time checkpoint still require postapproval implementation evidence. No
new post-failure sample is authorized by that design.

The full Candidate B is not ready for user API approval. Architect review
identified the exact producer/alpha gap: `F5cKeyForest::unordered_root_keys`
currently evaluates `k!` permutations for `k` distinct non-owner variables;
naively expanding an O(d)-node shared Function DAG by occurrence paths can
visit `2^d` paths. These refute the current algorithm/bound, not all possible
exact bounded algorithms. The context-keyed graph idea may preserve owner/path
semantics in principle, but has no proved work bound. Preserve §44's
first-normalized-member public Union representative throughout.

There are two user decisions before the affected code gates can resume:

1. Alpha/order contract: preserve unrestricted exact alpha and accept a revised
   worst-case complexity contract; preserve bounded work by restricting and
   proving the production forest class; or weaken alpha/order independence.
2. Failed-route physical accounting: approve a narrow conditional
   post-rollback O(1) sample; retain the sample whitelist and journal/reconcile
   every physical change without another sample; or defer that resource gate.

After the alpha choice, finish producer/key-order parity and obtain a clean M2
review of the complete Candidate B before asking for explicit approval of its
new §24 API. Do not implement the candidate before that approval. F5c/F5e stay
incomplete. This continuation changed design/task/handoff/index/daily records
only; it ran no code, tests, benchmark, commit, or push. See the accounting
Draft and current task record for the exact owner matrix and current state.

## Post-restart logical rollback verification (2026-09-23)

`cargo test -p yu-solver --lib f5c_incoming_union_ -- --test-threads=1`
passes all three matching tests. The failure witnesses use canonically
distinct `Int` and `Function` Union members and exercise both a private-member
diagnostic-edge reserve failure and a later representative-provenance failure.
The test checkpoint compares relevant logical live/session state and public
store state after rollback; retained physical capacity/resource deltas remain
separately accounted and are not declared closed. This confirms the logical
atomicity portion of F5 §44, not the outstanding failed-route physical
resource gate. No solver source, benchmark, commit, or push changed in this
verification.

## Producer-order and failed-route sample adjudication (2026-09-23)

The user's delegated design direction is adjudicated in
[`2026-09-23 F5c producer ordering and failed-route sampling`](../design/2026-09-23-f5c-producer-order-and-failed-route-sampling-addendum.md).
Q/R binders now follow first surviving producer encounter; equality across
different producer/admission orders is not required when that changes binder
numbering or positional recursive-bound order. The full Union relation,
same-input traversal contract, and §44 canonical first-member representative
plus transactional route operation remain required. A failed incoming route
takes one fixed-size O(1) post-rollback sample iff a physical capacity or
counted-owner/retention transition occurred.

Architect preflight and the final M3 specification, compiler, and performance
delta reviews are clean. This closes only these design choices. Producer-order
implementation/tests, bounded stack-safe post-Q/R normalization, complete
failed-route physical accounting and sample coverage, component sharing, the
remaining iterative producer/finalizer work, and F5e certification remain
open. Candidate B's proposed §24 API is not approved. The producer-order and
sampling choices remain authoritative, but fixed-Q/R closed normalization is
paused: §25 structural-first order and §36 per-postorder-height ranking do not
specify a single mixed-height child order. The user has been asked to choose
between preserving §25 with a clarified global structural rank, or explicitly
making §36 height-major order supersede §25. The earlier producer-order
relaxation does not cover this fixed-assignment change. Continue the
independent failed-route sampling subgate; do not change canonical order or
§44 projection until the decision is recorded, and do not claim F5c/F5e.

Sampler implementation checkpoint: fixed-size snapshot arithmetic and
instantiation-scratch metric flush now use checked preparation and atomic
publication. Focused overflow/route witnesses pass; spec and performance delta
review are clean for this core. The compiler review confirms the same core but
keeps the full §3 gate open: the outer failure trigger still keys only off
instantiation growth, missing partial route-begin growth (for example, first
seen-vector reserve succeeds and the second fails) and other lane events. The
architect is mapping a single attempt-local physical-change trigger across all
lanes. No full solver suite or benchmark ran.

## ConstraintStore and routed-use failed-route owner group (2026-09-23)

The four ConstraintStore owners (facts, canonical map, consumed receipts, and
provenance) now capture fixed-size simultaneous capacity snapshots at each
growth event. Incoming-route store owners use fallible reserves, so a failed
reserve that leaves capacity changed is sampled before its error propagates.
Per-lane growth and event counters are checked; overflow returns the existing
`IdentityExhausted` error without publishing partial route state. The event
snapshot is passed to the existing aggregate sampler and independent test
ledger, while the outer incoming-route exit still owns exactly one conditional
post-rollback sample. Routed-use records and positions remain covered by their
existing event hooks.

Focused tests cover the four ordered event snapshots, all four changed failed
reserves, store-counter and event-counter overflow, local admission failure
after growth, logical rollback, retained-capacity reconciliation, one outer
sample, and retry. The fresh M2 specification review found no blocking
conformance gap. Static performance review found O(1) aggregate work per event
with no added scans or per-route heap allocation; successful-path time remains
unmeasured and requires the planned bounded baseline/candidate measurement.

Verification for this owner group:

- `cargo test -p yu-solver f5c_ -- --test-threads=1` — 109 passed.
- `cargo test -p yu-solver --lib f5c_store_ -- --test-threads=1` — 5 passed
  after the cfg-only warning cleanup.
- `cargo check -p yu-solver` — passed without warnings.
- `cargo check -p yu-solver --tests` — passed.
- `cargo fmt --package yu-solver --check` and `git diff --check` — passed.

The full `yu-solver` library suite, workspace suite, benchmark, and F5e matrix
were not run. This closes only the ConstraintStore/routed-use owner group; the
remaining active/spare journal setup and value/effect-row journal owners still
need mapping, implementation, and independent evidence. Do not claim F5c/F5e
completion. Changes remain unstaged, uncommitted, and unpushed.

## Latest scratch changed-reserve closure and resume (2026-09-23)

The seven incoming-instantiation scratch lanes now preserve physical growth
evidence when a reserve changes capacity and then returns an error. The lane
growth counters use checked arithmetic; an O(1) pending-event marker carries a
changed capacity through error propagation, even if growth-counter publication
overflows. The changed-failure path samples while the scratch owner is attached,
then retains the separate §26 scratch-exit sample and the single conditional
post-rollback sample required by the failed-route addendum. A pre-reserve or
no-growth failure does not trigger the post-rollback sample.

The focused sidecar test exercises all seven lanes, consumes a failure after
actual capacity growth, checks one event sample per traced capacity change and
separate scratch-exit/post-rollback samples, verifies RouteCheckpoint logical
restoration and retained scratch-ledger reconciliation, then retries the same
use successfully. Companion tests cover no-growth with exhausted growth
counters, a changed-capacity counter-overflow marker, pre-reserve failure, and a
failed route without scratch growth. The test trace now consumes multiple Term
owner changes in their per-snapshot sample order.

Fresh M2 specification review found no blocking issue for this narrow gate.
Verification:

- `cargo test -p yu-solver --lib f5c_scratch_ -- --test-threads=1` — 3 passed.
- Pre-reserve scratch failure and no-growth/no-outer-sample focused tests —
  passed.
- `cargo test -p yu-solver --lib -- --test-threads=1` — 202 passed in
  675.10s.
- `cargo check -p yu-solver --tests` and `git diff --check` — passed.

The full F5c/§3 resource and F5e gates remain open. The bounded successful-path
event-sample measurement has not run. The `yu-solver` crate has no dedicated
benchmark target; choose an isolated production-path comparison before
measurement, within the approved one-warm-up/three-paired-sample/eight-process/
ten-minute budget. Continue independently on end-to-end per-use rollback across
the remaining availability lanes, component sharing and iterative producer /
finalizer work. The mixed-height §25/§36 normalization choice is still pending;
do not change fixed-assignment normalization or §44 projection. `lib.rs` is
28,441 lines; this repair kept the new focused test in
`src/tests/f5c_scratch_reserve.rs` and did not attempt a broad module split.
All changes remain unstaged, uncommitted, and unpushed.

## Latest resume: incoming ValueExactUpper lane and measurement limit (2026-09-23)

The per-use failure witness for the currently reachable `ValueExactUpper` lane
is now closed. A sidecar test drives one closed Function use through
`route_incoming`, pre-seeds a negative Function upper bound on the use row, and
injects failure after the fresh result row's `ValueExactUpper` reserve actually
changes capacity. Its trace proves that exact owner event was sampled before
the error propagated; the witness also checks RouteCheckpoint restoration,
no surviving public fact/provenance/routed marker, exactly one conditional
post-rollback sample, retained nested/session ledger reconciliation, and a
successful retry. A fresh M1 specification delta review is clean. The focused
test is in `crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs`; `lib.rs`
only gained its module declaration.

Primary adjudication: `FreshValueBounds` was already exercised through
`route_incoming` by `f5c_incoming_fresh_outer_row_growth_samples_before_rollback`
in `lib.rs`; the earlier resume summary understated that coverage. The new
`ValueExactUpper` witness closes that specific lane. The broader owner-to-route
failure-lane matrix remains open pending reconciliation of every reachable
value/store/diagnostic/journal lane against its incoming-route witness. Live
effect-row lanes remain outside this matrix because approved closed-pure
Function effects contain only `EmptyEffect`/`EffectBottom`; do not imply they
were exercised. None of this closes the full §3 resource/accounting gate.

The required successful-path sampler-cost experiment was attempted and
stopped without accepting timing data. Across the conservative eight-process
budget, the last paired run's temporary no-sample control bypassed 26
IncomingRoute aggregate calls while the measured sample counter still advanced
by 26. The control therefore did not isolate the target work; the single pair
printed before its assertion is invalid, and no warm-up/three-pair result was
completed. All temporary feature, setter, example, and test harness code has
been removed. Any later attempt first needs a path-complete ablation or another
valid baseline and a new measurement budget; do not repeat this experiment as
if it had produced a candidate/baseline comparison.

The `yu-solver` library test suite remains at 202 passed in the last full run.
For this new lane witness, the focused test passed; `cargo fmt --package
yu-solver --check`, `cargo check -p yu-solver --tests`, and `git diff --check`
passed. The experiment did not change product behavior. `lib.rs` is 28,442
lines, with one module declaration for the sidecar test. A read-only bloat
mapping found a mechanically safe 63-line `ResourceSampleChecked` extraction;
defer it to a separate local-refactor slice after the open accounting/measurement
checkpoint, so it does not contaminate the current gate.

Resume the owner-to-route lane audit and the remaining iterative
producer/finalizer and component-sharing gates, without changing the approved
§44 first-normalized-member representative. Producer-ordered Q/R normalization
remains paused on the unresolved mixed-height §25/§36 decision. The full §3
measurement/accounting gate, F5c, and F5e remain open. Work is still unstaged,
uncommitted, and unpushed.

## Incoming ValueLevels, ValueMetadata, and ExtrusionValueMarks witnesses (2026-09-23)

Two more changed-failure incoming-route lanes now have focused end-to-end
witnesses in `crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs`.
`ValueLevels` isolates a fresh quantified value-row capacity change while
earlier dense rows and route-journal storage have spare capacity. It proves one
event sample before failure propagation, an exact semantic/session retained
delta from the observed vector growth, event peak growth over the baseline and
peak preservation after rollback, complete logical/public route restoration,
one conditional post-rollback sample, and successful retry.

`ValueMetadata` similarly isolates its post-reserve failure after pre-reserving
the earlier `bounds`, `value_levels`, and `extrusion_value_marks` lanes. Its
event and post-rollback sample snapshots are matched only after successful
aggregate completion. The witness checks exact capacity-byte contribution,
event-time peaks, and one event plus one post-rollback sample. It then
recomputes a fresh `IndependentResourceLedger` from the live post-rollback
session capacities, the current journal owner, and independently enumerated
surviving nested rows; retained totals and peaks must match the captured
post-rollback snapshot. Checkpoint restoration and retry remain covered.

The next lane map found `ExtrusionValueMarks` had only pre-reserve coverage.
Its new quantified-value route fixture fills that vector, gives the earlier
`bounds`, `value_levels`, and `value_metadata` lanes spare capacity, then
injects at the fourth fresh-row reserve. The exact event lane, retained delta,
event peaks, independent post-rollback ledger, one conditional final sample,
checkpoint restoration, and retry all pass. A fresh M1 specification delta
review is clean for this lane. The broad route matrix remains open, especially
lane-specific changed-capacity evidence for remaining diagnostic scratch.

The `ValueLevels` M1 specification delta audit first found that lower-bound
aggregate assertions could be masked by unrelated growth; fixture prewarming,
single-lane isolation, exact totals, and event-peak assertions closed the
finding. The `ValueMetadata` audit first found missing post-rollback snapshots
and peak evidence, then required direct independent re-enumeration rather than
only a baseline-plus-delta check. The fresh ledger helper and named completed
sample snapshots closed that finding. Fresh post-repair M1 reviews are clean
for both lanes. The trace extension is cfg(test)-only and lives in
`incoming_sample_trace.rs`; this lane slice did not add code to `lib.rs`.
`lib.rs` is currently 28,456 lines. Keep the separate 63-line
`ResourceSampleChecked` extraction deferred until the accounting/measurement
checkpoint closes.

Verification: `cargo test -p yu-solver --lib f5c_value_exact_upper_route --
--test-threads=1` — 6 passed; `cargo check -p yu-solver --tests`,
`cargo fmt --all -- --check`, and `git diff --check` passed. The full solver
library suite was not rerun; its last full run remains 202 passed. No
benchmark or resource matrix was run; the previously exhausted eight-process
sampler-cost budget still has no valid timing result. Continue reconciling the
remaining reachable owner-to-route lanes. This closes only these named
witnesses, not the full §3 accounting/measurement gate, F5c, or F5e. All
changes remain unstaged, uncommitted, and unpushed.

## DiagnosticDelta changed-capacity failure witness (2026-09-24)

Added a changed-post-reserve `DiagnosticDelta` failure witness to
`crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs`. The route produces
an ordered sequence of completed capacity events. The witness requires an
earlier `FreshValueBounds` growth event and derives the target lane's retained
byte and peak changes from its immediately preceding completed sample, rather
than attributing unrelated prior growth to `DiagnosticDelta`. It also checks
the independent post-rollback ledger, exact route checkpoint restoration, one
conditional post-rollback sample, failure consumption, and successful retry.

A fresh M1 specification delta review found no blocker after requiring the
actual earlier event. The review confirmed event/sample pairing and the exact
§3 failed-route sampling boundary. The focused sidecar now has seven passing
tests; `cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check` pass. The last completed full solver library result remains
202 passed. A later 209-test single-threaded run was interrupted after more
than six minutes in the F4 scale tests; before interruption,
`direct_root_n_and_2n_counters_remain_linear` was reported failed. Its isolated
rerun passed 1/1; the cause of the discrepancy remains unadjudicated. No
benchmark or resource matrix was run, and the earlier eight-process
sampler-cost budget remains consumed without valid timing data. This closes
only the `DiagnosticDelta` witness, not the broader owner-to-route matrix,
full §3 gate, F5c, or F5e. The current lane slice kept test bodies and trace
machinery outside `lib.rs`. The checkpoint commit is `bb1ec56c`; check the
current branch status for remote synchronization.

## Errors-lane changed-capacity witness (2026-09-24)

Added `f5c_incoming_errors_growth_samples_after_first_union_member_and_retries`
to `crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs`. The incoming
scheme is a normalized Union of canonically distinct Int and Function members;
an existing Int upper bound lets the first Int member complete and makes the
second Function member incompatible. The fixture pre-reserves
`ReportedErrors` and its route-journal key lane, then injects failure after the
`Errors` Vec grows. The trace pairs all completed capacity events and derives
the target event's exact retained/session delta and peaks from the immediately
preceding completed sample. It also proves the event sample preceded failure,
the route checkpoint is restored, the error Vec's physical capacity remains,
one conditional post-rollback sample reconciles against a fresh ledger, and
retry reports one incompatibility while publishing only the canonical Int
representative fact.

The first M1 spec review found that retry did not verify the public
representative. The test now checks the sole public fact's lower Term is
`Leaf::IntPositive`; a fresh spec delta review closed the finding and found no
new blocker. The focused value-route sidecar passes eight tests, the exact new
test passes, `cargo check -p yu-solver --tests`, formatting, and `git diff
--check` pass. The full library-suite attempt and its unresolved isolated
linearity-test discrepancy remain as described above. No benchmark or resource
matrix was run. This closes only the `Errors` changed-capacity witness; the
remaining reachable diagnostic scratch/`ReportedErrors` lanes and the wider
owner-to-route matrix remain open. This test-only slice did not modify
`lib.rs`; F5c/F5e are still incomplete.

## `ReportedErrors` changed-capacity witness (2026-09-24)

Added
`f5c_incoming_reported_errors_growth_samples_after_first_union_member_and_retries`
to the route-sampling test sidecar. It uses the same normalized, canonically
distinct Int/Function Union and existing Int upper bound, but pre-reserves the
`Errors` vector and route-journal key lane so the injected changed-capacity
failure is isolated to the `ReportedErrors` set. The witness requires the Int
private member to complete first, records event-time growth and exact
session-byte/peak delta from the immediately preceding completed sample, and
checks that the set retains physical capacity while all logical route state is
restored. One conditional post-rollback sample is reconciled against an
independent ledger. Retry reports the Function-vs-Int incompatibility while
publishing exactly one public `Leaf::IntPositive` representative fact.

A fresh M1 specification delta review found no blocker. The focused sidecar now
passes nine tests; `cargo check -p yu-solver --tests`, format, and
`git diff --check` pass. The prior full-library attempt and unresolved isolated
linearity-test discrepancy remain unchanged; no benchmark/resource matrix was
run. This closes only the `ReportedErrors` changed-capacity witness. Other
diagnostic scratch lanes, the complete owner-to-route matrix, the §3
sampling/accounting gate, F5c, and F5e remain open. This test-only slice did not
change `lib.rs`.

## `DiagnosticDeltaIndices` changed-capacity witness (2026-09-24)

Added
`f5c_incoming_diagnostic_delta_indices_growth_samples_before_rollback_and_retries`
to the incoming value-route sampling sidecar. The fixture leaves the index
HashMap at zero capacity while pre-reserving the typed-pair map, diagnostic
delta Vec, and route-journal typed-pair key lane. It injects failure after
`DiagnosticDeltaIndices` grows, checks the observed `(CanonicalValuePairKey,
usize)` slot-byte delta and aggregate peaks against the immediately preceding
completed event, and proves that one post-rollback sample reconciles to an
independent retained-resource ledger while the route checkpoint is restored.
Retry checks that the fact, provenance edge, consumed receipt, routed-use
record, and use-position marker all refer to the one intended route.

The focused sidecar passes ten tests. Package test-check, formatting, and
whitespace checks pass. The fresh M1 spec review found the sampling and ledger
evidence sound, and flagged a minor retry-identity/linkage gap; the primary
closed it by checking fact/provenance identity, receipt count, and route/use
linkage, followed by the exact test rerun. The witness uses a simple quantified
predicate to isolate this diagnostic map lane; it does not replace the separate
Union-representative witnesses. Other diagnostic scratch lanes, the complete
owner-to-route matrix, §3 accounting/measurement, F5c, and F5e remain open. No
production code or `lib.rs` changed.

## `DiagnosticReverseOffsets` changed-capacity witness (2026-09-24)

Added
`f5c_incoming_diagnostic_reverse_offsets_growth_samples_before_rollback_and_retries`
to the incoming value-route sampling sidecar. The fixture pre-reserves the
typed-pair map, `DiagnosticDelta`, `DiagnosticDeltaIndices`, and journal key
lane, then replaces the `DiagnosticReverseOffsets` vector with an empty one to
isolate its first growth. The witness checks the `usize` slot-byte delta and
event peaks against the immediately preceding completed sample, retained
capacity, full checkpoint rollback, one conditional post-rollback sample with
independent retained-ledger reconciliation, and retry identity across fact,
provenance, consumed receipt, routed use, and use-position marker.

The fresh M1 spec review first raised a major concern that the independent
ledger was seeded with the event peak. Primary adjudication pointed to the
separate assertions deriving the event peak from the immediately preceding
completed sample plus the observed capacity delta, and requiring the final
sample to preserve that peak; the reviewer then withdrew the finding. No
remaining review finding. The focused value-route sidecar passes eleven tests;
package test-check, format, and whitespace checks pass. No production code or
`lib.rs` changed. A follow-up M1 test-only consolidation moved the shared
route/trace/rollback/retry assertions for `DiagnosticDelta`,
`DiagnosticDeltaIndices`, and `DiagnosticReverseOffsets` into one private
helper. Lane-specific capacity setup and slot-size formulas remain explicit.
The refactor removes 325 net lines, and a fresh specification delta review
found no weakened or omitted assertion. Remaining diagnostic scratch lanes,
the owner-to-route matrix, §3 accounting/measurement, F5c, and F5e remain open.

## `DiagnosticReverseCursors` changed-capacity witness (2026-09-24)

Extended the shared diagnostic-lane helper with a changed-post-reserve witness
for `DiagnosticReverseCursors`. The fixture isolates its vector at zero
capacity, while ensuring the preceding `DiagnosticReverseOffsets` vector has
capacity for the route's one diagnostic pair plus terminal offset (two slots).
The shared assertions cover `usize` slot accounting, event-time sample and
peak, one conditional post-rollback sample, independent retained-ledger
reconciliation, full checkpoint restore, and retry identity.

The M1 specification delta review found a minor proof gap: the initial fixture
reserved one predecessor slot and checked only nonzero capacity. It now
reserves and asserts at least two slots, matching `pair_count + 1`. The exact
test passes after the repair; the focused value-route sidecar passes twelve
tests, package test-check, format, and whitespace checks pass. No production
code or `lib.rs` changed. Other diagnostic scratch lanes, the owner-to-route
matrix, §3 accounting/measurement, F5c, and F5e remain open.

## Per-pair diagnostic scratch lane matrix extension (2026-09-24)

Extended the shared changed-capacity helper to cover eight more one-pair
diagnostic scratch lanes: DFS stack, finish order, SCC indices, SCC nodes, SCC
offsets, SCC pending children, SCC worklist, and node witnesses. Each selected
lane starts at zero capacity while the other route-preceding scratch lanes are
pre-reserved to their exact one-pair request; offset lanes reserve two slots.
The helper retains the same event-time delta/peak, rollback, independent
retained-ledger, exactly-one post-rollback sample, and retry identity checks.

The focused value-route sidecar passes thirteen tests; package test-check,
format, and whitespace checks pass. A fresh M1 specification delta review found
no issue. No production code or `lib.rs` changed. The formerly uncovered
`DiagnosticReverseEdges`, `DiagnosticBucketHeads`, `DiagnosticBucketTails`, and
`DiagnosticBucketCandidates` lanes now have changed-capacity failure witnesses
in the incoming route-sampling sidecar, driven by a Union fixture with both
diagnostic edges and a mismatch seed. Their independent ledger recomputes
retained typed-pair child-edge payload. A first M1 review's §44 representative
finding was repaired by checking the finalized first member and retried fact
lower endpoint; fresh M1 delta review is clean. The complete owner-to-route
matrix, §3 accounting/measurement, F5c, and F5e remain open. Next audit exact
trace witnesses for `TypedPairs` and `DiagnosticEdges`.

## TypedWorklist changed-capacity witness (2026-09-24)

Extended the generic incoming-route changed-capacity sidecar helper with an
isolated `TypedWorklist` failure case. The quantified source fixture keeps a
real earlier `FreshValueBounds` event; the worklist starts at zero capacity and
the injected post-reserve failure is traced to `TypedWorklist`. The shared
witness checks exact slot-byte and event-peak deltas, RouteCheckpoint restore,
one post-rollback sample, independently recomputed retained resources, and
retry linkage across fact, provenance, receipt, and routed-use state.

The fresh M1 specification delta review found no issue. Primary verification:
the exact test passes, the full sidecar passes 14 tests,
`cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check` pass. The helper rename preserves all previous diagnostic
lane assertions. No production code or `lib.rs` changed; the test remains in
the sidecar. The broader §3/F5c/F5e gates remain open.

## TypedPairs and DiagnosticEdges changed-capacity witnesses (2026-09-24)

Extended the shared incoming-route reserve witness with two remaining typed
memo lanes. `TypedPairs` starts from a verified zero-capacity map and checks
its exact key/memo slot-byte growth event. `DiagnosticEdges` uses an
edge-producing normalized Union constrained against a negative Function; its
per-pair child vector is allowed to disappear when rollback removes the new
memo, so event-time peak evidence is reconciled against the independently
rebuilt retained post-state rather than a surviving target capacity.

Both witnesses verify ordered event-to-sample linkage, exact capacity delta,
event peaks, full RouteCheckpoint restoration, one conditional
post-rollback sample, independent retained-ledger reconstruction, and retry
identity. The edge case also confirms the canonical first Union member remains
the sole public representative. A fresh M1 specification delta review is clean.
Primary verification: the focused incoming-route filter passes 55 tests, the
full value-route sidecar passes 16 tests, `cargo fmt --all -- --check`, and
`git diff --check` pass. No production code or `lib.rs` changed; this is test
coverage only. Next audit per-use rollback and remaining owner-to-route
transitions. The §3 sampling/accounting gate, F5c closure, and F5e certification
remain open.

## Route-journal undo-key changed-reserve witnesses (2026-09-24)

Added end-to-end changed-capacity failure witnesses for the `typed_pair_keys`
and `reported_error_keys` Vecs owned by `RouteMutationJournal`. Since each
journal Vec shares its reserve lane with the typed-pair map or reported-error
set, a cfg(test)-only matching-reserve skip count now lets the test inject the
failure after the journal Vec grows, before its new key is pushed. Existing
post-reserve injection callers still target their first matching reserve.

Both witnesses check the exact journal slot-byte delta, event-time retained
and peak totals, spare-owner capacity after rollback, full RouteCheckpoint
restoration, one conditional post-rollback sample, independent retained-ledger
reconciliation, and successful retry. The reported-error Union retry checks
the canonical Int representative and fact/provenance/receipt/routed-use links.
A fresh M1 specification review found one minor omission: canonical-map linkage
on retry. The primary added that assertion and reran the focused journal tests.

Verification: both new tests pass; the value-route sidecar passes 18 tests;
the related journal filter passes five tests; `cargo fmt --all -- --check` and
`git diff --check` pass. The only `lib.rs` change is the 17-line cfg(test)
injection seam; fixture and assertion code remains in the test sidecar. Next,
strengthen event/sample and independent-ledger evidence for `value_row_seen`
and `effect_row_seen` setup reserves. The owner-to-route matrix, full §3 gate,
F5c closure, and F5e certification remain open.

## Journal seen-vector setup event witnesses (2026-09-24)

The partial journal-setup failure witness now starts the incoming sample trace
before route begin, then injects the existing post-reserve failure at the
EffectBounds-backed second seen-vector reserve. It proves exactly two ordered
events: `journal/value_row_seen` and `journal/effect_row_seen`. Each begins at
zero capacity and is reconciled using its observed slot delta and the previous
event sample, including semantic/session peaks and finish-output bytes.

After failed begin, the test checks RouteCheckpoint restoration, both retained
capacities in the spare journal, empty logical seen vectors, one conditional
post-rollback sample, and independent retained-ledger/counter agreement. The
existing retry remains intact. Fresh M1 specification review is clean. Primary
verification: the five-test journal filter passes; format and diff checks pass.
Three existing journal setup tests were mechanically relocated from `lib.rs`
to the test sidecar without changing bodies, reducing `lib.rs` by 91 lines.
Next reconcile the remaining per-use owner-to-route matrix against §3. The
sampler-cost remeasurement remains deferred pending a fresh budget and a valid
isolating method; F5c/§3/F5e remain open.

## Incoming value-row undo-owner event witness (2026-09-24)

Moved `f5c_incoming_value_undo_growth_precedes_later_provenance_failure` from
`lib.rs` into `tests/f5c_value_exact_upper_route.rs` and strengthened it for the
`RouteMutationJournal.value_rows` reserve. The trace requires exactly one
`journal/value_rows` capacity event and ties its observed `ValueRowUndo` slot
delta to the corresponding event-time retained-byte and peak sample. It also
checks that the sample sees the active journal, the capacity and undo entries
survive rollback in the spare journal, RouteCheckpoint/public-route restoration,
exactly one post-rollback sample, independently reconstructed retained/session
and nested totals, and successful retry.

Fresh M1 specification delta review found no blocking or major finding. The
focused test, `cargo check -p yu-solver --tests`, formatting, and whitespace
checks pass. The independent post-rollback ledger enumerates retained state;
it carries forward the event peaks already derived from the immediately
preceding sample and observed capacity delta rather than independently replaying
the full peak history. The move removes 67 lines from `lib.rs`; no production
code changed. Next reconcile the remaining ConstraintStore and routed-use owner
traces against §3. F5c, the full §3 accounting/measurement gate, and F5e remain
open.

## ConstraintStore incoming-route changed-reserve witnesses (2026-09-24)

Moved `f5c_store_changed_failed_reserves_keep_one_outer_sample` from `lib.rs`
into the route sidecar and extended its four injected post-reserve cases to
trace facts, canonical keys, consumed receipts, and provenance. Each preceding
successful store growth and the changed failed reserve is linked to its ordered
event sample using that lane's slot size. Store bytes are session-only, so the
assertions require unchanged semantic totals and exact session deltas/peaks.
The test then checks one post-rollback sample, restored logical state, retained
capacities, independent retained/session/nested totals, and exact successful
retry publication across fact, canonical key, receipt, provenance, and routed
use.

The first test-only attempt used the wrong aggregate expectation; source
inspection confirmed no production sample-order defect. A second test run
exposed that RouteCheckpoint compares all store counters even though the
approved physical growth/rebuild counters remain monotone. The test now checks
those counters against event-derived counts and normalizes only those fields in
the expected checkpoint before asserting all remaining logical state. The
original shared closed-Union fixture is preserved. An M1 spec review found a
minor omission in retry linkage; primary added canonical/receipt/provenance
assertions and verified the focused sidecar. No production code changed; moving
the test removes 46 lines from `lib.rs`.

Verification: the single-threaded sidecar filter
`cargo test -p yu-solver --lib f5c_value_exact_upper_route -- --test-threads=1`
passes 23 tests;
`cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check` pass. Full solver/workspace suites and performance
measurement were not run. The complete §3 gate, F5c, and F5e remain open.

## Routed-use incoming-route changed-reserve witnesses (2026-09-24)

Moved `f5c_route_use_owner_failed_reserves_reconcile_after_rollback` from
`lib.rs` into `tests/f5c_value_exact_upper_route.rs`, removing 54 lines from
the already large primary file. The two injected cases now trace the ordered
`RoutedUsePositions` and `RoutedUses` owner events, check exact observed slot
byte deltas and semantic/session attribution, prove one post-rollback sample,
assert logical checkpoint restoration and retained capacities, rebuild
post-rollback retained/nested totals independently, and retry through the
canonical fact, receipt, provenance, routed-use, and position links.

The first M1 specification review found two major assertion gaps: the
`RoutedUses` semantic delta was only positive rather than exact, and the
independent ledger was seeded directly from the target event's production
peak. The repair now checks the exact delta and derives each target event peak
from the immediately preceding completed sample, exact lane delta, and
finish-output bytes. Those test-derived expected peaks, not the target sample
fields, seed the independent post-rollback ledger. A fresh specification
delta review accepted this carry-forward at the per-owner scope: earlier event
peak transitions have their own lane witnesses; this test does not replay the
whole route history. No production code changed.

Verification: the focused routed-use test passes 1/1;
`cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check` pass. The full solver suite and performance measurement were
not run. The complete §3 gate, F5c, and F5e remain open.

## ValueLevels incoming-route retained-ledger witness (2026-09-24)

Extended `f5c_incoming_value_levels_growth_samples_before_rollback_and_retries`
to capture the completed post-rollback sample and independently rebuild
retained/session and nested-bound totals from surviving state. Its one
event-time sample now checks exact semantic/session byte deltas and derives
exact peak values from the pre-attempt peaks, observed ValueLevels capacity
delta, and finish-output bytes. The test-derived expected peaks seed the
independent ledger, which is compared against the post-rollback sample and
production counters. Existing checkpoint restoration, retained physical
capacity, no-public-route, and retry assertions remain.

The first specification review found an initial compile blocker: expected peak
locals were referenced before definition. Primary added the locals from the
saved pre-attempt state and exact event delta; the reviewer confirmed closure.
The focused test, package test-check, format, and whitespace checks pass. No
production code changed. This slice is checkpointed as `38d40b01` and pushed
to `origin/yulang3`. The full §3 gate, F5c, and F5e remain open.

## FreshValueBounds incoming-route event/rollback witness (2026-09-24)

Moved the incoming fresh-outer-row failure witness from `lib.rs` into
`crates/yu-solver/src/tests/f5c_value_exact_upper_route.rs` and strengthened
it into a same-proof rollback/retry test. The trace identifies exactly one
`FreshValueBounds` growth event and its completed sample; the test derives the
outer `VariableBounds` byte delta from the observed capacity change and checks
semantic/session retained bytes and peaks against the immediately preceding
sample. It then asserts exactly one completed post-rollback sample, complete
RouteCheckpoint restoration, retained physical capacity, independent
post-rollback semantic/session/nested-ledger reconstruction, production-ledger
reconciliation, and successful retry linkage through canonical fact, consumed
receipt, provenance, and routed-use records. The move removes 75 test lines
from `lib.rs`; no production code changed.

The focused witness and all 57 `f5c_incoming_` tests pass, as do the package
test check, workspace formatting check, and whitespace check. The user asked
for primary-only work without subagents, so this M1 slice has primary diff
inspection but no independent reviewer. No benchmark or sampler-cost
measurement was run; that measurement budget remains exhausted without a
valid comparison. This slice is checkpointed as `e226f8b4` and pushed to
`origin/yulang3`. Next: reconcile the remaining per-use owner-to-route lanes
against §3. The full §3 gate, F5c, and F5e remain open.

## ExtrusionStack incoming-route transient/retained witness (2026-09-24)

Moved `f5c_incoming_extrusion_stack_growth_samples_before_rollback` from
`lib.rs` to the existing value-route sidecar and strengthened it into an exact
event/rollback/retry witness. The test derives the `ExtrusionEndpoint` slot-byte
delta from the observed capacity change, checks the target event against its
immediately preceding sample, and proves that this is the final capacity event
before rollback. The single post-rollback sample preserves the event peak while
its retained totals are lower after transient route scratch is released; an
independent ledger rebuilds surviving retained/nested state and reconciles the
production counters. Full RouteCheckpoint restoration and retry publication
through canonical fact, receipt, provenance, and routed-use links are asserted.
The move removes the old test body from `lib.rs`; production code is unchanged.

The focused test and all 57 `f5c_incoming_` tests pass, along with
`cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check`. Primary-only M1 work follows the user's explicit request;
there is no independent review. No benchmark was run. The test/record slice is
checkpointed as `559a2d91` and pushed to `origin/yulang3` before the next §3
lane audit. The complete §3 accounting/measurement gate, F5c, and F5e remain
open.

## ValueExactUpper fresh-row transient-bound witness (2026-09-24)

Strengthened `f5c_incoming_value_exact_upper_growth_samples_before_rollback_and_retries`
to capture the completed `ValueExactUpper` event sample, derive its exact
`ValueEndpointKey` byte delta, and compute event-time semantic/session peaks
from the immediately preceding sample. The route grows the exact-upper payload
on the fresh row at the pre-attempt `bounds.len()`; rollback drops that row.
The same trace also records a `ValueExactLower` growth on a preexisting row,
whose capacity survives rollback. The one post-rollback sample and independent
ledger now prove that split: the upper lane returns to its baseline while the
lower lane retains its observed delta, and production retained/peak totals
match the independent surviving-state ledger. The target upper event is the
last capacity event, so its derived peak is reconciled directly with the final
sample. Full RouteCheckpoint restoration and successful retry linkage through
canonical fact, consumed receipt, provenance, and routed-use records remain
asserted. No production code changed.

The focused witness and all 57 single-threaded `f5c_incoming_` tests pass, as
do `cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check`. Primary-only M1 work follows the user's explicit request;
no independent reviewer or benchmark was used. The verified test/record slice
is pending checkpoint. Next: strengthen `ValueExactLower`'s paired event and
rollback evidence, then continue the §3 owner-to-route audit. The complete §3
accounting/measurement gate, F5c, and F5e remain open.
