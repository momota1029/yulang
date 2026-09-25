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
is checkpointed as `7c07b7af` and pushed to `origin/yulang3`. The next M1
slice strengthens `ValueExactLower`'s paired event and rollback evidence,
then continues the §3 owner-to-route audit. The complete §3
accounting/measurement gate, F5c, and F5e remain open.

## ValueExactLower retained-row rollback witness (2026-09-24)

Strengthened `f5c_incoming_value_exact_lower_growth_samples_before_rollback_and_retries`
to bind the completed `ValueExactLower` event to the preexisting use row and
its exact `ValueEndpointKey` capacity delta. Event-time semantic/session
retained bytes, nested-bound bytes, and peaks are derived from the immediately
preceding sample. Unlike the paired upper-lane witness, this lower payload
survives rollback: the post-rollback sample and an independent retained-state
ledger reconcile that exact delta and the surviving nested total. The witness
also reconciles event sampling counters, RouteCheckpoint restoration, and
retry publication through canonical fact, consumed receipt, provenance, and
routed-use links. No production code changed; the test remains in the existing
sidecar, with no additions to `lib.rs`.

The focused witness and all 57 single-threaded `f5c_incoming_` tests pass, as
do `cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`, and
`git diff --check`. Primary-only M1 work follows the user's explicit request;
no independent reviewer or benchmark was used. This verified slice is
checkpointed as `f69dbb76` and pushed to `origin/yulang3`. Next: continue the
residual §3 owner-to-route audit, now including the direct value-row lanes.
The complete §3 accounting/measurement gate, F5c, and F5e remain open.

## ValueDirectLower/Upper event and rollback witnesses (2026-09-24)

Strengthened `f5c_incoming_value_direct_rows_sample_before_rollback_and_retry`
for both direct-bound lanes. It now identifies the exact preexisting lower row
and fresh upper row, derives each `u32` slot-byte delta from the completed
event, and reconciles event-time semantic/session retained bytes, nested bytes,
and peaks against the immediately preceding sample. The post-rollback sample
and independently rebuilt ledger distinguish the surviving lower-row growth
from the dropped fresh upper row; complete RouteCheckpoint restoration and
retry links through canonical fact, receipt, provenance, and routed-use records
are asserted. A small event/sample assertion helper stays in the test sidecar;
`lib.rs` and production code are unchanged.

The focused direct-row witness and all 57 single-threaded `f5c_incoming_` tests
pass, as do `cargo check -p yu-solver --tests`, `cargo fmt --all -- --check`,
and `git diff --check`. Primary-only M1 work follows the user's explicit
request; no independent reviewer or benchmark was used. This verified slice
is checkpointed as `8b118260` and pushed to `origin/yulang3`. Next: continue
the residual §3 owner-to-route audit. The complete §3 accounting/measurement
gate, F5c, and F5e remain open.

## §3 per-use owner-to-route crosswalk and final-sample overflow (2026-09-24)

The primary reconciled the §3 per-use changed-capacity matrix against the
incoming-route witnesses and the current approved closed-pure Function scope.
Coverage now maps nested/fresh value-bound rows and outer value tables;
metadata, direct/exact bounds, and extrusion lanes; typed-pair payload and all
diagnostic scratch owners; all seven instantiation scratch lanes; all six
inference-Term physical owners; active/spare journal undo and setup vectors;
all four ConstraintStore owners; and both routed-use owners. The audit also
confirmed the no-physical-change skip and partial-begin cleanup cases. Live
effect-row mutation is excluded because current pure Function schemes use only
closed `EmptyEffect`/`EffectBottom` effects.

The audit found one missing witness: checked-byte overflow specifically at the
conditional post-rollback sample boundary. A cfg(test)-only
`IncomingPostRollback` fixed-capacity probe now reaches that exact sample after
changed-capacity event samples and rollback. The direct-route witness verifies
full RouteCheckpoint restoration, exactly one attempted but uncompleted final
sample, no boundary/test-ledger sample publication for that failure, and the
resource ledger remaining at its last completed event sample. A consuming
`run()` witness uses partial journal setup growth, proves one final-sample
attempt and `IdentityExhausted`, and returns no `SolvedModule`. Both test bodies
remain in the existing value-route sidecar; `lib.rs` only gains the test probe
variant and condition. Existing `f5c_resource_sample_overflow_publishes_nothing`
continues to assert all-or-nothing counter and ledger publication at the
sampler boundary.

The focused `f5c_` library filter passes 137 tests, including both new
post-rollback overflow witnesses. No production runtime behavior changed and
no benchmark was run. A full single-threaded `yu-solver` library run was
started but stopped during `f4_unbounded_cycle_scale_4k_keeps_direct_frontier_linear`
after more than seven minutes; it has no final suite result and is not
verification evidence. The successful-path sampler-cost measurement remains
unresolved, and the previously exhausted measurement budget is unchanged.

This closes the residual per-use owner-to-route witness crosswalk for the
current pure-Function route set only. The full §3 accounting/measurement gate,
F5c, and F5e remain open. Continue with the other active F5c gates without
adding live effect-row mutation or changing the approved first-member Union
projection. The mixed-height fixed-Q/R normalization authority question and
the stack-safe producer/finalizer work remain separate open gates.

## Mixed-height normalization choice (2026-09-24)

The user selected option B: use §36's height-major descriptor ranking when
normalized Union/Intersection children have different postorder heights. The
choice is recorded in
[`2026-09-24 F5c mixed-height normalization ordering`](../design/2026-09-24-f5c-mixed-height-normalization-order-addendum.md).
Lower postorder height sorts first; descriptors at the same height use §36's
stable lexicographic mergesort order. This supersedes §25 only for the
conflicting mixed-height child order. §44's first-member representative and
transactional private-member constraints remain unchanged, so the selected
representative can change for a mixed-height Union.

Current code inspection found that `F5cKeyForest::finish_grouped` still
enumerates variable-label permutations in R/Q selection, while the post-Q/R
normalizer and finalizer still recurse over boxed trees. The existing
`ClosedTypeFinalizationSession::finalize_scheme` uses a higher-ranked callback;
`finalize_generalization_draft_raw` creates transaction-branded handles and
recursively builds children inside it. The F5b boundary forbids callback
allocation/mutation of solver-owned lanes. The proposed indexed `yu-types`
finalization API remains an unapproved Draft, and its prior review identified
producer-graph/compaction and exact accounting gaps. Do not implement that API
or move handle storage across the callback without a separate reviewed and
user-approved boundary.

## Producer-encounter ordering implementation checkpoint (2026-09-24)

The current code slice now implements the approved producer-order rule:
retained R owners follow their first surviving trace in `self.reentries`, and
Q ordinals follow first occurrence in the retained predicate followed by each
R owner's lower then upper bound. A single live-identity-to-Q map spans that
whole traversal. Factorial variable-label permutation ranking and the
normalized-first guarded-trace sort were removed. The exact R fixture now
asserts the unique owner sequence stored in the producer trace, and another
producer-level fixture checks one Q identity shared by the predicate and two
R bounds. Dense R ordinal addition now uses checked conversion/arithmetic.

Mode: M2, primary-only at the user's explicit direction; no independent
reviewer was used. Verification: `cargo fmt --check`,
`cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (136 passed), and
`git diff --check`. The suite also rejects leftover live `Variable`/`Shared`
nodes before normalization. `lib.rs` is 27,892 lines, 200 fewer than the 28,092-line
resume point, after deleting the factorial alpha-key implementation. No
benchmark or F5e resource matrix was run.

This is a partial producer-order implementation checkpoint, not closure of
the producer-order gate. Remaining assertions include the final R-prune
no-op, dense/reference-complete Q/R after normalization, the pre-pruning
census case involving a later-pruned provisional R bound, hash/insertion
variation, and §44 linkage to the exact finalized first member. Most
importantly, the selected B normalizer is not implemented: current structural
tree ranking remains recursive and structural-first, so it is not yet
height-major or stack-safe. The finalizer also recursively constructs
transaction-branded handles inside its existing higher-ranked callback. Keep
§24 and the F5b accounting/callback boundary unchanged; if the new pass cannot
be carried through that boundary with exact accounting, stop for a separate
reviewed and user-approved decision. Next: implement the bounded,
stack-safe §36 descriptor order in a private module, add mixed-height
positive/negative and duplicate tests plus §44 representative linkage, and
reconcile stack scratch/accounting without growing `lib.rs`. The old note's
statement that code was unchanged is historical and superseded by this
checkpoint.

## Height-major normalization implementation checkpoint (2026-09-24)

The selected option B is now implemented as a local candidate in
`crates/yu-solver/src/f5c_normalization.rs`. Production calls a component-wide
iterative postorder pass before `DraftsVisible`; each height group uses the
specified stable descriptor-word mergesort, exact equal descriptors share a
rank, and Union/Intersection children are sorted and deduplicated by
`(height, rank)`. Rebuild is iterative. The module owns an 11-lane Vec index
ledger with checked capacity arithmetic; the public `closed_normalization_index`
family and §34/§36 normalization counters are wired into `ProductionCounters`.
No §24 callback/API or live Union Term was added. `lib.rs` is 27,812 lines,
80 fewer than at the pushed producer-order checkpoint; the algorithm and its
tests live outside that already-large file. The later physical-capacity ledger
and amortized-reserve repair is preserved in local commit `d1ac3062`.

Tests cover positive and negative mixed-height order, duplicate collapse,
source-order-insensitive normalized output, unclassified-node rejection, a
4,096-Function chain on a 64 KiB stack, transient index-lane reconciliation,
public counter exposure, and §44 routing of exactly the first member after
height-major normalization (including the case where §25 structural-first
would choose the other member).

The test-only independent ledger now reads all 11 live Vec capacities and
slot sizes before release, independently sums their co-resident peak, and
reconciles that sum to the normalization-index peak. Normalizer growth uses
fallible amortized `try_reserve`, avoiding exact one-slot reallocation on each
push. Counter updates are staged on a copy, with an overflow witness proving
that a later checked-add failure publishes no partial counters.

The gate is not closed. A root-permutation probe with the same five quantified
leaf roots, rotated as a set, produced identical normalized values but
different exact stable-mergesort word-comparison counts: 18 and 24. This
conflicts with F5 §36's simultaneous requirements that the counter report the
comparisons performed by the prescribed mergesort and that root-order
permutations yield identical counters. A test-only integer-descriptor oracle
now reproduces both counts independently from the production key builder and
checks the output schemes are the same set; it deliberately does not assert
counter invariance. A separate checked-overflow witness proves normalization
counter publication is atomic.

This incomplete candidate is preserved in local commit `b07de8fe` on
`yulang3`; it is not pushed. User direction is needed before resolving that
conflict:

1. Keep the exact input-sensitive comparison counter and narrow the
   root-permutation invariance requirement to ranks, normalized child order,
   and schemes; or
2. Keep all-counter invariance and approve an extra deterministic
   pre-ordering/comparison schedule plus its additional work and scratch model.

The first option preserves the specified sort and reports actual work. The
second adds a new algorithm/resource decision beyond the already-selected
height-major order. Do not silently choose either. The index ledger accounts
its 11 physical Vec lanes only; it does not certify all simultaneously live
F5c draft/output-tree scratch or F5e resource surfaces. Those gates remain
open. The focused `f5c_` suite passes 147 tests. No full library suite,
benchmark, or F5e matrix was run. Work remains primary-only with no independent
reviewer, as explicitly requested by the user. Keep the checkpoint local and
unpushed until the counter-contract choice and its records are resolved.

## Counter-invariance option B implementation checkpoint (2026-09-24)

The user selected option B: preserve §36's counter invariance by adding a
canonical preordering schedule while keeping the exact comparison count for
the prescribed stable mergesort. The design is recorded in
[`2026-09-24 F5c normalization counter invariance`](../design/2026-09-24-f5c-normalization-counter-invariance-addendum.md).
This decision supersedes the earlier instruction above to wait for the
counter-contract choice. The mixed-height ordering/counter subgate is now
implemented; broader F5c gates remain open.

`crates/yu-solver/src/f5c_normalization.rs` now canonicalizes both child-key
lists and each same-height descriptor group before the existing stable
mergesort. Inputs of three through eight keys use stable insertion
preordering; one- and two-key inputs need no preordering. Larger sets use
iterative in-place MSD radix distribution over big-endian
`u32` bytes, with a low end-of-descriptor symbol for variable descriptor
lengths. The counter-measured mergesort and following equality/dedup checks
remain unchanged in ordering and semantics. Key-word comparison accounting
now increments only for fields actually examined. The normalization index has
13 physical Vec lanes: the prior 11 plus an explicit radix-frame stack and a
771-`usize` workspace; small preorders allocate neither new lane.

Focused evidence: the five-root rotation now produces the same exact count
(18/18) and complete `NormalizationStats`; reversing a five-member Union also
preserves its complete stats. Coverage includes >8-key unsigned byte ordering
across `u32` boundaries, variable-length descriptor-prefix ordering, physical
scratch-lane reconciliation, radix scratch-counter overflow before allocation
or partition, and the existing height-major/stack-depth/§44 representative
checks. All 15 normalizer-module tests pass. The full single-threaded `f5c_`
filter passes 152 tests, and `cargo check --workspace`,
`cargo fmt --all -- --check`, and `git diff --check` pass. No full library
suite, benchmark, or F5e matrix ran. Static work analysis keeps the extra
preordering within `O(N+W)` and the existing `O(N+W+C)` total bound; timing was
not measured because the selected behavior does not depend on a timing result.

Work remained primary-only at the user's direction, so there was no
independent reviewer; this is not represented as independent certification.
The subgate is checkpointed and pushed on `origin/yulang3` at
`fc34f127` and `e81b9e84`; the worktree is clean. This does not close F5c/F5e,
the full single-threaded solver suite, or complete resource/public-observation
certification. Next: continue the remaining stack-safe producer/finalizer
work within the current F5b callback/accounting boundary. Do not add the
unapproved indexed `yu-types` API or move solver-owned allocation outside the
existing callback; stop for a separately reviewed decision if that boundary
cannot support the required iterative construction.

## Iterative summary-to-draft materialization checkpoint (2026-09-24)

`F5cSummaryStore::node_iterative` and `materialize_summary` were already
iterative graph walks. The root-local post-summary conversion was still
recursive: `F5cGeneralizer::materialize_positive` and
`materialize_negative` recursively rebuilt boxed Function, Union, and
Intersection trees while replacing `Shared` references. That conversion now
lives in `crates/yu-solver/src/f5c_materialization.rs` as an explicit
polarity-tagged task/value walk. It preserves child order and effect fields,
uses the same summary mark callback for `Shared` nodes, and leaves the §44
representative and Q/R logic unchanged. Two distinct task/value lanes were
added to the existing walker capacity observer and independent ledger so they
remain accounted while nested summary materialization uses its own lanes.
`lib.rs` is 27,700 lines, 112 fewer than before this extraction.
The implementation and synchronized records are checkpointed in commit
`68952716`.

The sidecar test builds and consumes alternating Function chains of depths
2,048 (positive root) and 2,049 (negative root) on a 64 KiB thread stack. It
checks lane requests, growths, peaks, release, and independent-ledger
reconciliation. The existing
active-conflict tests exercise the production generalizer wrapper. Verification
passes: `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (153 passed),
`cargo check --workspace`, `cargo fmt --all -- --check`, and `git diff --check`.
No benchmark or F5e matrix ran. The extra producer work is O(N), with two
O(N)-capacity worklist lanes replacing recursive traversal; draft output-tree
storage remains outside this newly isolated lane accounting and is still an
open F5c accounting item.

This closes only boxed-tree summary-to-draft materialization recursion. Other
recursive generalizer paths remain in `term_value_rows`, guarded-owner
search, replay, recursive-owner reference closure, incidence collection, and
Q first-occurrence traversal; cloning and destruction of the boxed trees also
remain recursive. `finalize_generalization_draft_raw` still recursively
constructs closed nodes inside the §24 higher-ranked callback. F5b §6 does not
permit solver-owned scratch allocation/mutation there, and transaction-branded
`Draft*Id<'tx>` values cannot be stored in solver-owned slots across the
callback. The indexed `yu-types` construction API is still Draft and was
reviewed as underspecified. Therefore end-to-end stack-safe closed-tree
construction cannot proceed without a new design/review/approval boundary;
do not implement Candidate B or claim stack-safety/F5c closure on this slice.

The complete `yu-solver` library suite was not repeated: the most recent
single-threaded attempt stopped after more than seven minutes in
`f4_unbounded_cycle_scale_4k_keeps_direct_frontier_linear`, with no passing
suite result; the earlier linearity discrepancy remains unresolved. This
checkpoint is primary-only per user direction and has no independent review.
F5c and F5e remain open. Continue only with boundary-compatible F5c slices.
The indexed `yu-types` finalization API remains unapproved and must not be
implemented without a new reviewed design and explicit user approval.

## Iterative producer-analysis traversal checkpoint (2026-09-24)

The recursive producer-side walkers for guarded-owner search, recursive-owner
reference closure, polarity incidence, Q first-occurrence ordering, and Term
value-row collection now use the private explicit-stack visitor in
`crates/yu-solver/src/f5c_tree_analysis.rs`. It preserves DFS order: Function
argument before result, Union/Intersection input order, and first-seen row
ordering. Function children still acquire the guarded bit; Term traversal still
ignores Function effects and skips unavailable Term views as before. No change
was made to replay, quantifier/R rebinding, §44 projection, or finalization.

The `AnalysisTasks` lane is included in the generalization walker's physical
capacity accounting and independent test ledger. A parity test checks both
polarities, incidence sets, guarded detection, recursive-owner references, and
first occurrence. Positive and negative boxed Function chains plus a deep
Term Function chain each traverse on a 64 KiB stack. The boxed inputs are
intentionally forgotten by the small-stack test after traversal so recursive
destruction does not obscure the traversal result; clone/drop remain separate
open stack-safety work.

`lib.rs` is 27,542 lines, 158 fewer than before this extraction; the traversal
is isolated in a 297-line private module with a 195-line sidecar test. Checks
pass: `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (155 passed), the same
filtered suite with `--no-default-features` (155 passed),
`cargo check --workspace`, `cargo fmt --check`, and `git diff --check`. The
unfiltered no-default-feature library suite was started but interrupted in the
known broad F4 scale area; it provides no passing-suite evidence. No benchmark
or F5e resource matrix ran; measurement budget consumed: zero.
The implementation and records are committed and pushed at `2366de39` on
`origin/yulang3`.

Work remained primary-only at the user's explicit direction, with no
independent reviewer. This closes only these producer-analysis walks. Recursive
binder substitution in `build_inner`, boxed-tree clone/drop, finalization under
the §24 callback, complete ineligible-variable closure, non-pure Function
effects, per-use failure atomicity, and the wider F5c/F5e resource/public-
observation gates remain open. Keep the approved §24/F5b callback boundary and
the §44 first-member representative unchanged; do not implement the unapproved
indexed `yu-types` API. The next bounded stack-safety slice is iterative Q/R
binder substitution with its own accounted lanes and small-stack parity tests.

## Iterative candidate-replay checkpoint (2026-09-24)

Candidate replay no longer recursively rebuilds F5c boxed trees. The new
private `crates/yu-solver/src/f5c_replay.rs` worklist preserves the prior
polarity rules: unprotected positive-only variables become `Bottom`,
unprotected negative-only variables become `Top`, and protected variables
remain. Function arguments/results retain depth-first order, Function effects
are canonicalized as before, and Union/Intersection member order is unchanged.
All production replay callsites now propagate checked task/value-lane
exhaustion as `IdentityExhausted`; candidate membership and §44 projection were
not modified.

The `ReplayTasks` and `ReplayValues` lanes are included in the walker resource
summary and independent test ledger. Shallow positive/negative fixtures assert
exact replay results, including protected rows and nested product order.
Positive and negative depth-4,096 Function chains replay on a 64 KiB stack;
the test iteratively consumes the outputs and checks each canonical effect,
eliminated leaf, lane peak, release, and independent ledger reconciliation.
`lib.rs` is 27,508 lines, 34 fewer than after the prior extraction; replay code
is isolated in a 211-line private module and 209-line test sidecar.

Verification passes: `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (157 passed), the same
filtered suite with `--no-default-features` (157 passed),
`cargo check --workspace`, `cargo fmt --check`, and `git diff --check`. No
benchmark or F5e matrix ran; measurement budget consumed: zero. The full
yu-solver library suite was not run to completion; do not infer broader suite
success. Work remained primary-only at the user's direction, without an
independent reviewer.

At the resumed continuation on 2026-09-24, Git metadata was writable again.
The focused verification rerun passed; implementation and synchronized records
were committed as `da9097db` and pushed to `origin/yulang3`. The next bounded
stack-safety slice is iterative Q/R binder substitution with accounted
scratch and exact small-tree parity.

This closes only candidate replay recursion. It does not certify complete
co-resident output-tree accounting: the two worklist lanes are accounted, but
the transformed boxed payload is a separate open F5c accounting item. Recursive
binder substitution in `build_inner`, clone/drop, closed finalization within
the §24 callback, ineligible-variable rejection, effect closure, per-use
failure atomicity, and F5c/F5e resource/public-observation gates remain open.
The next bounded stack-safety slice is iterative Q/R binder substitution with
accounted scratch and exact small-tree parity; keep the finalizer callback/API
unchanged.

## Iterative generalization Q/R substitution checkpoint (2026-09-24)

Under §§8, 9, 14, and 33, the recursive local `positive`/`negative` rewrites
at the end of `F5cGeneralizer::build_inner` now live in the private
`crates/yu-solver/src/f5c_binder_substitution.rs` task/value transform. It
preserves R-before-Q mapping, polarity-specific elimination to `Bottom`/`Top`,
Function polarity and canonical effects, Union/Intersection order, and the
existing predicate-then-lower/upper processing order. No binder assignment or
eligibility policy changed.

`BinderTasks` and `BinderValues` are part of the existing generalization walker
resource summary and independent ledger. Exact positive/negative fixtures
cover Q, R, both polarity extremes, nested Functions, and ordered products; an
unmapped variable remains `IdentityExhausted`. Both polarities also transform
4,096-deep Function chains on a 64 KiB stack, and the test iteratively checks
all outputs, lane peaks/release, and independent-ledger reconciliation.
`lib.rs` is 27,419 lines, 89 fewer than at the candidate-replay checkpoint;
the transform is isolated in a 230-line private module and a 240-line test
sidecar.

Verification passes: `cargo fmt --all -- --check`,
`cargo check -p yu-solver --tests`, the focused substitution tests (3 passed),
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (160 passed), the
same filtered suite with `--no-default-features` (160 passed),
`cargo check --workspace`, and `git diff --check`. The full solver library
suite was not run to completion. Static cost is O(N) visits per transformed
tree; each invocation adds task/value worklists with O(N) worst-case capacity.
No benchmark or F5e matrix ran; measurement budget is zero. The work remained
primary-only at the user's direction, without independent review.

This closes only recursive Q/R rewriting in `build_inner`. The task/value
lanes do not certify co-resident boxed output payload; clone/drop and closed
finalization within the §24 callback remain open, as do the other F5c/F5e
resource/public-observation gates. Preserve the approved §24/F5b boundary and
do not add the unapproved indexed `yu-types` API. The implementation and
records are checkpointed and pushed as `a41b9875`; map the next boundary-safe
stack-safety path before expanding scope.

## F5c raw recursive-bound materialization ownership checkpoint (2026-09-24)

The final `build_inner` materialization pass previously cloned every raw R
lower/upper boxed tree before passing the clone to the already iterative
materializer. Those `F5cPositive`/`F5cNegative` clones recursively traversed
the boxed tree and kept the original and clone co-resident. The pass now moves
each bound out with `mem::replace`, materializes it in place through the same
`DraftMaterializeTasks`/`DraftMaterializeValues` lanes, and preserves lower
before upper processing. The map is local to `build_inner` and is discarded on
failure; successful draft structure and Q/R decisions are unchanged. No boxed
representation or finalizer API changed.

A 4,096-deep positive and negative bound pair passes through the shared move-
and-materialize helper on a 64 KiB stack. The test iteratively checks child
order and canonical effects, then reconciles both existing materialization
lanes against the independent ledger. Verification passes: formatting,
`git diff --check`, `cargo check -p yu-solver --tests`,
`cargo test -p yu-solver --lib f5c_ -- --test-threads=1` (161 passed), the
same filtered suite with `--no-default-features` (161 passed), and
`cargo check --workspace`. The full solver library suite was not run to
completion. This removes one deep-clone path; static transform complexity stays
O(N), and peak live bound payload no longer includes the redundant clone. No
benchmark or F5e matrix ran; measurement budget is zero. Work remained
primary-only at the user's direction, without independent review.

This does not make derived `Clone` or recursive destruction of arbitrary
boxed F5c trees stack-safe. Candidate replay's remaining clone arms handle
leaves after branching nodes are explicitly traversed; boxed output drop and
other deep-tree ownership paths remain open. Do not claim full clone/drop or
F5c/F5e closure. The next step is to map whether deep destruction can be made
safe without changing the approved boxed representation or §24 boundary. The
implementation and records are checkpointed and pushed as `992df956`.

## Owned boxed-draft destruction boundary map (2026-09-24)

This was a primary-only M1, read-only boundary investigation at the user's
direction. Convergence required identifying the owned-tree cleanup points and
whether an iterative cleanup at one point would close a useful production path
under current F5b/F5c ownership and resource rules. No code change was
justified.

`F5cPositive` and `F5cNegative` derive `Clone` and own recursive children in
`Box` and `Vec`; neither enum has a custom destructor. Ordinary destruction of
a deep Function chain is therefore recursive. The iterative replay,
Q/R-substitution, materialization, and normalization walks remove recursive
visitation, not recursive destruction:

- `f5c_replay::replay` borrows its input but builds boxed output in its local
  values vector. On a checked error, unfinished tasks and partial output
  values are ordinarily dropped. Its 4,096-deep small-stack test forgets both
  input and output trees after checking them.
- `f5c_binder_substitution::substitute` and
  `f5c_materialization::materialize_iterative` consume their owned trees into
  local task/value vectors. Successful results leave as ordinary boxed trees;
  on an error, remaining owned tasks and partial values are ordinarily
  dropped. Their deep tests avoid output destruction; the raw-bound test
  explicitly forgets the moved bounds after validating them.
- `f5c_normalization::collect_drafts` moves nested trees into its iterative
  `Walk` stack and `rebuild` reconstructs boxed output. An error can leave
  nested owned values in the normalizer's work/output vectors, which then use
  ordinary drop. On success, normalized component drafts remain boxed.
- `execute` retains all normalized `generalization_drafts` while
  `finalize_generalization_draft_raw` borrows each plan. Its local positive and
  negative constructors recurse through every Function/Union/Intersection
  child inside the existing `finalize_scheme` callback. A finalization error
  (including the test injection before tree traversal) exits through `?` and
  drops the still-owned draft vector; after successful finalization the vector
  also drops at scope exit. Thus fixing only draft destruction does not make
  this path stack-safe: deep finalization is reached first on success.

An iterative owned-tree drain is expressible without changing the boxed enum,
but a production-safe drain needs an O(depth/frontier) worklist. Its checked
growth can itself fail after ownership has been partially peeled; returning at
that point leaves a remainder whose ordinary destruction is recursive, while
leaking it is not an acceptable recovery policy. No existing lane represents
this destruction scratch or defines that partial-drain failure contract. A
local helper would also leave the other task/value, normalizer, finalizer, and
component-vector drop sites unchanged. Adding such a helper in isolation would
therefore not close a bounded end-to-end path, and would add a new resource and
failure-policy surface without a design decision.

The finalizer is a separate hard boundary. F5b §6 and the current finalization
accounting contract do not authorize persistent solver-owned scratch mutation
inside the higher-ranked callback, and transaction-branded `Draft*Id<'tx>`
values cannot be retained across it. The proposed indexed `yu-types` API in
`notes/design/2026-09-23-f5c-indexed-finalization-accounting-boundary-draft.md`
remains explicitly unapproved and its own status says it is not ready for
approval. The §24 callback/API and boxed representation were left unchanged;
no unsafe custom `Drop`, `mem::forget` production path, or partial cleanup lane
was introduced.

Outcome: no bounded, failure-safe production destruction slice was found under
current authority, so this goal ends as a no-code map rather than a stack-safety
claim. The precise next design decision is how to own and account iterative
draft construction plus destruction across finalization: either a reviewed,
approved `yu-types`-owned indexed finalization boundary with explicit
transaction/peak/failure contracts, or a separately reviewed private
representation/ownership change that avoids recursive boxed destruction.
The current indexed-finalizer Draft is not approval-ready; do not implement it
or claim F5c/F5e closure. No tests or benchmarks were run for this record-only
checkpoint.

## F5c ineligible-variable gate reconciliation (2026-09-24)

The stale “complete ineligible-variable closure remains open” residual in the
earlier iterative producer-analysis checkpoint is superseded by the current
source/test audit. Under §23, expanded rows enter the generalizer's first-
occurrence `order`, including rows reached through shared summaries when
materialized. Eligibility requires level greater than zero and exclusion from
the computed non-generic closure. Positive-only/negative-only elimination,
retained R, and assigned Q are all eligibility-filtered. Before binder rewrite,
`reject_unclassified_rows` rejects observed rows outside eligible/Q/R. The
binder transform independently returns `IdentityExhausted` for an unmapped
variable, so no ineligible row silently becomes Bottom or Top.

Coverage exercises level-zero ineligible variables in both polarities inside
Function children, non-generic targets in both polarities, direct non-generic
rejection, unmapped-variable rewrite, and component failure with no installed
scheme, closed candidate, or retained closed-byte change. Verification on
2026-09-24:

- `cargo test -p yu-solver --lib f5c_generalization_rejects -- --test-threads=1`
  — 3 passed;
- `cargo test -p yu-solver --lib f5c_component_rejection_installs_no_scheme_or_closed_candidate -- --test-threads=1`
  — 1 passed;
- `cargo test -p yu-solver --lib f5c_binder_substitution_rejects_unmapped_variables_and_releases_lanes -- --test-threads=1`
  — 1 passed;
- `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` — 161 passed;
- `cargo test -p yu-solver --lib --no-default-features f5c_ -- --test-threads=1`
  — 161 passed.

This closes the §23 ineligible-variable rejection subgate for the represented
F5c variable sources and its component no-partial-publication path. It does not
close all generalization semantics, stack-safe finalization/destruction, the
full §3 accounting/measurement gate, or F5c/F5e certification. No production
code changed; this audit had no independent reviewer under the user's
primary-only direction. The exact-alpha/normalization decision and other gates
remain separate.

## Callback-local iterative finalizer feasibility map (2026-09-24)

This was a primary-only M1 architecture feasibility check against authoritative
F5 §§14, 24, 26 and F5b's finalization accounting amendment §§2 and 6. No code
change was made; convergence required checking handle lifetime, transaction
failure, joint peak accounting, and post-finalization draft destruction.

A local iterative traversal is compatible with the higher-ranked callback's
handle lifetimes in principle: task/value vectors declared inside the
`finalize_scheme` closure could hold `Draft*Id<'tx>` values and drop before the
closure returns, so no branded handle escapes. The current recursive helper
already allocates per-Union/Intersection vectors of draft IDs inside that same
callback for `positive_union`/`negative_intersection`. Checked worklist growth
could return `IdentityExhausted`; the existing finalizer transaction then
rolls back the overlay, preserving failure atomicity.

That establishes traversal/lifetime feasibility, not an authorized complete
implementation. The iterative task/value vectors would add solver-local
capacity-managed heap scratch. F5b §6 freezes non-`yu-types` resource lanes
for the callback, while `ClosedTypeAccountingCheckpoint` reports only
`yu-types` retained-before/after and peak bytes. It has no callback-local
scratch or event-time combined-peak field. Capturing the worklist's maximum
outside the callback and adding it to `peak_bytes_during_call` is not exact:
the solver worklist is dropped when the callback returns, while later
`yu-types` validation/planning/reservation may produce that checkpoint peak.
Adding those independent maxima would violate the fixed-baseline temporal
accounting rule. No current lane can be updated during the callback to record
the actual co-resident maximum.

Even a stack-safe callback traversal would leave the borrowed boxed
`GeneralizationDraft` to be recursively destroyed on both finalization success
and early error. That remains the separate ownership/drop blocker recorded
above. The indexed `yu-types` construction proposal remains Draft,
unapproved, and not ready for approval; the current API offers no approved
joint accounting protocol.

Outcome: callback-local worklists are lifetime-safe in principle and preserve
transaction rollback, but exact accounting and the subsequent deep-draft drop
are unresolved. No bounded implementation satisfies the active goal's full
contract under current authority. The next decision is whether to authorize a
new independently reviewed design round for a `yu-types`-owned iterative
construction/accounting boundary and an explicit draft-destruction strategy;
do not implement Candidate B or change §24 without that approval. No tests or
benchmarks ran for this read-only checkpoint.

## Property-oriented finalizer boundary map (2026-09-24)

The indexed-finalization Draft's new §8 compares three choices in terms of
preserved and lost properties: current recursive HRTB callback, local iterative
worklists inside that callback, and a `yu-types`-owned indexed transaction with
flat solver drafts. The key distinction is end-to-end stack safety: loops can
remove recursive visitation, but a nested boxed input still recursively drops
on both success and checked error cleanup. A flat representation is useful only
if it replaces the boxed ownership path through expansion, replay, Q/R rewrite,
normalization, finalization, and error cleanup.

The source also exposes callback-local Q/R handle arrays, recursive-bound
storage, and per-product child vectors that coexist with finalizer storage.
F5b's result checkpoint reports only `yu-types` bytes and §6 freezes non-
`yu-types` resource lanes; no explicit exclusion for these temporary
capacities was found. This is recorded as an accounting question, not a ruling
that the current counters are incorrect and not authorization to alter F5b.
It needs adjudication before any design claims exact whole-call peak evidence.

The property map is primary-authored, has no independent review, and changes
neither code nor §24. Candidate B remains Draft and unapproved. The next
decision is whether to preserve §24 and leave this gate open, or continue a
design-only pass toward a reviewed `yu-types`-owned indexed boundary (which
would require an explicit §24 change before implementation). A later producer
should live behind a dedicated module boundary; this map does not refactor the
already-large `lib.rs`.

## User product priority and bounded finalizer direction (2026-09-24)

The user now delegates the technical path choice: Yulang should match its
frozen Oracle on practical inputs and stay lightweight; pathologically deep,
large, or resource-intensive inputs may be rejected deterministically if
basic safety, accepted-input invariants, and no-partial-publication remain
intact. The durable rule is in `rules/design-authority.md` and passed a focused
independent spec audit. This permits choosing a bounded supported-input
envelope, but does not silently supersede narrower F5 authority.

A primary-requested Sol architect review recommends first pursuing a bounded
current-§24 implementation rather than the new indexed `yu-types` API. The
limit must prevent over-limit boxed values from being built in the first
place, then hold through replay, binder substitution, summary materialization,
normalization and finalization; rejecting only before finalization is too late
because destroying the rejected box tree may overflow. It also flags the
callback-local Q/R/bound/product vectors as overlapping `yu-types` storage
whose accounting is not represented by the current checkpoint. A bounded
stack-only path might avoid those allocations, but that remains unverified.

This is a conditional design direction, not an approved cap or implementation
gate. The source audit must enumerate every production tree constructor and
error exit, locate the earliest cheap pre-construction check, verify the public
failure surface and callback accounting, then draft a concrete gate for
independent spec/performance review. If that cannot preserve practical Oracle
behavior and safe cleanup without disproportionate machinery, reconsider the
indexed flat-graph fallback. Keep approved Q/R order, height-major
normalization, and §44's canonical first-member projection fixed.

## Bounded boxed-draft gate proposal (2026-09-24)

The focused source audit confirmed the main end-to-end stack boundary: iterative
F5c producers still create recursively dropped Box/Vec trees, and
`finalize_generalization_draft_raw` recursively consumes those trees inside the
unchanged §24 callback. `Term` inputs themselves are arena handles, so a guard
can be enforced while producing solver-owned draft values rather than while
dropping a deep source `Term`.

Sol's focused architect judgment: depth metadata plus a pre-normalization
height check is not enough unless every boxed-tree transition checks before
constructing a parent and partial values remain bounded. A depth cap alone also
does not bound shallow width or repeated expansion of shared summaries. Sol
recommended a low-hundreds depth ceiling, selected through 64 KiB small-stack
tests of finalization and both success/error destruction; keep §24 if those
checks pass, otherwise fall back to a flat/indexed ownership path. Sol also
recommended reusing `IdentityExhausted` for the scoped rejection rather than
adding a public variant absent a confirmed consumer need.

The primary drafted
[`F5c bounded boxed-draft gate`](../design/2026-09-24-f5c-bounded-boxed-draft-gate-draft.md)
for review. The first M2 pass found blocking gaps: budget ownership across the
memo-clear/normalization boundary; insufficient check-before-parent/error-drop
proof; ambiguous pending-lane meaning; overbroad atomicity wording; and no
pre-scheduling charge for shared-summary expansion. The primary accepted those
findings.

A second Sol adjudication, after the broader work/byte budget failed two M2
review rounds, selects a depth-only subgate as the lightest credible progress.
It keeps the current boxed representation and §24 callback, proposes maximum
structural depth 128, and requires a pre-parent check at every producer so an
over-depth tree is never built or dropped. It explicitly does not bound shallow
width, repeated shared-summary expansion, aggregate work, or total memory;
those remain separate F5c/F5e resource gates. This is partial stack-safety
progress, not general resource protection or F5c/F5e closure.

The new Draft names all current production tree builders and error/drop
boundaries, preserves §§24/44 for accepted depths, and narrows the §14
clarification to the stack-safety sentence rather than claiming §14 promised
unlimited depth. Sol also confirmed the narrow atomicity wording: every member
in a component is finalized before its scheme-install loop, and consuming
`run(self)` returns no `SolvedModule` on any error; this is no partial public
result, not rollback of private staged arena bytes. The proposed 128 boundary
is unverified until small-stack tests run after approval.

Focused M2 `spec_auditor` and `performance_auditor` delta reviews completed on
2026-09-24 with no blocking or major findings. The spec review closed the
construction/error-drop proof, the narrow §14 authority boundary, and the
depth-2,048 test approval gate. The performance review closed the extra-scan
concern; its minor finding clarified that `push_node` may copy child IDs and
grow flat scratch before detecting excessive height, so rejection is not a
zero-cost failure path. Sidecar size, successful-path cost, all-producer
coverage, and 64 KiB stack safety remain implementation checks. At that point
the proposal was marked Reviewed, not Authoritative. A subsequent source audit
found and corrected a mismatch between §2's childless-node depth and §3's
induction statement; the focused spec delta reviewer accepted the latter as a
major finding. The correction now uses the childless/nonempty rule
consistently; a fresh focused review found no blocking or major issue and its
minor stale-status wording finding was closed. The proposal is again marked
Reviewed, but remains non-Authoritative pending explicit user approval.

## Depth-measure source-audit correction (2026-09-24)

After the focused reviews, a direct source reread of
`Normalizer::push_node_at` found a detail the proposal's first depth definition
did not state exactly: height increments only when `child_count != 0`. Thus a
childless node is height zero; this includes an empty Union/Intersection if
one reaches normalization. The Draft now follows the implementation's exact
measure (otherwise a nonempty product is `1 + max(child heights)`). The first
focused spec delta review found that §3's separate induction sentence still
used the nonempty formula for every parent. The primary accepted and repaired
this major consistency finding; the fresh focused spec delta review found no
blocking or major issue. Its minor stale-status wording finding was closed in
the proposal metadata. The proposal remains unapproved; no code or tests have
changed.

## Fast resume card (2026-09-24)

### Exact checkpoint

At handoff start, branch `yulang3` was clean and matched `origin/yulang3` at
`ccd39524` (`docs(f5c): align depth invariant with normalizer`). This handoff
update is the only requested change. The user asked for a handoff, commit, and
push before leaving; no implementation was authorized by that request.

### Active gate and authority

The repository rule now records the user's product priority in
`rules/design-authority.md`: preserve Oracle-compatible behavior for practical
inputs and keep the successful path lightweight; proportionately reject
pathological inputs rather than building exhaustive recovery, while retaining
basic safety and atomic public publication.

The current proposed F5c slice is
[`2026-09-24-f5c-bounded-boxed-draft-gate-draft.md`](../design/2026-09-24-f5c-bounded-boxed-draft-gate-draft.md).
It is Reviewed but not Authoritative. Its concrete proposal is maximum
`Normalizer::Node.height` 128; childless nodes (including empty products, if
encountered) have height zero, and nonempty nodes have one plus the deepest
child. A prospective node above 128 returns `IdentityExhausted` before that
parent is built. The children and flat normalization scratch may already have
been traversed/allocated on the failure path.

The user previously delegated the practical route and accepted pathological
input rejection in general. The exact 128 / `IdentityExhausted` boundary has
not been explicitly approved in the recorded conversation. Repository policy
requires that concrete boundary's approval before changing the existing §14
deep-chain success contract or implementation. The goal tracker is blocked on
that approval. If the user approves, first record the approval and the narrow
§14 supersession in the design/index/task records, then begin implementation;
if not, revise only the affected proposal and return it to focused review.

### What the proposal keeps and changes

- For depth-at-most-128 inputs that otherwise complete, preserve current
  polarity, Q/R classification, binder order, normalization order,
  §24 finalizer API, and §44 normalized-Union representative behavior.
- Above depth 128, behavior changes from attempting deeper generalization to
  deterministic `IdentityExhausted`; no truncation or approximation.
- A failing `run(self)` returns no `SolvedModule`; this does not promise rollback
  of private state or earlier private component installation.
- This is only a stack-depth gate. It does not bound shallow width, repeated
  shared-summary expansion, aggregate work, or total memory. F5c and F5e remain
  open.

### Review and implementation evidence

Focused M2 spec and performance reviews found no blocking/major findings after
the depth invariant repair. The performance minor is recorded above: the
normalizer may copy child IDs and grow flat scratch before detecting excess
height. The fresh spec delta review confirmed the childless/nonempty height
rule; all review status is in the linked proposal. No code/test was changed and
no benchmark was run for this gate. The prior full-suite evidence in this
handoff does not verify the proposed 128 boundary.

After approval, keep `lib.rs` additions localized to its current owners; use
the existing `f5c_*` modules for their owned producer paths instead of a broad
refactor. Before calling the slice complete, verify every production boxed
producer and test both polarities: depth 128 through normalization, the
unchanged §24 finalizer, and destruction on a 64 KiB stack; checked-error
cleanup at 128; and depth-129 rejection before parent construction with safe
child cleanup. Check the dynamic lane accounting after adding depth metadata,
including `size_of::<F5cWalkValue>()`. Do not change the existing depth-2,048
success witness or related 2,048/4,096 helper expectations until approval.
Then run focused tests first and the single-threaded library suite once at the
coherent gate boundary (`cargo test -p yu-solver --lib -- --test-threads=1`).

### Immediate next action

Wait for explicit user approval of maximum `Node.height` 128 and
`IdentityExhausted` above it. Do not begin code or alter the depth-2,048 test
before that approval. After approval, promote the reviewed proposal to
Authoritative, update the task/design records, implement only this stack-safety
slice, and checkpoint/push the coherent verified slice promptly. Do not claim
F5c or F5e closure.

## Candidate depth-256 stack probe (2026-09-25)

This later probe supersedes the preceding 128/64 KiB candidate note. The user
approved a bounded compiler support envelope and suggested evaluating 256;
they also asked to slim unnecessary implementation code if that route works.
No exact caller-stack floor or implementation behavior has been approved yet.

The focused probe is
`tests::f5c_depth_limit::f5c_candidate_depth_256_finalizes_and_drops_on_small_stack`.
It builds one positive and one negative depth-256 Function draft, invokes the
unchanged §24 finalizer, then normally drops the closed result, input draft,
and finalization session.

Observed results:

- Debug test build, 64 KiB stack: stack overflow during finalization.
- Debug test build, 256 KiB stack: stack overflow.
- Debug test build, 512 KiB stack: pass.
- Optimized release test build, 64 KiB stack: pass.

Commands used:

```text
cargo test -p yu-solver --lib f5c_candidate_depth_256_finalizes_and_drops_on_small_stack -- --test-threads=1
cargo test -p yu-solver --lib f5c_candidate_depth_256_finalizes_and_drops_on_small_stack --release -- --test-threads=1
```

The passing debug witness currently uses a 512 KiB thread. The release result
is an observed profile-specific result, not a cross-platform guarantee. The
test is only a finalizer/destructor feasibility probe: it does not exercise the
production depth guard, all boxed-tree producers, depth-257 rejection, checked
error cleanup, or route/publication atomicity.

The remaining decision is the supported execution-stack envelope. A fixed
depth-256 limit is lightweight for ordinary stacks but does not protect an
unusually small unoptimized caller stack. Keeping a 64 KiB unoptimized-stack
guarantee would require a much lower limit or a larger iterative finalization
and destruction redesign. Continue only after resolving that exact boundary;
keep the production worktree unchanged until then. F5c/F5e closure remains
open.
