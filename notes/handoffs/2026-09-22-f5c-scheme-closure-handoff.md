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

## Flat indexed stack-independent design direction (2026-09-25)

The user chose to explore deep F5c support with explicit stacks rather than a
fixed structural-depth threshold. This authorizes design work only; the exact
§24 indexed API and resource/work boundary remain subject to reviewed design
and explicit approval before implementation.

A Sol architect review recommends keeping F5c drafts flat and solver-owned
from the first potentially deep producer through Q/R rewriting, replay,
substitution, materialization, normalization, component staging, finalizer
input, and error cleanup. Pair this with a `yu-types`-owned indexed finalizer
transaction that validates IDs/spans/Q/R/reachability/cycles, constructs
closed nodes with private explicit worklists, and preserves the existing
transaction rollback/atomic commit. A finalizer-only loop over the current
boxed drafts is insufficient: both successful destruction and checked-error
cleanup can still recursively drop the boxed source or partial task/value
trees. The current normalizer likewise cannot hand off by rebuilding boxes.

Preserve existing practical-input scheme semantics, Q/R and normalized order,
component install order, §44's first canonical Union member as the sole public
representative, and atomic publication of that fact plus all private member
constraints. The flat representation removes the depth-cap and caller-stack
calibration proof, but does not remove producer parity, index validation,
resource/peak accounting, transaction rollback, route atomicity, or work
bounds. Existing F5 §26/§34 resource contracts remain authoritative. A
deterministic charged-work limit covering shared expansion, R replay, ranking,
and normalization is unresolved; do not imply pathological-work protection
or F5c/F5e closure until that gate is settled.

The proposal is recorded in
[`2026-09-25 F5c flat indexed stack-independent draft`](../design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md).
The initial M3 review and two focused delta rounds are adjudicated; no assigned
blocking/major finding remains. The proposal is Reviewed, not Authoritative.
On 2026-09-25 the user approved first-stage investigation only: inspect
practical source inputs, map charge sites, and gather focused scale/resource
evidence. This does not authorize a production-path prototype, API
implementation, or semantic change. The numeric support boundary must be
independently reviewed and separately approved before implementation. Keep
`lib.rs` as orchestration and isolate the eventual flat producer/finalizer
bridge in dedicated modules.

## First-stage flat/indexed resource investigation (2026-09-25)

The user authorized repository source/corpus inspection, charge-site mapping,
and focused scale/resource evidence only. The proposal remains Reviewed, not
Authoritative; no public API, numeric support boundary, F5 clause
supersession, or production implementation is approved.

The stable-core corpus has 73 cases, including 16 public-signature fixtures.
The public fixture `main.yu` plus expected `signature.toml` files total 4,513
bytes; all stable-core `main.yu` files total 10,258 bytes. These measure source
surface, not inferred graph size/work. The runtime corpus has 10 cases but is
not a type-size distribution, and the repository has no compiler CLI/corpus
harness to collect expanded F5c metrics. No external-source representativeness
claim follows from these fixtures. The Rust test suite mostly uses synthetic
builders.

Current repeated-work owners and required charges are recorded in §13 of the
draft. In short: actual shared-summary incidences; root-local task/edge and
eligibility/trace visits; binder-substitution tasks; replay/product candidates,
structural comparison visits and copied elements; R fixed-point rounds and
owner replays; normalization admission dimensions; and, if implemented, direct
dense indexed-finalizer passes. The finalizer's proposed `O(V+E+B+Q)` bound is
conditional on checked direct Q/R ordinals, scanning all IDs/spans, iterative
three-color DFS, and bounded plan/commit passes. The existing F5a callback's
ordered-subset R contract must not be narrowed.

Existing synthetic depths include 1,024 direct rows, 2,048 alternating
Function levels, and 4,096-deep replay/materialization/tree-analysis paths.
These establish selected traversal feasibility and accounting behavior, not a
complete numeric work/size envelope. The current single-threaded F5c filter
passed 162 tests (0.64 s); a `f5c_deep` filtered run passed 2 tests. No
benchmark samples or peak-memory measurements were taken. No code source was
changed; numeric thresholds remain unsupported.

The next-action note from the initial corpus/charge-site audit was to prepare a
test-only scale probe. The normalizer-only follow-up below fulfills that first
measurement slice; shared-summary, replay/substitution, R fixed-point, and
indexed-finalizer work families remain unmeasured. F5c/F5e remain open.

### Normalizer-only scale probe follow-up

The primary added one ignored test-only probe at
`crates/yu-solver/src/tests/f5c_resource_probe.rs`; the sole `lib.rs` edit is
the test-module declaration. It exercises current normalizer shapes only:
Function chains, unique and duplicate-heavy Unions, and multiple roots. The
reproducible command is:

```text
cargo test -p yu-solver --lib f5c_resource_probe_scale_families -- --ignored --nocapture --test-threads=1
```

Selected largest observations:

| Shape | Raw nodes | Child slots | Work counter | Tracked lane peak |
|---|---:|---:|---:|---:|
| Function chain, depth 4,096 | 8,193 | 8,192 | 28,673 word comparisons | 1,972,544 bytes |
| Unique Union, width 1,024 | 1,025 | 1,024 | 24,572 word comparisons | 293,224 bytes |
| Duplicate Function Union, width 1,024 | 3,073 | 3,072 | 1,023 duplicates; 56,312 word comparisons | 547,176 bytes |
| Independent roots, count 128 | 128 | 0 | 1,150 word comparisons | 24,952 bytes |

“Raw nodes” are pre-dedup normalizer nodes. “Tracked lane peak” covers the
normalizer's counted vectors only; nested allocations in boxed inputs and
outputs are omitted, so it is neither total memory nor a flat-path forecast.
The probe says nothing about shared-summary path expansion, replay,
substitution, R fixed-point work, or indexed-finalizer scratch. It is a
primary-authored diagnostic, not independently reviewed or a numeric limit.

The probe ran three times while its test-only reporting/assertions were
finalized; all runs passed, one initial warning was fixed, and no timing sample
was collected. The regular F5c filter passes 162 tests with the probe ignored.
Next: inspect existing test-visible counters for shared-summary and R/replay
work. Avoid production instrumentation unless a narrow test-only observer is
needed and separately reviewed.

### Shared-summary and replay probe follow-up

The same ignored test-only probe now also constructs a binary shared-summary
DAG and a deep replay chain. At DAG depth 12, the memo holds 13 unique nodes
and 24 child edges, while materialization creates 8,191 output nodes and 8,190
edges. The materializer requested 12,286 task slots; the tracked task-lane
peak was 512 bytes. This demonstrates path expansion in the current
boxed-output route, not an externally representative input or a proposed
flat-DAG output size. The lane peak omits the materialized tree and other
co-resident storage.

At replay Function depth 4,096, the existing lanes report 12,289 task-slot
requests and 8,193 value-slot requests, with lane peaks of 131,072 and 262,144
bytes. Successful task/value slot requests reflect scheduled entries, but not
all comparison, copy, or owner-check work. Static inspection of
`F5cGeneralizer::build_inner` shows cumulative replay lane accounting can
include repeated R-bound replay, but there is no direct count for R rounds,
candidate clone/retain operations, per-owner checks, trace-hop visits, or
reachability-frontier visits. R fixed-point cost therefore remains
unmeasured; substitution and finalizer work remain outside this probe too.

The source loop starts from eligible re-entry owners and only removes
candidates. Thus every non-final round removes at least one candidate and the
loop has at most `C + 1` rounds for `C` initial candidates. This is a
source-level bound, not an observed round count or per-round cost. A round can
still replay and inspect large bounds/traces, so the work meter must charge
rounds, owner and trace records, trace hops, candidate entries copied, and the
underlying replay/tree-analysis visits.

The combined manual probe command was invoked seven times: five completed
diagnostic runs and two compile attempts that exposed and fixed test-source
issues. One initial warning was also removed. No timing samples or process-RSS
measurements were collected. The single-threaded `f5c_` filter passed 162
tests with the probe ignored. These measurements are primary-authored and not
independently reviewed. They do not establish a numeric limit or complete
resource bound; no production behavior, API, or F5 clause changed. The last
diagnostic process invocation is deliberately not spent on a new R-loop
observer: source inspection already bounds round count, while a valid witness
would need new test-only counters and still would not establish a representative
per-round envelope.

Next: finish the source charge-site-to-meter map for R owner/trace work, then
obtain focused independent review before presenting any numeric boundary.
Numeric boundary and production implementation remain unapproved.

## Current F5c resume: source charge-site map (2026-09-25)

Current checkpoint before this record update: branch `yulang3`, clean at
`664e239e` (`test(solver): probe F5c resource dimensions`), already pushed to
`origin/yulang3`. The active goal remains the reviewed, user-approvable
stack-independent F5c design; no production implementation, API, numeric
limit, or F5 clause change is authorized.

The primary completed a source-level map in §13 of
`notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`. It
separates logical work charges from storage admissions and covers summary
memo construction/maintenance, root-local walks and traces, structural
candidate deduplication, tree analysis/non-generic closure, all R fixed-point
stages, replay/substitution/materialization, normalization/compaction, and the
proposed indexed finalizer. This is not a fresh independent review. The
monotone R candidate loop has at most C+1 rounds, but per-round cost remains
unmeasured. No extra diagnostic process was run; its remaining invocation
budget is unchanged.

Scope correction: the Function Cartesian product in
`InferenceSession::closed_parts` runs after closed-scheme finalization, so it
is outside the F5c draft meter and remains an F5e closed-DAG
instantiation/resource gate. Its checked multiplication does not bound pair
generation. The §44 per-use atomic rollback gate also remains separate.

Still unresolved: whether the single checked draft-work meter accumulates over
one whole solve or resets per component. Solve-wide accumulation gives a hard
ceiling on charged F5c draft work across the solve but can reject many small
components; per-component
reset admits those while aggregate work scales with component count. Numeric
limits, practical-input margin, finalizer implementation proof, and focused
independent review remain open. No tests or probes were rerun for this
documentation-only slice.

Next: obtain focused independent review of the source map and metering units;
then choose meter lifetime and a numeric support envelope with the user. Keep
`lib.rs` orchestration-only, preserve §44's first-member representative and
atomic route contract, and do not claim F5c/F5e completion.

## F5c source-map repair resume (2026-09-25)

Draft §§5/13 received a primary-only batched documentation repair addressing
one blocking and multiple major review findings. The prior M3 architecture
review covers the earlier architecture, not this source-map extension. The
repaired map now follows authoritative §36 `O(N+W+C)`, accounts privately for
the `O(N+W)` canonical preordering, and specifies scheduling, copy, epoch-wrap,
trace-scan, co-resident lane, and rollback obligations. Existing public
comparison counters retain their exact sites and semantics. Current probes
measure neither the proposed co-resident peak nor R-loop cost.

At that checkpoint, the next action was fresh focused independent M3 delta
review of §§5/13 and their record synchronization. Solve-wide versus per-component meter lifetime,
numeric caps, API shape, and implementation authority remain undecided. F5c
and F5e closure and §44 per-use rollback remain separate open gates. No
production code or probe changes are part of this repair.
Scheduled-versus-popped early mismatch, epoch-wrap, exhaustion restoration,
co-resident lane ledger, and §36 counter-oracle parity witnesses remain future
implementation/review requirements, not evidence gathered in this repair.

Second focused M3 source-map delta review accepted the stale §34 correction and
§36 `O(N+W+C)` boundary, then identified new BLOCKING/major omissions in both
epoch scans, reentry short circuits, normalization work, rollback journal and
restoration, and peak evidence. The primary repaired §§5/13 and synchronized
records. Another fresh focused M3 delta review is required; the earlier
architecture review did not certify this extension. Restoration allocation,
simultaneous peak, and repeated R-round work remain unverified (`C + 1` caps
rounds only). Future implementation must prove and witness both wraps, reentry,
normalization work/public-counter parity, exhaustion restoration without
fallible allocation, and the simultaneous lane ledger. None ran in this round.
Meter lifetime, numeric caps, API, production authority, F5e `closed_parts`,
and §44 per-use remain separate open decisions/gates. No gate completed.

Third focused M3 source-map delta round found no new charge-map omission. It
accepted a rollback journal-visibility gap as an open implementation
requirement: no fallible step may intervene between private mutation and its
undo record; partial admission failure needs prior state journaled. A focused
failure/exhaustion witness must cover the current `memo.admit` →
`observe_walker()?` → `admitted_keys` boundary. Undo-journal admission is
separate from final graph size. Allocation-free recovery and
invalidation/reinsertion capacity remain unproven; co-resident peak remains
unmeasured. Only source-map wording received these focused rounds; the full
draft remains a proposal without implementation authority. At that point,
fresh focused review of this documentation repair was next. Meter lifetime,
numeric cap, API, rollback, F5e, and §44 remain open; no gate completed.

## F5c source-map repair review and meter-lifetime recommendation (2026-09-25)

The follow-up documentation repair passed a fresh focused M3 delta review by
specification, compiler, and performance roles with no blocking, major, or
minor finding. This review covered the source-map repair and synchronized
records only; it did not certify the full proposal or close any implementation
gate. The draft status and §13 now record that distinction.

A read-only architect consultation recommends a single solve-wide work meter
as the simplest way to bound charged F5c draft work across components in one solve.
The tradeoff is explicit: it can reject a large ordinary solve made of many
small components; per-component reset preserves those components but gives no
solve-wide ceiling for charged F5c draft work across components in one solve.
The primary records this as a recommendation for user
approval, not a durable approved choice. No numeric cap or supported-input
boundary is inferred from the available repository evidence. At this earlier
checkpoint, the next action was focused independent review of the recommendation.
After that, the meter-lifetime choice can be presented separately from the
later numeric-boundary gate. The mutation-to-journal gap, allocation-free
restoration, and co-resident peak
remain unproved; no implementation authority exists.

The subsequent focused M3 review of the separate meter-lifetime recommendation
found major scope and approval-sequencing issues plus a minor wording issue; the
source-map repair's fourth focused review remains clean. This batched wording
repair awaited another focused independent review. The provisional solve-wide
choice would cap charged F5c draft work across components in one solve and
prevent component-count bypass, but might exhaust on many small components.
Per-component reset admits those workloads while aggregate charged F5c draft
work scales with component count. Indexed-finalizer-local work, F5e Function
products, §44 per-use routing, and physical peak/storage remain separately
scoped and accounted; the meter caps neither total invocation work nor peak
memory. At that point, after this recommendation's review, the next step was
to present only meter lifetime for user architecture approval. A later numeric supported boundary needs scale
and practical-input evidence, focused independent review, and separate user
approval before implementation. No number, boundary, API, or implementation
is approved; rollback/invalidation capacity and co-resident peak remain open.

The repaired meter-lifetime delta passed a fresh focused M3 review with no
remaining blocking, major, or minor finding; the minor historical wording was
corrected. The user then approved solve-wide accumulation for charged F5c draft
work across components on 2026-09-25. This fixes meter lifetime only; there is
no numeric cap or supported-input boundary. Next: continue the resource
subgate with scale evidence and practical-input margin; focused independent
review and separate user approval remain required before implementation. Full
design approval, rollback/invalidation capacity, and co-resident peak remain
open.

## F5c stack-independent draft design resume (2026-09-25)

The active proposal is [`flat indexed stack-independent F5c draft`](../design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md).
The user approved solve-wide accumulation for charged F5c draft work across
components; this chooses no numeric cap and authorizes no API or production
implementation.

The latest full-slice M3 review found one accepted major gate-sequencing issue:
the draft requires a reviewed/approved numeric support boundary before
implementation, yet actual solver/finalizer co-resident physical capacity and
peak evidence require the implementation. Compiler and performance scopes had
no findings; the specification review also found a minor stale status, closed
by keeping the proposal Draft. Read-only follow-up consultation found no
evidence for a practical numeric cap. The earlier diagnostic campaign used
seven of eight process invocations; its one remaining invocation is
insufficient for prototype work and practical-margin evidence. No code,
prototype, test, or probe ran in this review.

At this checkpoint, the immediate next action was to obtain the user's decision
on whether to authorize a bounded non-shipping measurement candidate. The user
later approved that sequence, as recorded below. Do not choose a numeric cap or
claim F5c/F5e completion based only on that approval. The §44 representative
and atomic route contract remain unchanged.

## User-approved candidate-before-boundary sequence (2026-09-25)

The user approved the recommended sequence: after focused M3 review of the
revised design gate, build a non-shipping explicit-stack implementation
candidate on `yulang3`, then measure its logical work and actual physical lane
capacities before choosing numeric resource limits. This supersedes only the
prior rule that numeric limits had to precede all candidate code. It does not
authorize release, production acceptance, semantic/API expansion, or a
structural-depth cap. No code or probes have run yet.

Immediate next action: focused M3 delta review of design §15. If clean, implement
in modular slices (keep `lib.rs` orchestration-only), commit/push coherent
checkpoints, then run a fresh resource measurement plan under
`rules/performance.md`. The old probe campaign has one invocation left, which
is insufficient for this candidate. Actual physical reconciliation and separate
review/user approval of any numeric support boundary remain hard gates before
acceptance. The §44 representative and route transaction remain unchanged.

The focused M3 delta review is now closed. First round: `architect` had no
finding; `spec_auditor` found one minor historical-authorization wording issue;
`performance_auditor` found one major ambiguity about measurement-plan timing
and budget. One implementer repaired both in the design draft. A fresh focused
`spec_auditor`/`performance_auditor` delta review found no remaining findings.
No code, tests, resource probes, or benchmarks ran in those review rounds.

Candidate implementation is now authorized within the exact reviewed draft
scope. Immediate next action: begin a small module-owned implementation slice,
keeping `lib.rs` as orchestration; use focused small-fixture correctness checks.
Before any resource/scale/capacity probe, prepare and review the fresh bounded
measurement plan required by §15. Do not claim a numeric support boundary,
physical certification, production acceptance, or F5c/F5e completion yet.

## Fixture-only flat-draft normalization checkpoint (2026-09-25)

The first implementation slice is committed separately as a checkpoint after
review and verification. `f5c_draft.rs` defines polarity-specific IDs, flat
node/child arrays, spans, and predicate/bound roots. `f5c_normalization.rs`
adds an explicit-worklist flat input/output path using the existing canonical
ranker; it compacts from the predicate and bound roots after normalization and
does not reconstruct boxed F5c nodes. `lib.rs` contains only a module
declaration. The old boxed production path remains active, so the first §7
producer-boundary gate is still open.

Focused coverage includes positive/negative Functions, mixed-height Union and
Intersection ordering, duplicate elimination, shared child/root identity,
multiple bounds and bound order, exact flat output, compound shallow counter
parity with the boxed path, root/member permutation counter invariance, and
swapped/duplicate source-ID rejection. All fixtures are rooted before
normalization; a duplicated subtree becomes unreachable only after member
deduplication. Initial review findings on ID remapping, checked conversions,
and dropped-owner capacity stats were repaired. Primary rejected the separate
claim that any isolated pre-normalization node must be counter-invariant:
§36 counts actual key-generation work over supplied nodes, while §2 performs
root compaction after normalization. Spec review accepted this scope and the
performance review passed the non-shipping helper; physical lane/co-resident
peak accounting remains a later hard gate. Exact review dispositions and
evidence are in §16 of the design draft.

Verification: `cargo test -p yu-solver flat_tests --lib -- --test-threads=1`
passed (3 tests); `cargo fmt --check` and `git diff --check` passed. No broad
suite, resource/scale/capacity probe, or benchmark ran; candidate measurement
budget consumed is zero. `FlatNormalizationStats` contains logical counters
only and is not production resource accounting. Next: continue producer-side
flat migration and keep normalization/failure/drop flat through the first §7
gate. Then add the `yu-types` indexed transaction. Before any resource probe,
prepare and independently review the fresh §15 measurement plan. Numeric
limits, production acceptance, F5c/F5e completion, F5e Function-product
behavior, and §44 route rollback remain open.

## Occurrence-preserving flat summary materializer checkpoint (2026-09-25)

The fixture-only flat normalizer checkpoint is now joined by a private,
production-unused summary-ID-to-`FlatDraft` materializer. It lives in
`crates/yu-solver/src/f5c_materialization.rs`; raw row Variables are in
`f5c_draft.rs`, and closed `normalize_flat` rejects unresolved Variables.
`lib.rs` remains unchanged. The old boxed production path is still active.

An architect adjudicated the reviewed sharing/counter conflict under existing
§§2, 4, and 5: pre-normalization summary-DAG sharing is not required. Expand
each occurrence with an explicit worklist so the boxed path's scheme shape,
incidence order, and all five logical normalization counters remain exact;
normalization/compaction preserves sharing that survives deduplication. The
candidate checks every summary child is topologically earlier than its parent
and truncates all six append-only draft lanes on checked failure. External
callback state remains the caller's responsibility and must be discarded on
`Err`.

Focused fixtures compare both-polarity materialized structure and callback
order with the boxed path, compare all five normalizer counters on a repeated
summary edge, test cycle rejection, and prove late-error logical rollback.
Independent compiler/performance delta review found no remaining blocker for
this non-shipping helper. Primary closed the remaining minor malformed-ID
coverage request by checking the range/topological/polarity guards directly.

Important residual risk: path expansion is proportional to the occurrence
graph and can be exponential in a compact shared DAG; a recorded depth-12
synthetic case grows 13 summary nodes/24 edges into 8,191 output nodes/8,190
edges. Flat output and normalization/scratch lanes overlap, failed truncation
retains capacity, and exact work/physical peaks are not measured. Production
connection remains blocked on §5 solve-wide size/repeat-work admission and the
fresh independently reviewed §15 measurement plan. No numeric threshold,
depth cap, production acceptance, or F5c/F5e closure is claimed.

Verification: `cargo test -p yu-solver flat_tests --lib -- --test-threads=1`
passed (8), `cargo fmt --check` passed, and `git diff --check` passed. No
broad tests or measurements ran. `lib.rs` remains unchanged and the helper is
substantial but isolated; remove the old boxed materializer only once the flat
producer/downstream migration proves parity. Next: continue the producer-side
flat gate; before any candidate resource probe, review the exact §15 plan.

## Flat binder substitution candidate checkpoint (2026-09-26)

Added the non-production, fixture-backed `substitute_flat` helper in
`crates/yu-solver/src/f5c_binder_substitution.rs`. It starts at the component
predicate and retained recursive-bound lower/upper roots, walks iteratively,
preflights all reachable Variables, and mutates only after successful
preflight. Mapping order is R, then Q, then polarity-specific elimination to
Positive Bottom / Negative Top. Root IDs, bound IDs, spans, insertion order,
and non-Variable nodes remain unchanged. Shared nodes are visited once; no
boxed reconstruction or `lib.rs` orchestration growth was added. The
unreachable unmapped Variable witness confirms unrelated scratch does not
change root substitution outcome.

The first M2 compiler review found a false rejection from scanning unreachable
scratch and missing bound-only root parity; both were repaired. Performance
review asked to remove a temporary root array and avoid duplicate scheduling;
the follow-up uses reverse root seeding and visited-on-enqueue. Primary also
removed duplicate topology/index validation and its two per-polarity `usize`
position tables, leaving this check to `normalize_flat`. Final M2 compiler/
performance delta review found no blocker in the isolated helper. A compiler
minor on `u32`→`usize` conversion was repaired with checked conversions. The
helper is marked unused in non-test builds and remains disconnected.

Important follow-on integration blocker: `substitute_flat` leaves unreachable
scratch untouched, while `normalize_flat` currently scans all inserted nodes
and rejects unresolved Variables. Before using this path, isolate/compact the
selected root forest before normalization, preserving boxed-path logical
counter behavior; also retain §2's post-normalization compaction. Do not
connect this helper directly to `normalize_flat` or production.

Verification: `cargo test -p yu-solver f5c_binder_substitution --lib --
--test-threads=1` passed (6), `cargo fmt --check`, `git diff --check`, and
`cargo check -p yu-solver --message-format short` passed without warnings. No
broad tests, resource/scale/capacity probes, benchmark, or §15 plan ran;
measurement budget used remains zero. Residual work includes the
selected-root/normalizer handoff, flat replay and producer migration, error and
ordinary-drop coverage, the indexed `yu-types` transaction, §5/§15 resource
gates, F5e Function products, §44 rollback, and eventual removal of the
superseded boxed route after parity.

## Latest continuation (2026-09-26): selected-root normalization handoff

`normalize_flat` now composes with the fixture-only `substitute_flat` result,
which may retain unreachable raw Variable scratch. It marks the predicate and
all recursive-bound lower/upper roots, then propagates selection through a
single reverse pass over topological insertion order. The two per-polarity
source maps carry selection state and later normalized IDs; no separate
reachability arrays or traversal worklist are introduced. The forward pass
still validates every source ID and structural edge against its insertion
prefix, including orphan scratch. Only selected nodes enter ranking and the
five logical normalization counters. Preserve the §2 post-normalization
compaction unchanged.

The composed fixture compares all five counters with the boxed selected-root
path and asserts exact normalized flat nodes, child arrays, predicate, and
bound endpoints. It includes a positive Function predicate with a two-member
Union, positive/negative Function bound roots, and orphan compound/Variable
scratch. Separate malformed-edge witnesses cover orphan and selected
Union/Intersection spans and both Function polarities. M2 compiler-referee and
performance-auditor delta reviews found no blocking or major issue. Static
successful-path complexity is O(N+E+B). Two source maps remain sized to all
raw nodes, so their co-resident peak with the normalizer and compaction lanes
remains a §5/§15 production gate. No benchmark/resource measurement ran;
measurement budget used is zero. This remains a sizeable uncalled candidate;
`lib.rs` and production paths are unchanged.

Verification: `cargo test -p yu-solver --lib f5c_ -- --test-threads=1` passed
(176 passed, 1 ignored); `cargo test -p yu-solver flat_tests --lib --
--test-threads=1` passed (9); `cargo test -p yu-solver
f5c_binder_substitution --lib -- --test-threads=1` passed (7);
`cargo check -p yu-solver --tests --message-format short`, `cargo fmt --check`,
and `git diff --check` passed. A full single-threaded yu-solver library run
reached the unrelated F4 scale matrices: the 4k bounded-cycle case passed,
then the run was interrupted as the F4 chain scale matrix began. No earlier
failure was reported; the full suite is unverified.

Next slice: add a fixture-only flat replay candidate and compare it with the
boxed replay oracle before producer wiring. Continue the first §7 producer
gate only in bounded module-owned steps. Do not claim production acceptance,
F5c/F5e closure, the §5/§15 resource gate, indexed finalization, F5e Function
product certification, or §44 rollback.

## Latest continuation (2026-09-26): fixture-only flat replay candidate

Added uncalled `replay_flat` in `crates/yu-solver/src/f5c_replay.rs` and
focused coverage in `crates/yu-solver/src/tests/f5c_replay.rs`. It replays an
immutable flat source under each candidate mask, expands each shared source
edge occurrence independently, preserves polarity/order/elimination, and
reconstructs Functions with boxed replay's default effects. Explicit
enter/finish/leave tasks provide stack-independent traversal and reachable
cycle rejection. On checked failure it truncates every appended node,
child-index, and insertion-order lane. No production caller or `lib.rs` growth
was added.

Coverage directly compares both polarities with boxed replay, includes a
repeated edge in one root, and checks a 4,096-deep input on a 64 KiB thread
stack. The rollback witness enters a positive↔negative Function cycle only
after completing a child Union, then compares quantifier count, predicate,
both node/child arrays, bounds, and insertion order with the full pre-state.
M2 compiler-referee and performance-auditor delta review closed the two
fixture-local test findings and found no blocker for this disconnected
checkpoint.

Production risks remain explicit: every call allocates/zeros positive and
negative active flags sized to all source nodes, and occurrence-preserving
shared-DAG output can amplify exponentially and repeat under each fixed-point
mask. Replay task/value lane counters do not yet charge those flags or output
growth. Include them in §5 draft-size/repeat-work admission and §15
co-resident peak evidence before any production connection; rollback truncates
logical lengths but retains destination capacity. No measurement or numeric
boundary was selected; measurement budget remains zero.

Verification: `cargo test -p yu-solver --lib f5c_flat_replay --
--test-threads=1` passed (4); `cargo test -p yu-solver --lib f5c_replay --
--test-threads=1` passed (6); `cargo fmt --check` and `git diff --check`
passed. No broad suite, benchmark, or resource probe ran. The next bounded
step is to compose flat replay with flat substitution and selected-root
normalization against the boxed oracle. Keep production wiring, the indexed
finalizer, §5/§15 resource closure, F5e products, and §44 rollback open.

## Previous continuation (2026-09-26): composed flat downstream pipeline

The fixture-only flat candidate now composes `replay_flat` on the predicate,
lower bound, and upper bound; `substitute_flat`; and `normalize_flat`. It
compares the complete normalized scheme and five logical normalization
counters against the boxed replay → substitution → normalization path over
the same source and masks. The fixture includes repeated members in both
polarities, Q row 2 → Q0, R row 3 → R1, and polarity-specific Variables that
survive replay and are eliminated by substitution.

Before normalization the test confirms repeated source edges produced
distinct flat IDs. After normalization it checks predicate/bound-root
reachability for every node and child entry, dense IDs, duplicate removal,
and shared canonical R1 IDs across roots. This exposed and fixed a real
candidate defect: equal `(height, rank)` nodes were rebuilt as duplicate
output IDs. `normalize_flat` now uses its already allocated `sort_scratch` as
a first-representative table and reuses that output ID. The repair adds one
O(N) pass with no new allocation. Existing selected-root fixture IDs were
updated to assert canonical sharing.

M2 compiler-referee/performance-auditor delta review found no actionable
finding. The added pass is statically O(N), reuses a lane already allocated
for ranking, and introduces no additional capacity growth. Replay's
source-sized active arrays, occurrence-expanded DAG output, repeated-mask
work, and rollback-retained capacity remain §5/§15 production risks; the
composition test is not resource evidence.

Verification: `cargo test -p yu-solver --lib flat_tests --
--test-threads=1` passed (10); `cargo test -p yu-solver --lib f5c_replay --
--test-threads=1` passed (6); `cargo test -p yu-solver --lib
f5c_binder_substitution -- --test-threads=1` passed (7). `cargo check -p
yu-solver --tests --message-format short`, `cargo fmt --check`, and
`git diff --check` passed. No broad suite, benchmark, or resource probe ran;
measurement budget remains zero.

Next: feed flat summary materialization into this fixture pipeline and compare
with the boxed oracle. Do not wire production or claim §5/§15, indexed
finalization, F5e, §44, or F5c/F5e closure. Review the exact §15 plan before
running any resource probe.

## Previous continuation (2026-09-26): summary-to-flat composed fixture

The composed fixture now begins with a synthetic `F5cSummaryNode` DAG and
materializes the predicate, lower bound, and upper bound into a `FlatDraft`
through `materialize_summary_flat`; it then runs flat replay, substitution,
and normalization. Before replay can erase or merge distinctions, each of the
three materialized roots is expanded and compared directly with the summary
memo's boxed positive/negative value. Repeated edges in positive Union and
negative Intersection remain separate occurrence IDs in the materialized
draft.

The rest of the fixture retains its prior checks: complete normalized scheme
and five normalization counters match boxed replay → substitution →
normalization; all output nodes and child entries are reachable from retained
roots; IDs are dense; duplicates collapse; and canonical R1 nodes share IDs
across roots. The normalizer's candidate repair maps equal `(height, rank)`
keys to one output ID using its existing `sort_scratch` lane, adding one O(N)
pass without new allocation.

M2 spec-auditor review found no issue. Compiler-referee review identified that
post-pipeline parity alone could hide root misassociation; direct boxed parity
assertions for predicate and both bounds were added before replay, and focused
delta review closed that finding. This remains fixture-only evidence. Replay's
source-sized active arrays, occurrence-expanded DAG output, repeated-mask
work, and rollback-retained capacity remain §5/§15 risks, with no resource
probe or benchmark run (measurement budget zero).

Verification: the focused composed test passed; `flat_tests` passed (10);
`cargo check -p yu-solver --tests --message-format short`, `cargo fmt --check`,
and `git diff --check` passed. No broad suite or resource/benchmark run.

Next: continue producer/downstream candidate coverage, comparing every raw
materialized root before lossy transforms. Keep production unchanged until
the reviewed design and resource gates authorize it. Indexed finalization,
§5/§15 certification, F5e, §44 rollback, and F5c/F5e closure remain open.

## Previous continuation (2026-09-26): actual F5c producer memo bridge

The composed pipeline fixture now builds its summary graph through
`F5cComponentExpansionMemo::positive_node` / `negative_node`, rather than
directly filling the memo's internal node and child arrays. Repeated
`Shared` references still produce distinct flat occurrence IDs before
replay/substitution/normalization, and the complete downstream result remains
compared with the boxed oracle.

A separate test in `crates/yu-solver/src/tests/f5c_materialization.rs` calls
the real `F5cGeneralizer::positive_row` and `negative_row` paths on a small
pure-Function constraint fixture. It takes the cached summary IDs returned for
both polarities, materializes each into a `FlatDraft`, and compares against the
boxed `positive_value_with` / `negative_value_with` results before any lossy
transform. The full incidence mark vectors are compared exactly and in order
between boxed and flat materialization. Structural parity is checked with an
explicit LIFO worklist across both polarities, Function fields/effects, and
ordered Union/Intersection members.

Evidence boundary: the test covers actual cached memo roots only; these are
partial summary components, not the full `build_component` predicate/bound
draft or finalized scheme. The comparison helper is explicitly shallow-fixture
only; ordinary deep boxed-tree drop safety remains open. The candidate is
still disconnected from production and no resource evidence was gathered.
`lib.rs` remains unchanged.

The M1 compiler-referee review found that checking only each root's first
incidence mark was insufficient and noted the helper's boxed-drop caveat. The
repair compares the complete positive and negative mark sequences and borrows
the boxed value; fresh spec-auditor delta review found no actionable issue.

Verification: `cargo test -p yu-solver --lib f5c_materialization:: --
--test-threads=1` passed (8); `cargo fmt --check` and `git diff --check`
passed. No broad library suite, benchmark, or resource probe ran; measurement
budget remains zero.

Next: extend the non-shipping source bridge toward complete producer predicate
and bound roots without routing through boxed `GeneralizationDraft`. Keep
`lib.rs` orchestration-only and production callers unchanged. Review the exact
§15 measurement plan before any resource probe; §7/§15, indexed finalization,
F5e, §44 rollback, and F5c/F5e closure remain open.

## Latest continuation (2026-09-26): pre-replay producer roots into FlatDraft

A new shallow guarded-self fixture follows the real `F5cGeneralizer` pre-replay
path: it obtains the root predicate, drains dynamically discovered reentry
owners, expands each owner's lower/upper roots, and applies the same Bottom /
Top defaults for missing source bounds as `build_inner`. It materializes the
boxed predicate and bounds, then encodes those full raw roots into one
`FlatDraft`, wiring its predicate and owner-ordered recursive-bound fields.

Before any replay or substitution, the test compares each root against both
the memo's boxed summary materializer and the expanded pre-replay boxed tree.
It checks polarity, Function fields/effects, ordered Union/Intersection
members, and complete incidence callback vectors. A nested positive row must
be admitted as a summary ID, referenced exactly once in both the predicate and
lower root, and produce exactly one corresponding incidence mark. Bound
ordinals here are source owner IDs, not final R binders.

This is deliberately an intermediate bridge: the producer still returns
boxed `F5cPositive`/`F5cNegative` trees, which the test re-encodes through
`positive_node`/`negative_node` before flattening. It bypasses
`GeneralizationDraft` and stops pre-replay; it does not prove direct flat
construction from solver tasks, Q/R, normalization, final scheme, deep drop,
resource bounds, or production parity. `lib.rs` remains unchanged.

The compiler-referee review confirmed the reentry-owner and empty-bound
selection, with one minor gap: the nested cached row's reference and incidence
could disappear on both paths. The primary repaired this by asserting the
nested `Shared` ID occurs once in predicate and lower, requiring its exact
incidence count, and connecting the returned roots into the flat draft. Focused
module tests pass (9); `cargo fmt --check` and `git diff --check` pass. No
broad library suite, benchmark, or resource probe ran; measurement budget is
zero.

Next: do a code-level design review for an uncalled, module-local flat sink
that shares actual producer traversal and emits IDs at leaf/exit tasks with
cacheability metadata. An architect exploration recommends this over a copied
test walker, while deferring a shared/generic sink refactor until the required
interface is clear. Reuse of producer state from a module-local candidate
without moving traversal ownership remains an unverified inference. Preserve
active-state taint, memo admission, reentry discovery, owner order, incidence,
and append/state rollback. If the design requires changing the active
production path, stop for independent M3 review and explicit user approval.
Resource probing still requires the reviewed §15 plan; §7/§15, indexed
finalization, F5e, §44 rollback, and F5c/F5e closure remain open.

## Latest continuation (2026-09-26): shared producer-walker design reviewed

The boxed-valued `F5cGeneralizer::walk` cannot supply a flat sink with the
actual leaf/exit decisions without a shared interpreter; a copied walker is
rejected. A separate proposal now places the F5c generalizer, summary
memo/transaction, ordered raw-root coordination, shared walker, and `build_inner`
under `f5c_generalization.rs`. `lib.rs` retains component invocation and outer
solver/fact installation. The current boxed sink remains the production path;
the flat sink is still uncalled.

The focused M3 design review used `compiler_referee`, `spec_auditor`, and
`performance_auditor`; two repair/delta rounds closed all blocking and major
findings. The reviewed draft specifies a tagged Local/Shared source arena held
across the full raw-root forest; first-reentry owner order with lower-before-
upper materialization and no hash-map-selected order; chronological root-edge
undo with transient active/conflict scratch returned to idle; and explicit
co-resident resource/work categories. No code, tests, benchmark, or resource
probe ran; measurement budget remains zero.

The no-behavior-change owner move is complete in `f5c_generalization.rs` and
has passed M2 specification/regression review plus focused checks. The boxed
path remains production; the flat sink is uncalled. Next repair and witness
memo transaction/active-state rollback, then add the shared sink. No production
cutover, resource probe, numeric limit, or completion claim is authorized by
this approval. A clean build does not replace §15 resource evidence. Indexed
finalization, F5e, §44 rollback, and overall F5c/F5e closure remain open.

## Latest continuation (2026-09-26): memo rollback gate closed

The approved producer-owner move and memo transaction/active-state rollback
gate are complete. Persistent root admission/invalidation events share one
chronological undo log and reverse replay; failure resets transient active,
conflict, work, visit-mark, and local-mirror state before node truncation.
Fallible child reserve errors now return before append, while retained reserve
capacity remains charged. Co-resident capacity samples include the memo's live
generalizer scratch mirrors, and the independent test ledger calculates its
peak from those snapshots.

Focused failure tests cover interleaved admission/invalidation, warm Shared
lookup after failure, nonzero entry marks, retries, and reserve failure with no
partial child append. They are in
`crates/yu-solver/src/tests/f5c_generalization_transactions.rs`. Latest M2
compiler-referee and performance-auditor delta reviews found no blocking or
major issue.

Verification: `cargo fmt --check`; `cargo test -p yu-solver --lib f5c_ --
--test-threads=1` (192 passed, 1 ignored); and
`cargo test -p yu-solver --lib --no-default-features -- --test-threads=1`
(277 passed, 1 ignored; 717.77 seconds); `git diff --check`. No benchmark or
resource probe ran; measurement budget remains zero.

Next: add the uncalled flat sink through the existing producer walker. The
boxed route remains production and observable behavior is unchanged. No
production cutover, §15 probe, numeric boundary, F5e acceptance, or overall
F5c completion is authorized here. Remaining gates include stack-safe flat
producer/drop and indexed finalization, complete ineligible/effect rejection,
closed-DAG memo/resource accounting, §44 end-to-end per-use rollback, and
independently reviewed §15 evidence.

## Latest continuation (2026-09-26): checked logical-work subgate

The approved shared-walker work now has a solve-wide checked logical-work
meter in the inference session. It is shared with each F5c component memo and
generalizer and covers the current producer, memo, analysis, materialization,
replay, and substitution paths. Charges survive component failure because
they represent attempted work; separately, component memo state still rolls
back. `usize` accounting overflow returns `IdentityExhausted`. No numeric cap
was selected, and this counter does not bound recursion depth, memory, physical
capacity, or wall time.

The meter charges before boxed Function construction and before typed finish
drains. Witnesses cover owner ordering and all five drain-owner families in
both polarities, with no mutation past a failed charge and a successful retry.
M2 compiler/specification/performance delta reviews converged with no open
blocker. Focused checks pass: work-meter filter (15), F5c filter (207 passed,
1 ignored), warning-free `cargo check -p yu-solver --lib`, formatting, and
`git diff --check`. The single-threaded no-default-feature library suite
passed (292 passed, 1 ignored; 952.91 seconds).

The implementation is localized in the F5c modules; `lib.rs` keeps only
session wiring and test registration. Static review identifies constant-
factor meter/lookup overhead, but no performance measurement was run. The
measurement budget remains zero: no benchmark or §15 resource probe. The next
gate remains the uncalled flat sink through the shared walker. Physical
capacity/peak accounting, §15 plan and measurements, indexed finalization,
production cutover, full §44 per-use rollback, F5e, and overall F5c completion
remain open.

## Latest continuation (2026-09-26): explicit raw reentry-owner order

The boxed producer now records each unique raw reentry owner in first
`self.reentries` encounter order and traverses recursive bounds lower before
upper for both materialization and the pre-pruning incidence census. The
owner-keyed map is used only for lookup. A helper-level witness proves callback
order does not depend on map insertion order.

The added owner-order vector charges one checked logical-work unit per entry,
uses fallible scratch reservation before append, and is included in the
simultaneous and independent retained/peak accounting. An injected reserve
failure witness verifies rollback to idle state and successful retry. Focused
materialization tests (12), owner-order/reserve rollback tests, formatting, and
diff checks passed. M1 `spec_auditor` review and focused delta review found no
remaining issue.

The full producer callback/Q/R witness with a warm Shared predicate and a row
first encountered in a later bound remains open for the candidate raw-forest
gate. Next: extract the boxed compatibility sink behind one shared task
interpreter, then add the uncalled flat sink and ordered forest. The boxed path
remains production; no resource probe, benchmark, numeric boundary, production
cutover, §44 closure, F5e acceptance, or overall F5c completion is authorized
by this slice.

## Latest continuation (2026-09-26): boxed sink extraction

The existing task interpreter now runs through one generic
`walk_with<S: F5cWalkSink>`. `F5cBoxedWalkSink` owns the former boxed leaf,
row-deduplication, Function construction, and memo-promotion operations. The
existing `walk` entrypoint and all production callers still use the boxed
sink. Generic value-lane capacity accounting uses the instantiated value
size. No flat sink or candidate flat raw-root forest exists yet.

M2 spec and performance review found no confirmed defect in this intermediate
extraction. Focused checks passed: formatting, solver library check,
generalization filter (17), and F5c filter (209 passed, 1 ignored). Code size
and successful-path timing remain unmeasured under §15. Next: implement the
uncalled tagged flat sink and ordered forest with complete parity and rollback
evidence. Production cutover, §15 probes, numeric limits, §44 closure, F5e,
and overall F5c completion remain open.

## Latest continuation (2026-09-26): fallible sink constructors

The five `F5cWalkSink` value constructors now return
`Result<Value, SolveAvailabilityError>`; the generic interpreter propagates
those errors through its existing cleanup and component rollback. The boxed
sink returns the same prior values inside `Ok`, with task order and work-meter
charges unchanged. M1 compiler-referee delta review found no issue. Formatting,
solver library check, and diff checks passed. No test was added because the
boxed sink has no fallible construction path; injected flat-sink growth and
rollback witnesses remain required.

Next: build the checked Local/Shared source arena and promotion/materialization
bridge, then wire it through the shared walker and the ordered raw-root forest.
This interface preparation does not close the flat-sink gate.

## Latest continuation (2026-09-26): sink construction context

The five `F5cWalkSink` value constructors now receive mutable generalizer
context so a future flat sink can charge source creation and reserve/account
its lanes at construction. `cacheable` remains value-only. The boxed sink
ignores the context and returns the same values. M1 spec-auditor delta review
found no issue; solver library check and diff check passed. No flat arena was
added. Candidate implementation must keep mutations within the sink-owned
representation and component rollback boundaries. Next: add the checked
tagged source arena and explicit node/edge accounting lanes.

## Latest continuation (2026-09-26): tagged flat source arena substrate

A non-production arena now stores polarity-specific Local IDs and Shared
summary IDs, scalar/Function nodes, and ordered tagged child spans in four flat
lanes. It owns no recursive boxes or child vectors. Append checks IDs/spans,
reserves all required lanes, charges solve-wide work, and publishes only after
those steps. Rollback truncates all lanes; release drops them and clears live
capacity. The four lanes participate in the walker ledger and simultaneous
memo peak.

Independent spec and performance reviews found no blocker. Four focused
tests cover tagged order/Functions, work-charge failure, partial reserve
failure, and rollback; solver library check, formatting, and diff checks pass.
The arena remains uncalled by the shared walker. Sink construction,
structural equality/dedup, memo promotion, ordered full-root forest, component
integration, and co-resident source/memo/draft accounting remain open. Next:
implement Local/Shared sink semantics on this substrate without production
cutover.

## Latest continuation (2026-09-26): candidate flat sink over shared walker

An uncalled `F5cFlatWalkSink` now uses the shared `walk_with` task interpreter.
The source arena belongs to the generalizer and survives successive walks;
premature commit/release is not exposed before the future raw-forest
materializer consumes every Local root. The sink implements tagged
Local/Shared equality, ordered first-seen dedup, cacheability, Function
construction, and child-before-parent memo promotion. Failure rolls back memo
roots/nodes and source lengths, restores component result counters, and keeps
solve-wide work charges. Promotion's same-time capacity witness covers memo,
source, and task/ID worklists; reverse-parent construction no longer clones
child IDs into an untracked temporary vector.

M2 compiler-referee/performance delta review found no remaining blocker in this
subgate. Checks passed: formatting, the focused flat-sink filter (13), solver
test compilation, and diff check. No benchmark or §15 probe ran.

The flat sink remains test-only. The full ordered predicate/bound forest,
Local/Shared-to-FlatDraft materialization, full callback/Q/R parity,
source/memo/FlatDraft co-residency, and remaining §5 witnesses are still open.
Production remains boxed; no numeric cap, resource probe, §44 closure, F5e, or
overall F5c completion is authorized.

## Latest continuation (2026-09-26): checked Shared-to-FlatDraft materializer

Added a candidate-only iterative Shared-summary occurrence materializer with
a fallible incidence callback and rollback of all six FlatDraft lengths.
Repeated Shared refs emit separate occurrences and callbacks in traversal
order. Exact-size walker lanes track candidate-flat tasks/values and all six
FlatDraft vectors. A same-time witness checks source, memo, draft, and scratch
capacity; externally pre-reserved append does not grow a second time.
Union/Intersection drain work is charged before child movement; positive and
negative overflow witnesses verify no partial move and successful retry.

M2 spec/performance delta review found no remaining blocker. The
`f5c_materialization::` filter passed (17), the flat sink filter passed (14),
the solver test targets compile, and formatting/diff checks passed. No
benchmark or §15 probe ran.

This covers Shared occurrence materialization only. Local source
materialization, the full ordered predicate/bounds forest, callback/Q/R
parity, component-wide draft/memo rollback, and later FlatDraft/finalizer
co-residency remain open; production remains boxed.

## Latest continuation (2026-09-26): checked Local/Shared batch materializer

Added an iterative candidate materializer for caller-ordered Local and Shared
roots. It preserves polarity, Function field order, and ordered children;
Shared refs flow through checked occurrence expansion. One batch checkpoint
restores all six FlatDraft lengths and the caller-owned output length on error,
while the source arena remains available and work accounting remains monotonic.
Exact-size task/value/root lanes cover scratch and retained output capacity. The
output lane observes preallocated capacity even for empty batches and is
released only after the caller drops the output vector.

M2 spec/performance delta audits found no remaining blocker after repairing the
output-lane lifetime contract. The focused materialization tests passed (3),
solver test targets compile, and fmt/diff checks pass. No benchmark or §15
probe ran. The ordered predicate/bounds forest, callback and Q/R parity,
component-wide memo rollback, and production cutover remain open.

## Latest continuation (2026-09-26): test-only ordered raw forest

Added an uncalled candidate path on `F5cGeneralizer` that collects the
predicate first, then unique reentry owners in first encounter order with
lower before upper bounds and the existing Bottom/Top defaults. It keeps all
tagged roots live through the producer walks, rejects invalid effects before
materialization, and performs one ordered batch. The returned raw owner map
keeps source row IDs separate from final recursive binder ordinals.

Five tracked lanes account owner order, owner bounds, unique-owner state, raw
roots, and Shared callback trace. The checked summary callback receives the
resource ledger and current memo byte count after copying its node, so trace
growth participates in same-time source/memo/draft/scratch accounting. Table
lane counters are checked before allocation; allocator results reconcile
capacity even on reservation errors. The candidate allows one returned forest
at a time. Releasing it drops its owned lanes, advances memo checkpoints, and
resets producer state for a later component.

M2 spec-auditor and compiler-referee delta reviews converged after two focused
repairs: memo checkpoints now advance only after forest release, and owner
table counters preflight before allocation. Checks passed: flat sink tests
(19), materialization tests (17), solver test-target compilation, fmt, and diff
checks. No benchmark or §15 probe ran.

This closes only the raw predicate/bounds forest slice. Full boxed/candidate
callback and Q/R ordinal parity, direct invalid-effect timing evidence,
downstream component rollback through Q/R, indexed FlatDraft analysis, and the
remaining §5 witnesses are still open. Production remains boxed. Next: build
the indexed analysis/Q/R bridge under the existing boxed order authority while
keeping the candidate component transaction open through every later fallible
stage; do not copy the boxed analysis algorithm or cut over production.

## Latest continuation (2026-09-26): shared FlatDraft tree-analysis adapter

The boxed tree-analysis event scheduler now also accepts test-only FlatDraft
IDs. It drives incidence, references, unique first-occurrence collection, and
guarded-bound queries without a second traversal loop. Full event traces for
repeated positive/negative shared child IDs match equivalent boxed trees,
including guard state and early exit. Checked invalid roots, children, and
spans fail with `IdentityExhausted`, clear pending tasks, and permit retry;
logical work charges match exactly on the repeated-edge witness. The existing
4,096-depth 64 KiB test passes after boxing its large captured `ConstraintStore`
before spawning the worker.

M1 `spec_auditor` review found two major witness gaps; one implementation repair
added full trace/malformed/rollback/work evidence, and a focused delta review
found no remaining issue. Checks passed: FlatDraft trace/failure test, the
small-stack analysis test, solver test-target compilation, `cargo fmt --check`,
and `git diff --check`. No broad suite, benchmark, or §15 probe ran. A separate
compile-fix commit restores non-test solver library compilation for the flat
candidate support.

This closes only the shared analysis adapter subgate. The raw forest still
does not use this adapter in the full boxed Q/R orchestration; the candidate
memo transaction still commits before later analysis, and complete callback/
Q/R parity and late-failure rollback remain open. Next: factor the current
boxed incidence/R/Q fixed point over boxed and FlatDraft replay sources without
duplicating its owner/order algorithm, then retain the memo transaction through
all candidate transformations. Production remains boxed; no resource probe,
numeric boundary, §44 closure, F5e acceptance, or overall F5c closure is
authorized.

## Latest continuation (2026-09-26): raw-forest memo transaction precursor

The test-only raw-forest builder now leaves its memo root transaction open after
materialization. Releasing the forest commits and advances memo checkpoints;
aborting drops its lanes and restores root admissions/invalidations and appended
memo nodes. The shared abort owner poisons the candidate generalizer on any
rollback error, including construction-failure and flat-walk exits, and both
candidate entrypoints reject reuse afterward.

The warm-root abort witness invalidates and re-admits a retained key, compares
root maps/heads/edges/marks/undo and node/child/parent/incidence lanes, checks
idle transient state, then retries the same forest. Separate corruption
witnesses cover explicit abort and construction rollback failures. M2
compiler-referee/spec-auditor delta reviews closed. Eight focused raw-forest
tests, solver library and test-target checks, `cargo fmt --check`, and
`git diff --check` pass. No broad suite or §15 resource probe ran.

This proves only raw-forest-boundary rollback. The forest is not yet connected
to shared Q/R, replay, substitution, or normalization, so actual later-stage
failure rollback and full callback/Q/R parity remain open. Next: adapt the
existing single boxed incidence/Q/R algorithm to FlatDraft IDs and retain the
same transaction through every fallible candidate stage. Production remains
boxed; no resource probe, numeric boundary, §44 closure, F5e acceptance, or
overall F5c closure is authorized.

## Latest continuation (2026-09-26): shared raw-incidence census

Boxed `build_inner` and the test-only FlatDraft raw forest now invoke one
predicate-first incidence census through the existing tree-analysis Walker.
It visits owners in recorded order, lower before upper, and retains the prior
raw-bound-owner work charge. An exact-set parity fixture covers predicate
contributions, two declared owners, both polarities, and Function guard edges.
FlatDraft has no Shared node representation; the warm Shared callback check
remains in the separate forest fixture.

M3 compiler-referee, spec-auditor, and static performance delta reviews found
no blocker or major issue. The minor evidence gap closed with the exact-set
fixture and primary diff review. Nine focused raw-forest tests, solver library
and test-target checks, formatting, and diff checks passed. No benchmark or §15
resource probe ran; measurement budget remains zero.

This shares only incidence collection. R fixed-point filtering, retained
occurrence order, Q/R binder assignment, flat replay/substitution/normalization,
full callback/Q/R parity, and actual later-stage rollback remain open. Next:
extend the one shared algorithm through R and Q assignment while retaining the
memo transaction until all fallible candidate stages succeed. Production stays
boxed; no resource probe, numeric boundary, §44 closure, F5e acceptance, or
overall F5c completion is authorized.

## Latest continuation (2026-09-26): shared R fixed-point

Boxed production and the test-only FlatDraft adapter now run one
`r_candidates` fixed-point loop for candidate eligibility, lower/upper bound
replay and guarded-bound filtering, trace pruning, predicate replay,
raw-bound reachability, and convergence. The boxed adapter retains the prior
ordering and charge sites. Flat replay uses the same Walker analysis and keeps
output lanes across replays for reuse.

The test-only raw-forest wrapper owns the live memo transaction through R and
aborts on an R error. Its failure witness completes a replay that emitted
nodes, fails on a later replay, compares all persistent root/node/edge/index
and visit state, checks idle transient state and monotonic work, then retries a
warm lookup. Replay precharges source-sized active-array initialization and
accounts two active arrays and all five replay-output lanes while source, memo,
and forest coexist. Output is dropped before its lane release, including at
direct fixture call sites.

M3 compiler-referee/spec-auditor/performance delta reviews closed with no
blocking or major issue. The minor missing output-child release assertions and
one error-path drop-order precision point were repaired and verified with
focused checks. Flat-walker tests (25), replay tests (6), transaction tests
(11), the composed replay/substitution/normalization witness (1), solver
library/test-target checks, formatting, and diff checks pass. No broad suite or
resource measurement ran; measurement budget remains zero.

Only the R fixed-point loop is shared. Post-convergence retained-R assembly,
Q/R ordinal assignment, full callback/Q/R parity, flat substitution and
normalization integration, and later-stage rollback remain open. Immediate
next: extend the common path through retained-R assembly and Q/R ordinals while
keeping the memo transaction open through each later fallible stage. Production
remains boxed; no §15 probe, resource boundary, §44 closure, F5e acceptance, or
overall F5c completion is authorized.

## Latest continuation (2026-09-26): shared post-convergence R/Q selector

Boxed production and the test-only FlatDraft adapter now share the
post-convergence retained-bound replay, guard filtering, trace survival,
recursive-owner order, occurrence traversal, and Q/R ordinal selector. Bounds
replay in recorded raw-owner order, R follows first surviving traces with
duplicate owners removed, and Q follows the predicate then each recursive
owner's lower and upper bound. Ordinals do not depend on hash iteration.

The flat candidate accounts all retained and temporary post-R collections in
distinct capacity lanes and reserves fallibly before each growth. Temporary
lanes release after their owners drop; selected lanes remain live with replay
output and the memo transaction until release or abort. Paired tests cover
raw `[1,2]` versus trace `[2,1,2]` order, Q traversal through predicate/lower/
upper roots, R offsets, missing raw owners, and a rollback after post-R replay
has emitted output. The failure witness checks memo restoration, all output
and post-R lane releases, idle state, and warm retry.

M3 compiler-referee/spec/performance delta reviews closed without actionable
findings. Four `post_r_` tests and four tree-analysis tests pass, along with
test-target compilation, formatting, and diff checks. No broad suite or
resource measurement ran; the §15 measurement budget remains zero.

Immediate next: integrate FlatDraft substitution and normalization through
this shared selector, extend callback/Q/R parity, and prove rollback through
the remaining fallible stages. Then close the physical resource gate and its
reviewed §15 measurement plan before any resource probe. Production remains
boxed; production cutover, numeric resource limits, indexed finalization API
choices, §44 closure, F5e, and overall F5c completion remain open.

<!-- handoff-append-anchor: 2026-09-26 -->

## Latest continuation (2026-09-26): selected FlatDraft substitution and normalization

The shared post-convergence selector now composes with test-only flat
substitution and selected-root normalization. Recursive bounds follow R-owner
order; substitution applies R, Q, then polarity-specific elimination. A paired
fixture matches boxed structure, Q/R ordinals, and all five normalization
counters, and checks orphan Variable scratch is omitted.

The memo transaction stays open through normalization and output-capacity
observation. Late failure restores persistent memo state, releases transient
lanes, and permits a warm retry. Successful output stays accounted until
explicit release.

Requested-slot counters cover 27 observer lanes (13 normalizer, eight
additional scratch, six emitted output) and contribute to the aggregate. The
six output requests are counted once; publication records retained capacity.
M2 compiler-referee review found no semantic or rollback issue. The performance
requested-slot gap and duplicate count are closed after repair and primary
diff review.

Checks passed: RUSTC_WRAPPER= cargo test -p yu-solver --lib selected_flat_ --
--test-threads=1 (5); RUSTC_WRAPPER= cargo test -p yu-solver --lib flat_tests
-- --test-threads=1 (15); RUSTC_WRAPPER= cargo check -p yu-solver --tests
--message-format short; cargo fmt --all --check; git diff --check. No broad
suite, resource probe, benchmark, or §15 measurement ran. Next: close full
callback/Q/R parity and remaining physical resource reconciliation, then
prepare and review the §15 measurement plan before any resource probe.
Production remains boxed; indexed finalization, production cutover, numeric
boundary, §44, F5e, and overall F5c acceptance remain open.

## Latest continuation (2026-09-26): end-to-end callback and Q/R parity

The selected FlatDraft candidate now has a paired root-forest witness with two
raw recursive owners. It includes a prewarmed Shared occurrence repeated in
predicate roots and a negative-polarity Shared row first encountered in a
later bound. The test compares the complete boxed and flat callback sequence
including polarity, Shared-hit counts separately, Q/R maps and ordinals,
normalized structure, and all five normalization counters.

The same raw bound entries are inserted in both owner orders while the
explicit owner traversal remains fixed. Both variants yield identical
callback traces, hit counts, and Q/R assignments. Callback capture is
test-only at the existing materialization event. The M1 spec-auditor's major
single-owner finding is closed by the two-owner fixture.

Checks passed: `RUSTC_WRAPPER= cargo test -p yu-solver --lib
selected_flat_candidate_matches_boxed_q_r_and_normalization_counters
-- --test-threads=1` (1), `RUSTC_WRAPPER= cargo check -p yu-solver --tests
--message-format short`, `cargo fmt --all --check`, and `git diff --check`. No
broad suite or measurement ran. Remaining candidate gates are full physical
resource reconciliation, the reviewed §15 measurement plan and campaign,
indexed finalization under its approved API scope, and final implementation
review. Production remains boxed; no numeric support boundary, production
cutover, §44 closure, F5e acceptance, or overall F5c completion is authorized
by this slice.

## Latest continuation (2026-09-26): static F5c resource-lane audit

A read-only source audit compared the existing F5c owner against F5 §§26/34
and F5c §§5/15. It found that the `non_generic_closure` adjacency, connected,
closure, and frontier collections and the raw-incidence sets lack independent
physical-lane accounting. Full source+memo+draft+normalizer+finalizer
co-resident peak reconciliation remains open. The boxed normalizer reserve
returns before its candidate observer can reconcile actual capacity on a
failed reserve; the flat candidate helper observes capacity after success or
failure.

No code, tests, measurements, or probes ran during this audit. The bounded
FlatDraft producer/normalizer fixture gate is complete, so the next approved
implementation gate is the exact `yu-types` indexed API from §3 of the
2026-09-25 proposal. Finish physical-lane accounting and independently review
the fresh §15 plan before the first resource probe. Preserve existing resource
owners/families; do not infer numeric limits or production acceptance.

## Latest continuation (2026-09-26): indexed finalizer implementation gate

The approved `yu-types` §3 indexed finalizer is implemented and its focused M3
gate is independently closed. The method and seven input types match the
approved declarations. Validation uses checked dense IDs/spans/Q/R ordinals,
an iterative three-color traversal, and complete reachability; construction
uses the prescribed root/Function/product order and handles returned by the
active finalizer. The indexed path skips the old quadratic callback validator
only after direct validation succeeds. Eleven temporary lanes use checked
geometric growth and reconcile actual capacity with the existing Arena/Scratch
checkpoint; checked pre-reservation covers indexed overlay lanes.

Compiler-referee, spec-auditor, and performance-auditor delta reviews found no
remaining indexed-finalizer issue after repairs. Focused tests compare exact
callback/indexed event order with alpha-equivalent output across both
polarities, Functions, Q/R, and shared/repeated Union/Intersection edges. They
also cover malformed IDs/spans/Q/R, cycles/orphans, temp-lane and transaction
failure stages, retained-capacity retry, terminal short-circuit, unwind,
accounting peaks, and small-stack Function-chain cleanup. Checks passed:
`RUSTC_WRAPPER= cargo test -p yu-types --lib indexed_ -- --test-threads=1`
(13), the full `yu-types` lib suite (28), test-target check, `cargo fmt --all
--check`, and `git diff --check`. No resource probe or benchmark ran.

Next, close solver-side physical-lane accounting in the existing F5c owners,
including `non_generic_closure` temporary sets/frontier, raw-incidence sets,
failed-reserve observations, and the solver/finalizer same-time peak. Then get
independent review of a fresh §15 plan before any probe. Producer incidence
admission and measured resource bounds remain open. Production is still boxed;
there is no numeric support boundary, production cutover, §44 closure, F5e
acceptance, or overall F5c completion.
