# Local-use restoration source-owner audit

Date: 2026-10-11
Status: frozen, unreviewed research characterization and conditional implementation seam
Baseline: `18f13d938be7e7c85df8525c5dd2fb6a4c999671`
Lease: this note only; no compiler, test, Cargo, Git mutation or delegation

## Objective, authority and result

Trace parsed `Action::Local` through live capture, one fresh use, remapping,
accepted-bound restoration, replay, typed completion and publication. Authority
is the Authoritative private candidate suspension contract §§3–7, especially
owned nested frames (§3), completed owner operations and live opposite indexing
(§4), dependent withdrawal/group publication (§5), atomic route failure and
successful suspension (§6), and authentic source verification (§7). The accepted
user approval recorded there is “承認して実装を進めて”. The existing source-action,
source-support and typed-terminal handoffs supply their stated implementation
scopes; they do not establish the missing lifecycle theorem.

**Observed source result:** the earliest existing safe wait after a local-use
owner operation is the next source step after `route_candidate_local` returns
successfully and `source.next` advances. An accepted-bound seam already exists
in the restoration owner, but the surrounding fresh-use maps and source/route
return stages are still synchronous. Returning from that seam today cannot
mean a completed local action.

**Conditional seam:** retain a fresh-use owner before entering restoration,
call the existing `candidate_begin_bound_restoration`, store its returned ID
in that owner, and only then offer a private suspension boundary before
driving its first replay. This uses the complete accepted-bound owner operation;
it does not interrupt bound insertion or replay generation. The parent must
advance the captured-bound index only when that exact restoration completes.

**Precise blocker:** the pinned retained-input constructor unconditionally adds
`FilterObligationsUnavailable`, `ProducerReadinessUnavailable` and
`DependentObservationsUnavailable` and returns `InputCompleteness::Incomplete`
(`candidate_context.rs:994–997`). Search stops at that unsupported authentic
certificate premise. This note supplies neither a production certificate nor
the full §7 source join.

## Actual producer and consumer route

All source/test locators below refer to the pinned revision.

| Operation | Owner and exact locator | What happens before its parent advances |
| --- | --- | --- |
| Parsed local Name | `candidate_source.rs:369–388` | Name effects become source facts. A reference to an active recursive initializer selects `Action::Link`; a published local selects `Action::Local { slot, occurrence, value, level }`. Those are different existing routes. |
| Install local authority | `candidate_source.rs:307–328,643–652`; `candidate_scheme.rs:1239–1254` | Initializer processing precedes `Install`/`LocalAnnotation`. Construction retains the exposed term in `PublishLocal`; publication installs `LocalScheme { id, root, boundary }`. |
| Execute Local | `candidate_source.rs:656–658,680` | Calls `route_candidate_local`; only success increments the immutable schedule cursor. The next `step_candidate_source` checks registered support/raw synthetic wait before more work (`:611–623`). |
| Route transaction | `candidate_scheme.rs:1265–1302`; `lib.rs:9162–9190` | Read installed root/boundary/local identity; capture its current live graph; freshen; link to the source occurrence; retain `LocalFreshRoute`; finish accounting. `Ok` commits the route, `Err` rolls it back. No nested `Suspended` outcome is propagated by these helpers. |
| Capture | `candidate_scheme.rs:194–204,617–620,647–695` | Owns graph, endpoint/row/evidence maps, pending endpoints and row/bound/context/payload cursors locally. The graph is a use-time observation of the live root, not a frozen initializer scheme (`:1274–1276`). |
| One fresh use and rows | `candidate_scheme.rs:900–940` | `begin_use` allocates the use identity at `:904`. Canonical rows share one mapping. Only local rows above the capture boundary that are generic receive new coordinates (`:933–937`). Older/nongeneric coordinates remain shared. |
| Other remaps | `candidate_scheme.rs:941–1028,1031–1082,1083–1138` | Owns bundle, view, effect-operand, weight, context and imported-evidence maps; reconstructs structural Function terms through a local work stack. Shared inputs stay shared inside this use. |
| Bound transport | `candidate_scheme.rs:1141–1180` | Iterate captured bounds in order. Build mapped owner/item and side; transport the original relation with this use identity and remapped context; attach remapped bundles; supply `FreshUse { antecedent, use_origin, source_bound, mapped_relation }`. |
| Accept one bound | `candidate_extrusion.rs:655–675` | Reserve restoration storage, insert one accepted bound with evidence, canonicalize owner/item, save the opposite count, retain emission, occurrence and cause, and return the restoration ID. No product has been driven by this operation. |
| Drive physical products | `candidate_extrusion.rs:677–721` | Retained restoration owns count/index/replay. Complete the active replay before advancing. For each later saved index, reread the current canonical owner and direct/exact opposite vector; then construct its ordered input pair and retain the replay ID. |
| Generate replay | `candidate_context.rs:2855–2936` | Freeze heads/prior progress; enumerate the existing two ordered quadrants; retain exact child relations in an owned replay operation only after generation completes. The scratch vector and generation cursors are local during generation. |
| Consume child | `candidate_context.rs:2938–2970`; `lib.rs:11825–11920` | A fresh-use replay supplies original occurrence/cause to synchronous `constrain_live_item`. Queue transfer and successful child consumption remain separate frontiers. The popped typed item and acknowledgement are retained before fallible dispatch. |
| Terminal child handoff | `lib.rs:12219–12306`; `candidate_context.rs:1661–1667,1785–1795,1836–1863` | Diagnostics precede terminal acknowledgement. The drain owns completed/prepared acknowledgement cursors; final completion leaves a retired replay alive while its restoration parent still references it. Parent advancement then releases that handle. |
| Complete Local | `candidate_scheme.rs:1279–1296`; `candidate_source.rs:656–658` | Only after every freshening restore returns, admit/drain the value link, publish the local route record and commit; then advance the source cursor. |
| Publish SCC member graphs | `candidate_scheme.rs:768–842` | Complete every member source schedule, capture all member graphs into local `staged`, then install all graph slots together. A local scheme/route is distinct from the SCC member slot. |

The typed-terminal slice already closes the old missing-handle interval: a
retired final replay remains readable by its live restoration parent. It does
not supply the missing fresh-use parent or an outward suspension result.

## Why an inner return is still unsafe

This is a bounded ownership characterization, not a theorem that every nested
helper in the package is covered.

| Synchronous region | State lost or misinterpreted by an early return |
| --- | --- |
| Local route closure | Captured `Graph`, source identities, returned rows/lower, next link/publication/accounting stage. Its `Result<()>` is consumed as complete; an error initiates rollback. |
| Capture | `Capture` borrows the session and a local evidence meter; graph/maps/frontiers and context/payload traversal are not session-owned continuation frames. Keep capture atomic for the proposed narrow seam. |
| Freshening | `context_use`, all remaps, reconstructed terms/work, graph/occurrence/cause and captured-bound position. `freshen_candidate_graph` resets its scratch accounting on return (`:895–898`); dropping local maps while retaining their bytes would also misstate ownership. |
| Restoration wrapper/driver | Restoration data is retained, but `candidate_restore_bound_with_evidence` immediately drives it (`extrusion:651–652`). Its caller holds the only local returned handle until a parent frame records it. Returning `Ok(emission)` would make freshening proceed to the next bound. |
| Replay generation | Local heads/prior/quadrant/lower/upper cursors and partially generated child vector, before transfer at `context:2923–2929`. Reserve/construct/retain the full operation before yielding at the narrow seam. |
| Child/typed drain | The inner frame stores substantial work, but the enclosing driver still seeds/enqueues a new initial task and runs a local loop/transition total (`lib:11848–11881`). Its synchronous error branch removes the newly created drain (`:12227–12238`). A saved frame is not yet an executable entry point for resuming arbitrary dispatch. |
| Function admission | `candidate_step_function_dispatch` records the admitted relation in `pending` and stage `FunctionEnqueue` before enqueue (`lib:12316–12338`). This is a complete inner owner seam, but the synchronous outer drain must retain and resume its caller stage before it can yield there. |
| SCC orchestration | Components/members/current member/capture position and `staged` graphs remain local vectors/loop positions. Only the source action frame is persistent; pausing it does not by itself retain the enclosing SCC frontier. |

For Local specifically, a source-boundary wait is safe **after** route completion
and `next += 1`, not between those two statements. At that later boundary the
source frame points at the next action and completed per-use ownership is in
`local_routes`. `source_cursor_wait_after_completed_local_use_does_not_freshen_it_again`
(`candidate_context_tests.rs:4069–4098`) is the existing focused control. It
uses ordinary parsed source and a synthetic wait after the first Local; it
does not suspend an unfinished restoration.

## Source reachability and what a regression can establish

An ordinary parsed-source fixture has already reached multiple physical
opposites without synthetic graph edits in the independently reviewed
`2026-10-11-selected-owner-restore-callback-coverage.md`, at its own baseline
`064f2af2b1a49df0b332b5980cfc5a105715c353`:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int) = ({ my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb } as [
    E
    'x
] int); my defer u = (bridge as ((int -> ['a] int) -> ['b] int) -> [
    E
    'q
] int); defer }
```

That historical execution had no parser recovery, completed the normal private
graph-plan route, restored an unchanged nongeneric owner with saved count six,
and consumed six children covering three distinct ordered fibers. The callback
appended a duplicate upper; it did not modify the saved opposite vector. This
is evidence that normal source can reach restoration multiplicity. Its exact
IDs/count at `18f13d938` are **unverified**, since this audit runs no compiler.
Cached parser/HIR source-build provenance in the prior experiment was unknown;
the note does not convert that historical trace into a new baseline check.

The pinned ordinary-source bridge regression
`local_annotation_bridge_queued_endpoints_follow_parent_copy_equality`
(`candidate_context_tests.rs:3590–3594`) executes a related source root but
does not assert opposite multiplicity. The pinned restoration control at
`:1725–1791` directly creates rows/two uppers and attaches Swap contexts; the
terminal control at `:4409–4453` uses a synthetic drain fixture. They check useful
owner/rollback seams, with no authentic source certificate implication.

A focused future regression can establish, for one parsed schedule and exact
pause index: one retained use identity/remap, one accepted emission, saved count
and live-index product order, child drain/acknowledgement ownership, stable
repeated wait, exact rollback, and completion before source cursor advancement.
Comparing it to an uninterrupted run of the same compiler shares the compiler's
source generation and transition assumptions. It is an implementation
correspondence check, not an independent semantic oracle or all-source proof.
Assert count >= 2 from the actual source restoration before injecting a wait;
creating two opposites afterward would assume the source premise.

It cannot establish §7 initial authentic certification, old memo/completion and
published-member dependence, a late unsupported Function/swap in the same
component, full withdrawal/recomputation, or source-generated recognition.
The existing synthetic support attaches only to `PublishLocal`
(`candidate_source.rs:594–600`) and checks invalidity before publication
(`:613–617`); it supplies no Local-restoration support owner or full consumer
inventory. The unconditional three retained-input gaps above remain explicit.

## Concrete seam and falsifier

**Recommended seam, conditional on implementation ownership:** split the
captured-bound loop at `candidate_scheme.rs:1177–1180`. Move the captured graph,
single `context_use`, completed remaps, term/row results, bound cursor and exact
source provenance into a retained fresh-use frame before admitting its bound.
Fallibly reserve that frame and rollback ownership first. Store the result of
`candidate_begin_bound_restoration` in an `AwaitRestoration` stage before
checking support. The restoration owns the accepted emission/count/index;
the fresh-use parent keeps its bound index fixed. A successful suspended route
commits these retained obligations without publishing `LocalFreshRoute` or
advancing `source.next`; failure restores the pre-route frame/accounting. This
requires an explicit outcome propagated through the Local route and source
action, not translating suspension into `Ok(())` or availability failure.
Keep nested capture/remap/replay generation atomic in this bounded first seam.

**Small structural falsifier for a restart shortcut:** retain a restoration
after its first accepted bound, with source cursor still selecting the same
Local action, then resume by invoking `route_candidate_local` from its start.
The unconditional `begin_use` at `candidate_scheme.rs:904` allocates another
use identity before restoration resumes. Thus it already violates §3/§7's
single-use requirement even if all endpoints later canonicalize identically.
If resume also repeats `candidate_begin_bound_restoration`, it emits/adopts
another accepted bound rather than using the saved emission. The minimal
conditional state needs one Local action, one captured bound and a parked
restoration; two opposite products add §7's unfinished-product control.

This is a derivation against the proposed restart mutation, not an observed
failure in the pinned synchronous compiler. A discriminating check should
assert original `use_origin` and original accepted admission/emission identity
before/after repeated drive and final resume, and fail if the source cursor
advances while the restoration remains pending. No mutation or probe was run.

## Checks, independence, coverage and resources

Inspected pinned source with bounded `git show 18f13d938:<path> | nl -ba |
sed -n '<ranges>'`, targeted symbol/test `rg`, `git rev-parse` for baseline/blob
identities, and path-only status. Read governing rules and the `yulang-proofs`
skill. One initial task-record read and a few combined captures were truncated;
focused source slices subsequently support the reported owners. No exhaustive
negative claim depends on those captures. No tests, Cargo, parser execution,
formatting, Git mutation, delegation, random seed/range or timing measurement.
No checker/oracle is supplied. This source audit is a producer report and makes
no independent-review claim about its own note or the other lanes.

Budget: bounded read-only audit with one leased note under the assigned
25-minute ceiling; lightweight command pipelines only, no heavyweight process.
Exact CPU time, RSS, pipeline subprocess count and wall time were not measured.
No search timeout or killed shard occurred. Omitted: current-baseline dynamic
fixture reproduction, exhaustive constructors, full typed dispatch/extrusion
continuations, certificate recognizer/readiness/filter/transport proofs,
complete dependent-observation inventory, source/SCC suspension, full §7,
soundness/principality and production cutover.

One next action: implement and independently review the retained fresh-use
`AwaitRestoration` seam, using the historical ordinary-source fixture as a
multiplicity control after re-establishing its count at the implementation
baseline; keep authentic §7 certification and withdrawal as open dependencies.

## Commit packet

Exact leased/changed path:
`notes/progress/2026-10-11-local-use-restoration-source-audit.md`.
Baseline SHA: `18f13d938be7e7c85df8525c5dd2fb6a4c999671`.
Changed dependency hashes: none by this worker. Frozen baseline Git blob IDs:

| Dependency | Blob SHA-1 |
| --- | --- |
| `candidate_source.rs` | `632fb512ea8086ea8ed2065997ad619d582576ee` |
| `candidate_scheme.rs` | `1b8ad8d4cbfc3d8e7ea07666c4e0081b35c40ff5` |
| `candidate_extrusion.rs` | `447fc7303ba743cb1d07812dec9a320386b477b3` |
| `candidate_context.rs` | `d4c774e918de490359889ce20ec19584381fccb8` |
| `candidate_context_tests.rs` | `ba3723ef4d5e21ad8ffe7f39d9203a2905a466c2` |
| `lib.rs` | `5572f7b6a649605ec34f236263c13828d9325996` |
| Private suspension contract | `fd92fb5c62564455cb66e19059d147dfc20985e7` |
| Source-action handoff | `1e9575b5c3c86f002323b2d9099a0bcb9955b1bf` |
| Typed-terminal handoff | `6377a6d7ce2e7dc925ad0af3e7a36eda570f49eb` |
| Source-support handoff | `0fd4874a1a3f0c029aa4e86c634e557ea377f12e` |
| Historical selected-owner source trace | `f5704736c15377f52b746610b84593323be020ed` |

Source filenames in the table are under `crates/yu-solver/src/`; design and
progress filenames are the exact named references above. Primary revalidates
current HEAD/working dependencies before integration. Review status:
producer-only, unreviewed, frozen research checkpoint; no gate closure.
Checks already run: static pinned-owner/caller/test reads and baseline/blob
identification; no executable verification. Proposed one-line commit message:
`research: trace local fresh-use restoration continuation owners`.
Shared-record deltas intentionally left for primary/curator: record the
`AwaitRestoration` owner seam and restart-use falsifier; retain current-baseline
source multiplicity reproduction and readiness/filter/dependent-observation
joins as open; distinguish local slot installation from SCC member publication.
No shared task/index/theory/authority/question-board record changed.
