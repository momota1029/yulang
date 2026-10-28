# NATIVE-LAUNCH-PROJECTION/r6 core handoff

Assignment `native-launch-projection-r6-core`, revision 1; author `/root/native_launch_projection_r6_astra`; session `NATIVE-LAUNCH-PROJECTION-20261028/r6`. Contract SHA256 `01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a`; baseline label `7b3ad7074`. Requested Astra/medium; observed model/effort UNKNOWN. Sole write is this inbox. No descendants or scratch paths.

Outcome: **conditional source audit; stopped on input hash change; no completed proof or producer certification**. Three stages: observer/undo footprint; launch/seed/enqueue/receipt comparison; attempted transitive footprint audit stopped at changed input. Grant 300 seconds aggregate, three stages, no renewal. Exact elapsed time was not instrumented; stop-condition clock was 2026-10-28 09:26:02 UTC. No Git, Lean/Lake, Cargo, tests, builds, formatter or external tools ran. Shell reads, SHA256 computation and this handoff write only. Theorem types/axiom dependencies: no new Lean declarations, checker NOT_RUN; no claim of checked or axiom-free proof.

## Parent and source authority

`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`, remains

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.NativeCorrespondence`, line 147, independently requires

```lean
∀ s x n, p.nativeSuccess s x n →
  ∃ d a, p.generates s x d ∧ p.nativeRealizes n d a ∧ p.solves d a
```

These are proposition definitions. No concrete instance or shared source witness is supplied here. This local audit can support a bounded native launch bridge only; no source domain, ordinary inference, birth-level qualification or annotation-effect policy changes follow. The birth-level authority and effect-hygiene policy were read. R5 review is reused solely for its missing observer/seed/enqueue bridge and failed-evidence boundary. R5 unchecked declarations are neither imported nor assumed. `NativeDrainOwnership.lean` was inspected for its state representation; its abstract events are not evidence that source emits those events.

## Input authentication and failure

Before source-body reads, every Rust and Lean/proof input in both R6 hash tables was independently hashed; all 26 matched. ACK was sent to Luna. Source paths below have prefix `isolated/native-launch-projection-r6/` unless stated otherwise.

Direct dependencies:

- `crates/yu-solver/src/candidate_context.rs`: initial `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`; observed at stop `df3249497c1b37eb5ee13c763103206176d201b1ca9c23c7d77766f3a3b1c6b6`.
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`, rechecked unchanged at stop.
- `crates/yu-solver/src/candidate_effect.rs`: `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`, rechecked unchanged at stop.
- `notes/theory/lean/YulangClosure/NativeDrainOwnership.lean` in snapshot: `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18`.
- Main `notes/theory/lean/YulangClosure/Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Main birth-level authority: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`; effect-hygiene authority: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- Main R5 review: `9d4e79216181a452c026c89523ca2ad0d37803c318671c3e315f32a9c4adc5c1`.

The initial context launch/helper excerpts used the line numbers below. Later excerpts visibly shifted, prompting the hash check. Individual read commands did not atomically bind content to hashes; **the interval of modification is unknown**. Therefore context citations are locators for re-audit, not an authenticated immutable baseline transcript. No changed helper body is accepted as new authority. Source reads ceased immediately after detecting the mismatch; Luna was notified. The audit must not be promoted as complete source correspondence.

## Stage 1: observer footprint and projection discipline

At the initially observed `candidate_context.rs:4082–4095`, `candidate_prepare_replay_wait` first reads transaction presence and undo capacity, then calls `prepare_replay_ack`, and samples resources only if capacity changed. At `:2376–2384`, that helper looks up the operation, reserves one undo slot, then appends the previous `(id, waiting_child, queued, consumed, retired)` when transactional. Thus a sampling failure can follow an actual undo append and physical capacity growth. It is not an unchanged native state.

Stable `lib.rs:9253–9266`: `observe_typed_route_capacity(true)` sets `route_attempt_physical_change = true`; if sampling fails it also sets `incoming_route_event_sample_failed = true` before returning that error. `:10774–10789` sampling changes test sample attempts and thread-local observations. `:10821–11010` performs fallible accounting and calls resource-parts code; `:11017–11075` passes mutable counters and, under test, sample count/resource ledger. The tail around `:11419–11437` publishes prepared ledger/counters/sample count; successful probe builds also invoke `observe_f5c_matrix`. These are real writes, not a pure callback assumption. The latter transitive probe footprint was not completed before stop.

A sufficient mathematical rule for erasing an observer's *data update* is:

```text
for every native observer transition s --(phase, result)--> s',
  launchProjection(s') = launchProjection(s),
while retaining phase, result and the concrete resource/undo update in the
native transition and retaining all accumulated prefix writes on Err.
```

This is a proposed obligation, not a proved source theorem. Launch evidence can omit resource counters/capacities/flags while native state retains them. It must retain replay operation/task/child identities and cursors, frame stack and saved processing, queue contents, origins and receipt attribution, current processing, plus every relation payload used by the bounded conclusion. Undo and diagnostic state must either be explicit auxiliary state or have exact projected update/error-prefix constructors. Full context equality is unsuitable because seeding changes it.

Crucially, projection equality alone does not justify removing observer execution or its error edge. A capacity-blind projection need not determine availability. A source-located falsifier is transactional undo growth followed by resource-accounting overflow: the operation stays Idle, undo remains appended, no frame is created, and the caller returns Err. In test configuration, `sample_fixed_capacity_probe = RouteJournal` routes to checked arithmetic using `usize::MAX` at stable `lib.rs:10834–10859`. This is a falsifier recipe, not an executed fixture or proof of source reachability. Any model that unconditionally continues to frame creation after a pure stutter loses that prefix.

## Stage 2: composition constraints from launch source

The initially observed `candidate_context.rs:4097–4121` rejects missing operation, queued/consumed mismatch and nonempty worklist before preparation. It selects `children[consumed]` and retains the exact operation/task/index in the work item. After `start_typed_drain` succeeds, destination is written before `waiting_child = Running`. None of those prior failures can be collapsed into success.

Stable `lib.rs:14186–14229` gives this order:

1. `begin_typed_drain` reserves then appends a frame (initially observed context `:2249–2259`), saving both prior processing fields, with Transport stage, no destination and no receipt. Reserve failure precedes append.
2. Processing is cleared; diagnostic clear may fail after partial workspace journaling/clear. `lib.rs:15934–15960` has separately fallible reserve, payload and observation points between replacement of diagnostic vectors; `:15962–15988` clears remaining diagnostic scratch. A failure here retains the appended frame and whatever prefix writes occurred. This caller does not invoke the separate synchronous wrapper's unwind.
3. Resource sampling occurs, then `origin_index` and incoming relation are recorded, and `candidate_context_seed_with_formal` is called even though the item already carries `Some(child)`.
4. `item.relation.or(seed)` keeps the incoming child relation. The seed is a separate created identity; equality of created seed and selected relation is not guaranteed.
5. Enqueue succeeds before passive receipt publication. Receipt retains incoming relation, ack, created seed, selected relation, origin index, task, cause and `completed=false`. The origin is updated only if its index exists, relation/occurrence match and previous receipt is absent. The frame update itself uses an optional lookup. Those conditions need derivation from preceding concrete constructors, not assumptions that receipts exist.

The initially observed seed body `candidate_context.rs:3374–3460` can allocate context/source sets/scoped transforms, intern relation/scoped flow, propagate bundle linkage, append an origin, then fail in resource sampling. Formal is `None` on this child path. Even if selected relation stays the child, these writes cannot all be called seed preservation. A useful restricted lemma would preserve the selected replay row, existing frame prefix and worklist while specifying all newly created seed/origin/metadata. Transitive helper inspection was incomplete and became unauthenticated at the stop condition.

Stable `lib.rs:15223–15255` skips `candidate_enqueue_evidence` for this `Some(child)` item, but still reserves worklist and calls `transfer_replay_child`. `reserve_worklist` at `:15094–15112` may replace the queue allocation, transfer contents, append workspace undo and fail in observation. Initially observed `transfer_replay_child` at context `:2385–2398` checks Idle, not retired, child bounds and cursor interval; if ack index equals queued, it prepares undo and increments queued. Only afterwards do infallible journal push and queue insertion occur. The launch entry did not explicitly check `retired`; a universal Idle/Some-to-success claim therefore needs either native reachability evidence excluding that state or an explicit error constructor. Arbitrary field combinations are not claimed source-reachable counterexamples.

The intended successful result must retain `consumed=k`, `queued=k+1`, the exact queued task/relation/ack, the appended frame's index/provenance/saved processing, its receipt when the seed/origin construction supplies it, `replay_destination=ack`, and `Running(ack,index)`. No driver/Transport/Context/Dispatch completion follows.

## Stage 3 stop, obligations and mutual TODOs

First currently missing source evidence: immutable transitive write coverage of `candidate_context_seed_with_formal` / `candidate_context_seed`, particularly `context`, `intern_sources`, `intern_scope`, `relation_with_scoped`, `bundle_link`, and their resource sampling, preserving replay/frame/queue components while specifying seed/origin changes. Observer probe callbacks and reserve helpers also require complete write-footprint coverage. Candidate field disjointness is not yet a source proof.

`R6-CORE-FROZEN-INPUT-1` — Luna owns restoring an immutable read dependency for the proof/core audit while the Rust lane writes its leased snapshot file. Required input: exact source bytes/hash with stable access. Proposed next output: a newly authorized audit or proof revision after freeze; this handoff is stopped. Falsifier: pre/post source hash mismatch, or a hidden helper write into retained launch evidence.

`R6-CORE-PREFIX-1` — proof lane/Luna intake: represent observer Err with prior undo append; frame/processing/diagnostic/seed prefixes at every fallible point; enqueue transfer and cursor increment; separate seed and selected-child lineage. Required inputs are the authenticated source bodies above and all called owners within granted read authority. Falsifier: failure represented as unchanged native state, success obtained from assumed seed preservation, or receipt attached before queue insertion. This is an evidence request, not added authority or approval of either producer.

No parent theorem is closed. No independent review or production authority is claimed. Handoff revision 1 is frozen on submission; hash is returned separately to avoid self-reference. **Writer STOPPED; no descendants, live processes, unresolved descendant leases, or scratch outputs.**
