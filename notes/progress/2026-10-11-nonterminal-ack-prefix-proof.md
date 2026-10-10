# Nonterminal typed-drain acknowledgement prefix

Date: 2026-10-11
Status: unreviewed research checkpoint; conditional constructive derivation and pinned source bridge, not an established production theorem.
Baseline: `6a962826ab46d7f58529f7162aa016997ed5418d`, branch `research/simple-sub-intrusion`.
Producer: leaf `/root/ack_prefix_constructive_proof`; exclusive lease: this note only.

## Objective, authority and method

Derive the next acknowledgement-preparation gate by induction over the retained pending prefix, followed by one pre-pop/append step and ordered terminal consumption. Authority is the user-approved private candidate suspension contract §3 (exact continuation ownership, child completion distinct from generation) and §6 (route rollback, fallible reservation before mutation). The terminal handoff note supplies the reviewed synchronous foundation, not authorization to claim a nonterminal resume implementation. `tasks/current.md:8782–8788` names this next gate and leaves Dispatch/Function atomic.

The prior falsifier supplies a conditional witness: commit with one pending old acknowledgement, then prepare a new distinct handle and append without preparing the old position. Its debug assertion fails; without that assertion the counter denotes the wrong prefix and old completion lacks undo. This derivation addresses that exact counter/journal mismatch. It does not establish the witness's source reachability.

Rules read: orchestration budget; agent orchestration, especially Model routing and Astra escalation and Proof delegation and decomposition; research lab; design authority; compiler engineering, including proof-obligation economy; Git concurrency. The `yulang-proofs` skill was applied. No delegation or Astra assignment occurred.

## Frozen statement and hypotheses

Fix one retained topmost unfinished `TypedDrainFrame` F at a route entry, an ordered acknowledgement vector A of length N, completed cursor d, prepared cursor p, and a current transaction journal J with checkpoint C. Each A[i] is the exact pair `(ReplayOperationId, child index)`. Operation IDs may repeat, including in separated positions. The vector, operation identities and child indices are retained values, not reconstructed from task endpoints. A successful preceding commit has set `p=d`; write this initial cursor as d0.

For every finite N and every `0 ≤ d0 ≤ N`, the following rule prepares the pending prefix safely, provided:

1. F and each referenced pending replay operation remain owned. Their fields and ordered child vectors satisfy the existing replay invariants, including `consumed ≤ queued ≤ children.len()`. The ordinary identity validators remain active; no ID uniqueness assumption is added.
2. The route checkpoints the context before updating F. `prepare_typed_drain_update` successfully retains the original F before its first mutation. All subsequent frame mutation/removal in this route uses that retained snapshot. No successful commit occurs invisibly inside the rule; a new commit starts a new route and resets the frontier again.
3. Each pending position is prepared by a successful call to `prepare_replay_child_completion(A[p], true)` against J. The increment of p occurs only after this call returns success. Any fallible accounting/sample step propagates its error to the route failure owner before dispatch resumes.
4. Until p=N, the driver performs no further dispatch side effect, worklist pop or acknowledgement append. During prefix preparation, A and d do not change and no replay completion occurs. Reservations/frame journaling are the permitted preparatory mutations.
5. Every mutation of replay `queued`, `consumed` or `retired` in the route follows the existing journal-before-mutation helpers. Journal entries survive until commit or reverse rollback, and referenced operations are not reclaimed while rollback can need them.
6. Failure invokes rollback to C. This statement concerns F and replay-operation fields; preserving a previously nonempty worklist needs its own owner and is not assumed proved here.

Required conclusion: after the rule succeeds, p=N and every outstanding position has current-route undo ownership. The existing pre-pop reservation followed by append preserves p=|A|. Successful terminal steps consume the exact next A[d], then advance d once; failures restore the pre-route drain and replay fields. Semantic completion advances d/`consumed`; journal preparation alone never does so.

The ordered-success corollary has an explicit existing validation premise: when A[d] is consumed, its operation's current `consumed` equals A[d].index. A lawful per-operation projection beginning at the retained consumed index supplies this premise if no other owner consumes those children in between. The prefix rule itself neither proves that source history nor disables the validator. Arbitrary invalid ordering still fails through the existing validator and rolls back safely.

Excluded: production/source reachability; external mutation disjointness or incidence deferral; lifecycle observation withdrawal/recomputation; §7 authentic regression; general Dispatch suspension; soundness, principality, effect hygiene, complete Call meaning and F5 cutover. No new source restrictions, rejection policy or semantic decisions follow.

## Invariant with an actual journal meaning

For a route with entry cursor d0, use this invariant:

```text
0 ≤ d0 ≤ d ≤ p ≤ |A|
For each position i in [d0,p), its successful preparation event
has a distinct, still-retained entry e(i) in this route's replay undo.
e(i).id = A[i].operation, and e(i) records that operation's
(queued, consumed, retired) immediately before the preparation event.
e is strictly increasing in journal order for successive preparation events.
No position i ≥ p is certified by this frame's prepared frontier.
The original F, including A, d, p, stage, current item, Function cursor
and original acknowledgement allocation, remains owned by drain undo.
```

During prefix preparation d=d0. Afterwards entries for `[d0,d)` remain retained even though those acknowledgements have completed in the current route; entries for `[d,p)` cover the outstanding prepared prefix. A[i] below d0 completed in a previous committed route and needs no undo for that past completion.

This is an exact correspondence of positions to successful reservation events, not a count of unique operation IDs. J may additionally contain transfer or other mutation entries. Such incidental entries can protect the same operation, but do not make an unprepared position advance p. `prepared_acks` certifies reservation ownership only. It is neither `completed_acks` nor replay generation/queue progress. `terminal_prepared` concerns frame-update preparation and likewise does not certify semantic completion.

The mapping e is proof notation describing existing concrete append events in `replay_operation_undo`; it proposes no runtime relation or new metadata layer.

## Constructive derivation

**Base.** At commit, the old route releases its undo and resets p=d. At new route entry d0=d=p, so `[d0,p)` is empty. Retain F's route-entry snapshot before changing the frontier. If this reservation fails, the live F has not been replaced or changed; no dispatch/pop/append has occurred. A is fixed and the bounds hold.

**Prefix step.** Suppose d=d0 and p<N. Read the retained A[p]. Its completion-preparation helper validates that the operation exists, `A[p].index < queued` and `A[p].index ≥ consumed`; it then reserves one journal slot and pushes the snapshot. It changes no replay cursor. On failure p stays unchanged. On success associate position p with that new journal entry, then increment p by exactly one. The mapping is extended by one increasing journal position and the bounds persist. This argument does not identify positions by operation ID: a repeated ID gets a further entry. Accounting failure after this step aborts the route and invokes rollback; it cannot authorize the driver to continue.

**Finish.** Each successful prefix step decreases N-p by one, so at most N-d0 successful steps prepare all pending positions. Validation, allocation or accounting can instead abort; success is not promised for arbitrary invalid retained state or failed allocation. The gate now permits the next dispatch transition, with p=N.

**One pop/append.** If the front work item has acknowledgement b, the existing code reserves acknowledgement-vector capacity and prepares b's completion undo before popping. A failure before pop leaves work ownership in the queue (subject to the route owner on rollback). If these fallible operations succeed, pop and retain the exact current item, append b at old position N and increment p once. The previous prefix is unchanged; associate the append position with b's successful pre-pop journal event. Thus new p=N+1=|A|. An item without an acknowledgement leaves N and p unchanged. This step can be repeated without scanning the old prefix again within the same route. A new commit resets p to d and requires the gate again.

**Terminal.** Only completed diagnostics permit the existing Acknowledgements stage. With p=|A|, terminal consumption needs no second completion reservation for A[d]. The complete helper checks `consumed == A[d].index` before mutating the operation; success increments its consumed cursor once and may mark the operation retired. Only after that success does the frame increment d. The journal mapping remains present, d≤p still holds, and global consumption order is A[d0], A[d0+1], …. When d=|A| the frame becomes ReturnReady; only the subsequent terminal return step removes it and restores processing scopes. The empty suffix d=N needs no replay reservation or consumption.

If a terminal prefix commits early, its new d becomes d0 for the next route and p resets to it. Existing terminal preparation then reserves the next position only when d=p. It advances p after preparation, consumes after exact-index validation, and advances d after successful consumption. The same invariant covers this synchronous terminal behavior without requiring another full pending-prefix scan for terminal-only resume.

**Failure and repeated IDs.** Drain rollback restores the retained original F or re-pushes it after removal, then truncates new frames. For any operation r, project the chronological journal onto r: snapshots s1,…,sk each precede the protected mutation interval. Replaying entries in reverse restores sk, then …, then s1. Since the earliest protected mutation was preceded by s1, the final fields equal their pre-route values. Other operations are independent map entries. Operations created in the route are subsequently removed by the existing creation frontier. No deduplication is needed; reversing only the final occurrence is generally incorrect.

For example, the existing terminal-only sequence for one handle can reserve child 0 at `consumed=0`, consume it, reserve child 1 at `consumed=1`, then consume it and fail. Reverse restoration reaches 1 and then 0. Keeping only the latest snapshot would leave 1. If full-prefix preparation reserves both children before either completes, both snapshots may instead have consumed=0; the same reverse proof applies. It must not infer correctness of last-only restoration from that special schedule.

Repeated identical `(operation,index)` acknowledgements are not silently collapsed. Both can pass prefix preparation before completion, but after the first consumes that index, the second fails `consumed == index`; route rollback restores both cursors and F. Preparation is therefore not a proof of successful consumption or duplicate-child legality. Repeated IDs with successive lawful child indices complete through the existing validation, including the two-child same-handle terminal fixture.

These proofs establish logical drain/replay rollback and preservation of the original frame acknowledgement allocation. They do not claim allocation capacities of undo vectors shrink on failure or that historical resource peaks disappear; the source retains and accounts for such physical storage.

## Pinned source correspondence and missing owner

All semantic source reads below use `git show 6a962826a:<path>`.

| Owner / exact baseline locator | Established source fact / remaining premise |
| --- | --- |
| `candidate_context.rs:20–45,1714–1724` | TypedDrain carries A, d, p, current item, stage and Function progress; begin constructs empty A and zero cursors. No distinct semantic completion is inferred from p. |
| `candidate_context.rs:1674–1683` | Commit releases drain undo, resets every retained p to d, and clears terminal preparation. This establishes the next-route base, not a resume call. |
| `candidate_context.rs:1725–1755` | Drain-update preparation fallibly clones the live allocation while moving the original frame to undo; accounting includes active and undo frame acknowledgement capacities. Must be called before nonterminal frame mutation. |
| `candidate_context.rs:1815–1858` | Completion preparation appends one exact operation snapshot per successful transactional call; no ID dedup. Queue transfer prepares before increasing queued. Completion validates exact consumed index before advancing. |
| `candidate_context.rs:1568–1600,1654–1708` | Reverse undo restores drain/restoration/replay state; transactional retirement retains operations until commit, with final replay retained through a live restoration parent. |
| `lib.rs:11895–11965` | Fresh synchronous drain requires empty worklist, resets current/stage, can settle intrusion, reserves the front acknowledgement before pop, then appends with the assertion p=|A|. There is no pending-prefix preparation ahead of this seam. |
| `lib.rs:12285–12342` | Terminal helper accepts topmost Acknowledgements/ReturnReady only; prepares before consumption, validates bounds, advances d after completion, and removes ReturnReady with scope restoration. |
| `lib.rs:12386–12403` | Enqueue reserves queue capacity and transfers the exact acknowledgement before infallible queue insertion. |
| `lib.rs:9162–9208` | Successful route calls context commit; failed route invokes rollback. |
| `candidate_context_tests.rs:4320–4505` | Synthetic terminal fixture has two acknowledgements of one operation; tests specify partial commit/resume, injected preparation failure, exact frame/cursor rollback, final parent handoff and active/undo allocation accounting. Read only; not executed here. |

**Exact missing owner:** the baseline has no callable retained nonterminal typed-drain resume boundary that first snapshots F and prepares A[d..] before its saved stage runs. The fresh synchronous loop cannot supply it: it creates a fresh frame, requires an empty worklist, and mutates/reset stages before pre-pop reservation. The terminal helper explicitly rejects nonterminal stages. The proposed loop is therefore a conditional future operation, not an implementation theorem.

The rule can be expressed without a reconstruction layer:

```text
validate retained frame/frontiers and route ownership
prepare_typed_drain_update(F, true)
while F.prepared_acks < F.replay_acks.len():
    ack = F.replay_acks[F.prepared_acks]
    prepare_replay_child_completion(ack, true)?
    F.prepared_acks += 1
    account newly retained storage, propagating failure
resume the retained stage
```

This is a proof specification for the missing owner. It does not adopt an implementation. The gate must precede saved-stage side effects as well as later pre-pop preparation; placing it only immediately before an acknowledged pop is insufficient when dispatch can mutate first or pop an item with no acknowledgement.

There is a further whole-route bridge: `begin_route_transaction` at `lib.rs:8970` expects an empty worklist; `rollback_route_transaction` at `9637` clears the worklist. A retained nonempty-worklist resume must establish its own exact queue ownership/rollback. This note's drain/replay induction cannot certify that by appealing to the old transaction contract. Earlier prefix failures perform no queue operation, but whole-route rollback still needs its actual owner.

No second equivalent proof attempt was launched. The missing prefix ownership is a §6 safety obligation (A), with constructional evidence already known at the journal append. Retaining/reestablishing that evidence at the resume owner removes reconstruction debt (D); another ID-based reconstruction or an ID-uniqueness restriction would not establish the missing source call. This audit changes no gate status.

## Checks, dependencies and resources

Checks run: read-only `git rev-parse HEAD`; pinned `git show` range reads; `rg` owner/caller searches; baseline versus live SHA256 comparisons for the seven dependencies below; leased-note trailing-whitespace inspection. All seven dependencies matched at inspection. No executable model, test, Cargo/build, formatter, measurement, Git mutation, nested CLI or child agent was run. Only short read-tool shell utilities were used; reasoning time/RSS and their aggregate CPU/RSS were not measured. Wall-time budget: at most 30 minutes, static inspection only. Primary remains the verification and independent-review owner.

```text
24909fb9a09e6f9d383e5b1f8f4f8db9d5f7e587a1ed5bbb6a47ead77e140831  crates/yu-solver/src/candidate_context.rs
77a3c4bdb48d438f7e5678c35302ad2aa1f6665ca9cbb8f3fdc0a48e730a30f4  crates/yu-solver/src/lib.rs
3a63e52796fcc568e50f59462691ccde77acac5a0bcc0d02d550402811e31ba3  crates/yu-solver/src/candidate_context_tests.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8  notes/progress/2026-10-11-typed-drain-terminal-handoff.md
8f7e99ae225e312384bc2ec101a13392d8e935eb349edd5483316d16eb4c32f7  notes/progress/2026-10-11-local-use-restoration-continuation-falsifiers.md
3866519d215626aed59db39317d7b71ff6376c302e606948ef3196f99a058681  tasks/current.md
```

Requested runtime: registered `prover`, `gpt-6.1-sol` / `high`. `.codex/config.toml` registers that role and sets Sol/high subagent defaults; `.codex/agents/prover.toml` has no model/effort pin. Observed effective role/model/effort metadata is unavailable to this leaf and remains **unknown**; configuration and packet text are not runtime proof. No hot reload, override success or Astra execution is claimed.

Changed paths: this exclusive note only. Freeze this note before independent review. No implementation delta has been supplied or inspected. One next action: primary locates a legitimate retained nonterminal resume caller and its route/queue ownership before applying this rule; if absent, retain this conditional derivation without claiming the source gate closed.

## Commit packet

- Exact lease: `notes/progress/2026-10-11-nonterminal-ack-prefix-proof.md`.
- Baseline: `6a962826ab46d7f58529f7162aa016997ed5418d`.
- Changed dependency hashes: none at the recorded seven-file comparison; concurrent later deltas require primary revalidation against the hashes above.
- Claim/review status: producer-only unreviewed conditional derivation; no self-certification, theorem closure, source reachability or gate promotion.
- Checks already run: pinned static source/rule/authority reads, caller searches, seven dependency hash comparisons and leased-note trailing-whitespace inspection; no runtime tests or probes.
- Proposed checkpoint message: `Record conditional nonterminal acknowledgement-prefix derivation`.
- Shared-record delta left for primary/curator: record the concrete pending-prefix preparation invariant and missing resume owner; preserve full suspension, retained-worklist rollback, lifecycle and §7 gates as open. No task/index/theory-status/authority file was edited.
