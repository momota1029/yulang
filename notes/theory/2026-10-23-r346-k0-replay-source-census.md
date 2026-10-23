# R346 primary source census — ordinary K0 bound replay

Status: frozen primary-authored, read-only census. It is not a proof or independent review.

Baseline: branch `research/simple-sub-intrusion`, commit `a5edc8ee72b7fb1062b8d83d0753b1d43ec76702`. Source hashes are fixed in the R346 contract. All five matched when read. No source file changed during this census.

## Exact path through insertion and replay

For an ordinary owner-emitted bound, `candidate_insert_bound_with_evidence` first canonicalizes the owner and endpoint, calls `candidate_bound_origin_with_evidence`, and then appends the endpoint to the corresponding Value/Effect lower/upper direct-row or exact-endpoint vector. It reads the addressed slot back and checks the complete `BoundKey` before publishing the evidence emission (`candidate_extrusion.rs:702–875`). Therefore relation-fiber admission can precede physical append; the R338 interpretation explicitly accounts for this pre-append owner-side attachment.

`candidate_bound_origin_with_evidence` chooses the explicit origin, active processing pair, or bound pair. For ordinary `OwnerEmission`, it constructs a bound relation and then records/deduplicates origin evidence (`candidate_effect.rs:530–590`). `candidate_context_bound_for` interns the bound-pair relation from the ordinary parent context, adds its derived edge, and calls `attach(bound, child)` (`candidate_context.rs:3888–3937`).

`attach` first scans the exact key's chain and returns if the same `RelationId` is already present. Otherwise it inserts a new vector node at the map head and retains the prior head as `next` (`candidate_context.rs:3264–3295`). `bound_cursor` reads that head; `bound_entry(i)` returns the node's `RelationId` and next pointer (`3269–3275`). Thus each distinct fiber is a fresh head-prefix element; duplicate admission of the same key/relation does not move the cursor. This describes exact retained relation identity, not a collapse by pair equality or source spelling.

`candidate_replay_bound` snapshots the physical opposite-bound count, selects each indexed opposite endpoint, orders lower/upper according to polarity, constructs the same-sort task and exact input `BoundKey`s, then calls `candidate_context_begin_replay(..., false)` and `candidate_context_drive_replay(..., None)` (`candidate_extrusion.rs:877–936,1070–1112`). Positive admission scans the existing upper lane; negative admission scans the existing lower lane. Value and Effect use parallel physical storage and the same orientation.

## Incremental relation-fiber join

For one exact ordered pair of input keys, `candidate_context_begin_replay` reads current heads and the last published heads from `replay_heads` (`candidate_context.rs:3992–4014`). Ordinary replay uses the recorded frontier; only `incoming_use` resets the old frontier to `(None,None)`, and that route is outside this packet.

Nodes are immutable once linked. Given old heads `(L₀,U₀)` and current heads `(L,U)`, each current fiber chain is its new prefix followed by the old suffix. The exact product difference is the disjoint union

```text
newLower × allUpper  ∪  oldLower × newUpper
```

The first loop is `(heads.0, old.0, heads.1, None)` and the second is `(old.0, None, heads.1, old.1)` (`4015–4059`). A half-open cursor walk stops before the saved node. The loops cover new/new and new/old pairs once in the first region, and old/new pairs once in the second; old/old pairs are excluded. If one frontier is unchanged, its corresponding interval is empty. With no new fibers both intervals are empty. Because `attach` suppresses the same `RelationId` at one key, repeated exact admission changes neither head nor product.

For each visited pair, the code obtains the endpoint pair from `task_pair(task)`, combines the lower/upper contexts and source sets, composes scoped flow, interns a child relation, records the exact `Dependency::Replay { child, lower, upper, lower_input, upper_input }`, and adds that child to the retained batch unless the exact dependency key already exists (`4036–4057`). After the loops, it publishes `heads` only if they changed, then stores the exact children in a `ReplayOperation` (`4060–4073`). The dependency key includes both relation IDs, child relation, and ordered input keys; a key hit is not evidence of processing by itself.

Potential proof seam: after all product loops, cursor publication precedes checked child-byte accounting and operation insertion. This ordering is inside the actual route mutation path; the producer must establish which successful K0 prefixes can observe it and how any failed publication is handled. Do not silently extend the result to failed private routes or infer that rollback is a semantic goal.

## Work ownership, cache, and ordinary return

`ReplayOperation` owns the exact task, input keys, heads, child relation vector, queued and consumed frontiers, and retirement/wait state (`candidate_context.rs:126–143`). `candidate_context_drive_replay(..., None)` transfers the next owned child to the ordinary typed worklist; it can return `Queued` while that work remains with the outer drain (`4156–4228`). The queue transfer records the replay acknowledgement before insertion, and `transfer_replay_child` checks exact operation/index/frontier ownership (`lib.rs:15223–15250`; `candidate_context.rs:2397–2438`). On terminal acknowledgement, `complete_replay_child` validates the exact current index and increments consumption; retirement requires all child slots consumed (`candidate_context.rs:2397–2445`; `lib.rs:14881–14945`).

The ordinary drain reaches diagnostics only from Transport with no current item, empty typed worklist, and settled intrusion (`lib.rs:14289–14418`; the synchronous loop is `14873–14877`). While the queue is empty, `settle_candidate_intrusion` clears `dirty` immediately when there is no pending intrusion parent; otherwise it processes all pending parents before clearing (`candidate_intrusion.rs:568–594`). ReturnReady follows diagnostics and all owned replay acknowledgements; terminal return consumes the frame and restores its saved processing identities (`lib.rs:14881–14945`). This is a local successful-driver condition, not global fairness or whole-solver termination.

Pair-cache limit: `pair_is_current` requires both a typed-pair memo and the current processing relation's generation stamp (`lib.rs:13507–13518`). `mark_candidate_pair` writes that stamp at admission, before apply/decomposition has finished (`candidate_intrusion.rs:430–454`; the call path is in `record_typed_pair_admission`). Thus the stamp alone cannot certify prior completion. R345 proves retirement of its contracted generated K0 obligations using their actual bound witnesses; it does not prove all cache hits or all temporal/fiber cases. The R346 proof must establish the exact support of any cache-suppressed pair it includes. If that bridge does not follow, leave cache-hit coverage OPEN.

## Census disposition

This census confirms the exact implementation shape targeted by R346: owner-emitted fibers are linked by exact key and relation identity; replay progress is pair-keyed; the frontier delta uses the two-region product; and the resulting child batch is owned across queue, typed drain, and acknowledgements. The source path is more specific than a set-level description: physical endpoint replay and contextual relation-fiber replay are two connected but distinct loops.

No authentic K0 counterexample or concrete source-qualified defect was found by this read-only census. A missing fiber/interaction would establish a coverage gap, but not by itself a failure of `Sol(H)` preservation: the existing Value preorder or Effect inclusion may already entail the comparison from its two bounds. No code edit is authorized; disposition is `NO_SAFE_CODE_SLICE`. Cache-completion support and any dependency-key hit remain explicit proof obligations, not passed claims.

The census inspected the five owners pinned by the contract. It used source reading and hash verification only: no tests, builds, execution probes, edits, Git mutation, or network operation.
