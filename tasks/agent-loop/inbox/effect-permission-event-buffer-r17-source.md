Sprint-ID / contract revision: EFFECT-PERMISSION-EVENT-BUFFER/20261029-r17; R16 CLOSED_COMPLETE_CONDITIONAL and R17 admitted under the unchanged inference/executor goal.
Assignment-ID: R17-source / rev1.
Direct Lean dependency: `YulangClosure.FormalPermissionArenaEvents` SHA-256 `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3`; R16 manifest SHA-256 `f4174b99fe8f4c9935740cd3d0a5183cdaab601818d834a6df02370d5668aa18`.
Pinned Rust source hashes: `crates/yu-solver/src/term.rs` and `lib.rs` are frozen in R16's 174-entry manifest. `candidate_effect.rs` remains a frozen read-only dependency with the worktree/HEAD mismatch recorded in the prior Git disposition.
Role: primary Luna source audit, read-only on sources; writes only this handoff. No proof worker was launched by this source lane.

## Buffer representation and lifecycle

`BranchTermArena::new` initializes `capacity_events` with `TermCapacityEvents::new`. The buffer is `[Option<TermCapacitySnapshot>; 6]` plus `len = 0`. `push` asserts `len < 6`, stores `Some(snapshot)` at exactly `snapshots[len]`, then increments `len`. `take` replaces the whole structure with `new()`. Thus normal initialization and push operations preserve `Some` exactly on `0..len` and `None` on `len..6`. A failed assertion panics; it is not a recoverable constructor result.

The complete production set of direct `capacity_events.push` sites in `term.rs` is:

1. `record_capacity_change`: after reading the post-operation full snapshot, append it if and only if the selected lane's capacity changed. It runs before the reserve `Result` is propagated.
2. `push`: after a page has been claimed, inserted into the directory and published in `pages`, append the PageBacking snapshot.
3. `intern_structure` error branch: if `structural_backings.try_reserve` changed capacity and the later `intern` fails, append one structural-owner snapshot before returning that error.
4. `intern_structure` success branch: after `structural_backings.push` and payload-byte update, append one structural-owner snapshot. An interner cache hit returns before this structural publication.

The read-only search found no other production writer outside `term.rs`. `take_capacity_events` has one production call site: `Session::with_term_events` in `lib.rs`. Other hits are term-arena tests and are not part of production execution.

`take_capacity_events` performs `self.capacity_events.take().snapshots.into_iter().flatten()`. It does not consult `len`; exact ordered flattening with no omission, duplicate or stale suffix follows from the occupied-prefix invariant. `with_term_events` calls the constructor closure, then unconditionally obtains this iterator before sampling or mapping the constructor result. Therefore every normal `Result` outcome, including a constructor `Err`, drains and resets first. With route accounting disabled it drains without sampling. With accounting enabled it samples in order and returns on the first sample error, but the arena buffer has already been reset. The sampler receives `&self.store` and a separate mutable execution-counter reference; this call path does not mutate `store.terms` or append term events.

Consequently, an immediately following selected wrapper call begins with an empty event buffer if the prior wrapper completed normally and there was no direct arena mutation between calls. This remains true when the prior constructor returned an error or the first sampler call failed. A panic before the drain, including event-buffer overflow, does not establish this postcondition. Any interleaved arena mutation must be modeled or ruled out by the selected call path.

## R16 constructor application and scope limits

For the R16 live-variable and positive/negative function protocol, the empty entry gives R16's `Fits [] i` from its six-new-event bound. After each selected `with_term_events` wrapper returns normally, R17's reset theorem re-establishes the empty entry for the next selected wrapper.

`candidate_formal_value_pair` sequences positive then negative live-value wrappers for Variable/Hole; for Function it recursively builds argument/result and effect terms before invoking positive then negative function wrappers. Those recursive routes may contain other constructors. R16 did not certify the full recursive caller or its interleaving; this R17 packet must not claim that larger source trace. `live_effect_term` is another live-variable wrapper. Tuple, Variant and Record paths use `intern_structure`, whose extra structural-owner events are outside R16's six-stage protocol.

The selected lifecycle proof covers the generic fixed buffer and R16's selected normal-return wrappers. It does not establish an upper bound for every structural constructor's whole event batch, and it must leave interleaved/structural operations explicit. In particular, the structural writer sites above append events around `intern`; their complete maximum batch is not derived by this source handoff. The one-owner-per-fact rule and the `TermCapacityEvents` six-slot assertion remain authoritative source behavior.

## Explicit unresolved premises

No claim is made about actual allocator availability, whether every reserve failure can or cannot change capacity, snapshot validity, truthful `pageNeeded`/journal/cache observations, initial-buffer provenance for an unlinked native execution, panic-free constructor completion, sampler availability, native page identity, or full candidate caller execution. No source edits, Rust tests, Cargo, probes, instrumentation or Git operations were run.

Source work complete; no descendant leases.
