# Sprint EFFECT-PERMISSION-EVENT-BUFFER/20261029-r17

Status: admitted by Luna under the unchanged ongoing Simple-sub inference/executor goal after R16 `CLOSED_COMPLETE_CONDITIONAL` and the sprint-end selector recommendation.

## Baseline and authority

R16 pins the event-generation protocol and exact source provenance. Direct Lean dependency: `notes/theory/lean/YulangClosure/FormalPermissionArenaEvents.lean`, SHA-256 `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3`; R16 admission manifest SHA-256 `f4174b99fe8f4c9935740cd3d0a5183cdaab601818d834a6df02370d5668aa18`. R12/R13/R15/R16 roots and the original goal are inherited unchanged.

Pinned read-only source mapping is in `tasks/agent-loop/inbox/effect-permission-event-buffer-r17-source.md`. `term.rs` has four direct production append sites, including the `intern_structure` writer; do not claim a global six-event upper bound for every constructor. R16's selected live-variable/function protocol remains conditional. Existing source-hash mismatch and deferred Git disposition remain in force.

## Fixed proof result

Create `YulangClosure.FormalPermissionEventBuffer` with a faithful six-slot representation of `TermCapacityEvents` and prove:

1. Initialization and every bounded push preserve occupied-prefix/empty-suffix layout and exact order.
2. `take` returns exactly the occupied sequence and resets every slot and `len`.
3. Flattening the fixed array produces exactly that sequence, with no omission, duplication or stale event.
4. R16's selected derived suffix satisfies `Fits` from an empty entry.
5. A normal return from a selected constructor wrapper empties the buffer before sampling/mapping, including constructor `Err` and early sampler `Err`; consecutive selected wrappers preserve empty entry when no direct/interleaved arena mutation occurs between them.

Keep arbitrary initial prefixes separate. Do not infer initial emptiness for an unlinked Rust execution, arbitrary interleaved mutation, panic before drain, or the complete recursive candidate caller. Preserve `intern_structure` as an explicit writer outside the R16 six-stage constructor protocol; this packet does not certify its maximum event batch.

## Lanes and exact permissions

- Proof owner: one fresh registered `lean_prover`, 600 seconds. Write only `notes/theory/lean/YulangClosure/FormalPermissionEventBuffer.lean` and `tasks/agent-loop/inbox/effect-permission-event-buffer-r17-proof.md`.
- Source owner: primary Luna, read-only on Rust/Lean sources; write only `tasks/agent-loop/inbox/effect-permission-event-buffer-r17-source.md`. Source analysis is complete.
- Independent review: fresh nonauthor `compiler_referee`, 250 seconds, only after a complete successful primary audit; write only `tasks/agent-loop/inbox/effect-permission-event-buffer-r17-review.md`.
- Primary Luna: 150 seconds for contract/manifest/evidence, at most two primary audits, review adjudication and closeout.
- Total sprint envelope: 1200 seconds; zero Astra and zero descendants.

No Rust implementation edits, tests, Cargo, instrumentation, package updates, or Git staging/commit/push are authorized in this sprint.

## Audit and resource limits

Use pinned Lean 4.35.0 in a fresh isolated project copy under `/tmp/yulang-effect-permission-event-buffer-20261029-r17/`. Keep one primary-owned build/cache and run serially with `-j1`. At most two separately frozen audits, each ≤90 seconds and combined ≤120 seconds. Audit all 56 inherited R12/R13/R15/R16 roots plus every new R17 public theorem root. Preserve exact project-copy receipts, full stdout/stderr, status, resource receipt, theorem types, axiom reports and each plan. No diagnostic probe or third audit.

## Falsifiers and stop conditions

Stop and return the exact counterexample if a stale populated suffix survives `take`, `flatten` drops/reorders/duplicates a snapshot, reset happens after sampling, the selected normal wrapper path cannot establish empty entry, or an unmodeled direct/interleaved writer invalidates the stated call sequence. Stop on input hash drift, path conflict, worker/audit budget expiry or inherited root failure. Constructor panic before drain and overflow behavior remain explicit; do not silently treat panics as `Result` errors.

Primitive allocation/reserve behavior, snapshot authenticity, initial buffer provenance, page identity, sampler availability/execution, full recursive caller execution, whole-source/native correspondence, original parent, effect hygiene, consumer residual, soundness, principality, termination and production remain OPEN.
