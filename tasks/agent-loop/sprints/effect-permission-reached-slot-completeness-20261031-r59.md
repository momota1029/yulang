# Sprint EFFECT-PERMISSION-REACHED-SLOT-COMPLETENESS/20261031-R59

Status: ADMITTED, bounded research only. No production or whole-language closure.
Branch: yulang3; baseline: 3c103d8d1 (R58 closeout pushed).
Original goal: Yulang inference/executor soundness, effects, principality, termination.
Authority: rules/goal-driven-sprints.md §§1–4; unchanged Simple-sub source domain and A/B claims.

## Outcome

Prove the full candidate converse for the actual bounded LIFO search:

> From the initial state, every `Checked` target candidate occurs in the results of a successful complete `Run`.

R58 R1 established soundness and preservation only for candidates already queued/found. R2 added physical-row generation/scheduling and an omitted-candidate witness, but remains unreviewed and does not establish the converse. R59 must prove Support-member generation, frontier coverage from the initial state, preservation through arbitrary worklist prefixes, and elimination of the queued alternative at successful exhaustion. Combine with the exact R58 R1/R2 checked-path/soundness results; do not stop after Support alone.

Required falsifiers: the R2 omitted-candidate witness; mixed physical/Support prefixes; cyclic dependencies; competing paths; reversed ascending-push/LIFO order; reached read/resource failure; Entry/Catch policy distinction. A successful exhaustion theorem may not skip a reached failure or allocation failure.

## Pinned inputs

- R58 research-only commit: `df3d86fcf` (R2 is separately committed, exact bytes retained).
- R58 module: `notes/theory/lean/YulangClosure/ReachedSlotSearchR58.lean`, SHA-256 `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.
- R58 R2 proof handoff: `tasks/agent-loop/inbox/effect-permission-search-correspondence-r58-proof.md`, SHA-256 `0f21458b14cf34ca6712c85858cc02fac6f4733f14e14ffa174c43034495781f`.
- R58 R1 independent review: `tasks/agent-loop/inbox/effect-permission-search-correspondence-r58-review.md`, SHA-256 `7ab2a682b11fbc2e8fb49ace115fa0902f6e8bab1c9e43d91492e217504dc9fe`; it covers R1 only and records the precise queued-target limitation.
- `candidate_receiver.rs`: SHA-256 `8d491e52ed9922e982c93a694e8c065bb065ca5f50bff76c255a5303eba1e016`.
- `candidate_context.rs`: SHA-256 `8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89`.
- Preserve R57/R50 model, review, reader/source pins and every open boundary recorded in R58. Confirm pins before using; stop and report any mismatch.

## Lanes, exact leases and resources

- Lean proof: `/root/r52_proof`, constructive multi-stage packet. Write only `notes/theory/lean/YulangClosure/ReachedSlotCompletenessR59.lean` and `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-proof.md`. Reuse the existing R58 Lean model and pinned Lean 4.35.0; bounded stdin audit only in `notes/theory/lean`, one CPU, `-j1 -M1024`, at most 120 seconds per audit. Preserve theorem types, full transitive axiom audits, input/stdout/stderr hashes, and resource receipts. No project axioms, proof holes or native-evaluation assumptions.
- Rust/source: `/root/r52_rust`, exact source mapping of Support decoding, branch scheduling and ancestry behavior against `certified_lower_paths`; read-only `candidate_context.rs`. Write only `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-rust.md`. A private source change is allowed only if it materially clarifies correspondence; if needed, first stop and request a primary lease amendment. No tests/build/Cargo/formatter/typecheck.
- Independent review: `/root/r48_review`, read-only. First authenticate all 43 R2 roots and the omitted-candidate witness. After R59 artifacts freeze, review the converse, counterexamples, exact hashes and source mapping. Write only `tasks/agent-loop/inbox/effect-permission-search-completeness-r59-review.md`. R2 intake uses 450 seconds and final review 750 seconds; this does not reset or transfer any earlier review budget.
- Primary: `/root`; owns contract/state, exact leases, adjudication, review placement and Git.

Total fresh budget: 6000 seconds: Rust 800, proof 2800, review 1200 (450 R2 intake + 750 final), primary 1200 including up to 500 seconds closeout; Astra 0. No R58 balance transfer. Existing checkout/toolchain only: no builds/tests/typecheck, cache, scratch, target, persistent process, environment or worktree.

Before dispatch, synchronize the live roster and require all R58 writers STOPPED. Do not reclaim unknown/quarantined paths or assignments. Preserve all 32 pending questions, all UNKNOWN observations, and all 12 quarantined paths. Keep `current.json` <=16 KiB. Each author freezes exact bytes and reports WRITES STOPPED before review. Stop on a genuine converse counterexample, source-policy change, budget, user STOP or session end.

## Boundaries

This sprint addresses only successful-search candidate completeness in the R58 operational model. It does not prove a concrete borrowed owner-reader encoding, general `LocalDecode`, Rust small-step simulation, complete resource equivalence, parent A/B, inference soundness, principality, termination, full hygiene or production authority. A conditional model theorem, finite witness, successful Lean stdin audit or R58 checkpoint is not parent-theorem closure.
