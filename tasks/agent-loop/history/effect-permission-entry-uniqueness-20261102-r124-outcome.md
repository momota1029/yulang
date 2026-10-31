# R124 outcome — Entry schedule uniqueness

Contract: `tasks/agent-loop/sprints/effect-permission-entry-uniqueness-20261102-r124.md`, SHA-256 `aca5c91ba535c9e2342bcd593bb6e8cffc062a506966f2777fcb818526fbc82e`. Baseline: `8914838a21ab2dcf62ccf14dddcec3ea91fd8446`. Exact source/theory pins are in the manifest and admission.

## Result

**PASS for bounded immutable-source uniqueness evidence.** A successful `SccPlan` partitions and schedules the authenticated ordinary definition set without duplicate roots. Its consumer loops use the retained plan; the capture/visit state prevents revisiting a Lambda within one ordinary non-interpolation carrier, yielding at most one `FormalEntry` per preallocated registration on that path. No reachable duplicate-entry counterexample was found there.

The proof handoff initially misstated that repeated `Work::Visit` allocated a fresh registration. Independent review caught this major source-correspondence error. Revision 2 corrects it: registration/recipe ranges are preallocated once per emitter before traversal; a repeated Visit in that emitter reuses the same registration, while a separate emitter call/carrier may allocate a fresh range. The corrected distinction is authenticated against the pinned source.

Interpolation remains conditional on `SourceNodeKey` injectivity at its unpinned construction owner. The result also does not establish global semantic uniqueness across multiple HIR members/carriers or a same-registration replay/reuse law. Do not generalize the ordinary non-interpolation induction across those boundaries.

## R39 interpretation

Schedule uniqueness is not a premise of existing R39 `Valid` or its local successful-publication implication. It concerns inference progress/admission: whether an otherwise ordinary input reaches a guard that rejects repeated use. Each publication-reaching invocation still needs a concrete same-PRE Rust-to-R39 projection, exact identity/collection equations and retained permission witness. Interpolation identity and R121's consumer-read interpretation are separate open obligations.

## Frozen evidence and independent review

- Source handoff: `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-source.md`, SHA-256 `8a29f9eb9ba2ca7d5c45a2838ac81195887937d66b33776f3b8a8c2003d66d16`.
- Proof handoff revision 2: `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-proof.md`, SHA-256 `a21d5cfef24dac72baaa32629c1c36b7c9826fde90b8d42ed2bb329dc76ce86c`. Revision 1's prior hash and correction are recorded in the handoff.
- Fresh independent compiler referee: **PASS after correction**, no remaining findings. The reviewer authenticated the pinned blobs, identified and closed the registration-reuse finding on r2, and confirmed all remaining boundaries. Reviewer wrote no file; this outcome is the primary review receipt.
- Source, proof and reviewer workers are STOPPED: `/root/r124_entry_uniqueness_source`, `/root/r124_entry_uniqueness_proof`, `/root/r124_uniqueness_review`.

No source, Lean declaration or model was changed. No build, test, compiler, Lean, checker, source execution, storage/environment probe or dirty/quarantined source read occurred. `python3 tools/agent_sprint.py check` passed as static consistency only; it is not proof or independent review evidence.

## Disposition

Close R124 conditionally. Keep interpolation identity, global multi-HIR member uniqueness, same-PRE Rust-to-R39 correspondence, R121 consumer read, R111 verification resource, parent soundness, full effect hygiene and production OPEN. Rust code integration remains **NO_SAFE_CODE_SLICE** under current gates. Continue the standing Rust/Lean goal by selecting a next bounded source/proof seam; do not create another conditional uniqueness model.

The exact R124 Git packet is limited to this outcome, the two frozen handoffs, and the primary-owned current-state record. Dirty solver/runtime files and unrelated untracked artifacts are excluded.
