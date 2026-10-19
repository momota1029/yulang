# R128 recovery implementation receipt — Luna-authored provenance amendment

## Identity and scope

- Recovery contract: `tasks/agent-loop/sprints/qualified-member-target-20261019-r128-rev4.md`, SHA-256 `dbb6c40e4add69394fbb13696e09765af1167fb652005e5cce45782076a9585a`.
- Parent remains `R119-TARGET-JOIN-1`; no source-domain, quantifier, semantic, or production-authority change.
- Original producer handoff remains immutable: `tasks/agent-loop/inbox/20261019-r128-implementation.md`, SHA-256 `b6cc72d0e11ce0ee3ce90d731788c6b5fec7b71cf8ce7d19dac08520bc3b5cf2`.
- Final candidate remains the exact test bytes in checkpoint `58d5507d400385d7b4affbda1e7c9b51779ce019` (short `58d5507d4`), file SHA-256 `65de2d91ff14af0c5408fc1f1770deefd4a4e611d7bd327d4c3bfc55b58e98fb`.
- Proof remains `notes/theory/2026-10-19-r128-qualified-member-target.md`, SHA-256 `3d1ffc3f2fa32b7b3a663235c1d8abfbef7ad42880b308fd098dc05c7e9ae786`.

## Byte provenance

The producer's handoff reports the pre-repair test SHA-256 `1e4ffaa52e14008716da3a790808cf6bae7aea5b165b71df4283d94c7c7f9571`. Luna authenticated the exact bytes in unreachable commit `72700e3b1e5ebb46045604aa0ec7ecc9c3c09a9d` (subject `Checkpoint`, parent `b37e7ab9defb1b2142976c1bef782c08a3ba6b31`); the test file there has that exact SHA-256.

Luna then repaired six `PositionId` borrow expressions so the test compiled. The exact diff from that pre-repair checkpoint to final checkpoint `58d5507d4` contains only these six source-level changes: each `artifact.position(artifact.source_position(...).unwrap())` became `artifact.position(&artifact.source_position(...).unwrap())`. The final file SHA-256 is `65de2d91ff14af0c5408fc1f1770deefd4a4e611d7bd327d4c3bfc55b58e98fb`. No fixture, assertion, expected output, or compiler source changed in this repair. The unreachable commit was inspected read-only; Luna did not create or move a Git ref to recover it.

The original implementation handoff records the producer's pre-repair bytes and correctly attributes those bytes to the producer. This Luna-authored amendment records the later primary repair and final checkpoint; it does not rewrite the producer's receipt or attribute the repaired bytes to the producer.

## Verification chronology and rev3 breach

The frozen rev3 `current.json` records one PASS of the exact HIR test after Luna's six borrow repairs, while all three fresh rev3 final reviews were still NOT_RUN. That run preceded the required independent reviews and breached rev3's verification order. This is retained as a permanent historical workflow violation; it is not retroactively cured.

The three rev3 final receipts remain unchanged: compiler/source MAJOR / not CLEAN; spec/authority NOT CLEAN / BLOCKING; regression CLEAN for the bounded test at the exact final bytes. The source test itself is unchanged from checkpoint `58d5507d4` and remains covered by the regression receipt.

Rev4 authorizes one additional execution only after fresh compiler/source and spec/authority reviews of this receipt and the exact frozen checkpoint are CLEAN, and the prior regression CLEAN remains applicable. That would be a second test execution, not a relabeling or replacement of the earlier run. No test, build, compiler command, formatter, or source edit has been performed during this recovery receipt work.

## Remaining gates and resources

This receipt establishes byte lineage and honest chronology only. It proves no method target join, execution, inference acceptance, theorem, or production behavior. R119 M/T/A, R85 adoption, all six effect-hygiene parents, and original Simple-sub/evaluator A/B remain OPEN.

Recovery receipt and hash inventory charged: 60 seconds conservatively. The cumulative R128 cap remains 1,814 seconds; no prior charge was refunded or reset. Writer stopped; frozen for fresh review.
