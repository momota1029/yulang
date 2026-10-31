# EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1 — independent review

Fresh non-author compiler_referee: `/root/canonical_export_final_review`; read-only. Verdict: **CLOSED_INCOMPLETE warranted; Rust evidence did not pass.** Contract SHA `70a69a66a9367114a70970d73825942bfebfc08a2143b7288f057b76088aaf4b`; final Rust handoff SHA `ea9d9e74f383adefb120abcc619c8395404e20f41d0f1acc71764df0fba20d8e`.

## Findings

- **BLOCKING — nontrivial transport remains unobserved.** Both runs fail the strict `r != q` assertion. Run 1: `[(19,19),(21,21)]`; run 2: `[(21,21),(23,23)]`. q→r is ineffective on these observations. A genuine source construction with `r != q` and a passing test is still required; do not synthesize or weaken it.
- **MAJOR — delegated source-site recording uses the wrong coordinate.** Producer `candidate_effect.rs:2428` records `context.position()`, which resolves to `annotation.position`; `FormalEffectSite` at `:1657` records `effects.position`. The join at `:3224` compares them and fails 0/1 at `:3227`. Delegated ports at `:2486` and order grouping at `:235` also use the broader annotation position, so sibling nested rows may be conflated. Preserve nested effect-row position plus enclosing occurrence/path, then join both allocations to that source site. Do not relax the match.
- **MINOR — final frozen Rust handoff contains stale run-2-pending/no-tests wording** at lines 26, 28–36 and 46, contradicted by its final results and run-2 receipts. Preserve the frozen submission; primary outcome must explicitly supersede those sentences and state both runs completed, compiled, executed and failed, with both invocation slots spent.

The new q join is structurally sound: canonical intern event is matched to the `Graph.rows[Node::Row]` key by capture/node/polarity, then to the exact returned permission port. Per-origin concrete operands are matched to that origin's exact exported permission. Run 2 reached these joins before the `r != q` failure. These finite checks still do not authenticate arbitrary native snapshots or establish universal source/native correspondence.

| Falsifier | Static assessment |
|---|---|
| Alter q while actual captured row is fixed | Rejected structurally when q differs; both observed runs have r=q, so the observed q→r mutation is ineffective. |
| Both exports use same wrong concrete set | Rejected against each retained origin's concrete operands; run 2 reached these assertions. |
| Wrong owner wrapper | Exact wrapped owner and capture filtering reject. |
| Omit second origin | Origin count and export count reject. |
| Swap sibling ports | Per-origin node/export join rejects statically, but later explicit swap assertions were not reached after the earlier r!=q failure. |

These are static mutation analyses, not executed mutation tests. Neither Rust test passed.

## Receipt verification

All source, contract, final handoff and twelve raw receipt hashes match. Both feature-correct focused runs compiled, then exited 101:

| Run | Tests | Wall | Peak RSS | Swaps |
|---|---|---:|---:|---:|
| 1 | 0 passed, 2 failed | 60.14 s | 1,664,404 KiB | 0 |
| 2 | 0 passed, 2 failed | 6.40 s | 1,116,748 KiB | 0 |

Combined wall 66.54s, within 180s. Run 2's input manifest matches final source/dependency pins. Run 1 manifest matches its historical source pin, but that source snapshot is not retained; reviewer authenticated the manifest, not reconstructed historical bytes. Preflight memory/CPU affinity are not encoded in raw time records.

Run 2 owner test passed concrete, actual captured-row, polarity and returned-port joins before failing `r != q`. Symbolic test passed memo-count/name and paired delegation checks, then failed source-site matching; later tail/port materialization assertions did not run. Parent/native/production gates remain OPEN.

**STOPPED:** read-only; no edits, Git, build/tests, Cargo/Lean invocations, or descendants.
