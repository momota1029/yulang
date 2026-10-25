# R61 primary receipt — independent execution-proof reconciliation

Sprint: `YULANG3-EXECUTION-PROOF-RECONCILIATION-20261026/r61`
Contract SHA-256: `a5ad219e95459a9d103c58a9bf97ed0d225c7d69972c45787b6648af0198d881`
Baseline: `998de2a605b88a7c54db3177e21f86764016cffe` on `yulang3`
Disposition: **PRIMARY CHECKS PASS; FRESH INDEPENDENT REVIEW PENDING.** No source or proof files were changed.

## Inputs and process record

A detached worktree at the exact baseline was used. All 23 contract file pins matched. The additionally imported unchanged dependency `PaperTupleSplitExecution.lean` has SHA-256 `7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d`; it is not changed by external commit `31b1473a9d90355903e1462a4f2f75abae75e48e` and is covered by the full baseline commit. Lake resolved to `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`, SHA-256 `8ba83c98f76562d03b8dbc33f1057151ba6cbb121679dde76b2260ccc90495e1`. Lake reports 5.0.0-src+eb6cafb and Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

The runner SHA-256 is `3c39d94d4d256ba1f88e6c35bb3dcd4771639850f35bf3d816091090adb4796a`; the frozen audit source copy SHA-256 is `aa16f7e520fc56b6694e04d42e81a6f58c0ffe64b4db30c432fb2bd77692052f`; process manifest SHA-256 is `7ff24edc908202497610036645ba710a801d4e05afbe3ede31a136e4729b57cd`. Full output files and manifest remain in `/tmp/yulang-r61-execution-proof-reconciliation/`; every command had pre-created stdout/stderr files, a durable STARTED record, process completion, and output hashes.

01. `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--version']` — COMPLETED, exit 0, 0.068326994s; stdout 53 bytes SHA-256 `165f92ed239a8c7db772bf5ee9d58c59357b489951582a12c86dc9d8e06b23a2`, stderr 0 bytes SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
02. `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '--version']` — COMPLETED, exit 0, 0.067626491s; stdout 106 bytes SHA-256 `eb22144228dd41cd51a0c84af4f976cd0cef473102dcf99b60be756b11f2b95a`, stderr 0 bytes SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
03. `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', '--no-cache', 'build']` — COMPLETED, exit 0, 56.600768640s; stdout 462854 bytes SHA-256 `fb30da773ec234eaaea3f7569ac2a3931c6a1e495f55013bf028f72a9ac2cf08`, stderr 0 bytes SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
04. `['/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake', 'env', 'lean', '-j1', '-M1024', 'AuditExecutionProofs.lean']` — COMPLETED, exit 0, 5.430312608s; stdout 2080387 bytes SHA-256 `6e3eee81ffb975b006b7c53441c2821fd3dbc0acd02f856427e3adb4312f705a`, stderr 0 bytes SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.

Total checker time: 62.167034733 seconds of the 240-second cap. All four calls completed, exit 0, with no timeout; no retry occurred. Calls 3 and 4 used the corrected Lake/Lean argument boundary.

## Audit validation

The complete 2,080,387-byte audit output was passed to the existing `validate_audit(output, names)` implementation in `.agents/skills/yulang-lean-proofs/scripts/check_lean.py`, using the ordered names independently extracted from the full BEGIN marker sequence. Result: PASS for 1,368 unique ordered theorem declarations, each with a printed type and complete axiom report. The 11 module counts are 474, 57, 16, 399, 70, 14, 140, 28, 87, 71, and 12 (sum 1,368). All 26 required public roots in the frozen audit source are present; all three required typing constructors are reported; completion count is 1,368; no axiom outside `{propext, Classical.choice, Quot.sound}` occurs. Audit stdout SHA-256: `6e3eee81ffb975b006b7c53441c2821fd3dbc0acd02f856427e3adb4312f705a`.

## Claim boundary

The audited type of `PaperExtendedExecution.preservation` explicitly requires `BodiesTyped d`, `StateTyped d g e s result`, and a successful `controlStep` equation. `finite_interaction` additionally requires an initial typed state, a trace, and `ProtocolTyped`; its conclusion preserves the final state/computation typing and erasure relation for that represented finite interaction. Both report only `{propext, Quot.sound}`. They do not establish that every source-generated declaration table satisfies `BodiesTyped`.

The Lean definition checks each registered body under a shifted declaration table, empty graph, and an explicit formal-value environment. The R23 result still leaves the exact stored-body/caller declaration and graph-context embedding from actual source-generated tables OPEN. R61 therefore claims only a conditional represented theorem unless fresh review finds a precise authoritative bridge. It does not close R23, full-language inference A/B, source/native realization, termination, graph guardedness, or production.

The audited `chooseLeft` and `chooseRight` constructors select the corresponding intersection typing premise while the operational `choose` uses its selected side. `absurd` has a typing constructor but `PaperCoreStep.step (.absurd value) = none` in the partial principal operator. Fresh review must confirm these statements against the frozen manuscript and surrounding source, including omitted cases and hypotheses.

No test suite, Cargo command, network operation, source edit, question edit, R59 candidate import, or production promotion occurred. External commit `31b1473a9d90355903e1462a4f2f75abae75e48e` and the failed R59 candidate remain separate. Questions remain withdrawn.

## Review request

Fresh non-author `compiler_referee` review is pending. Review the exact baseline, contract, process manifest/captures, audit source and all 1,368 marker/type/axiom records; independently check endpoint and constructor claims, paper polarity, the printed theorem hypotheses, and R23 source-context correspondence. Return blocking/major/minor findings and an explicit disposition. No checker calls are authorized for the reviewer.
