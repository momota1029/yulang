# NAME-ENTRY-SEQUENCE-20261028/r1 — primary outcome

Disposition: **INCOMPLETE overall due to an unauthorized frozen-output overwrite. The targeted Sequence observation itself is technically supported.** The single execution produced the exact Parameter→Local Sequence evidence sought, but the driver wrote to the preceding sprint's frozen trace path. Copying the stdout to the newly leased path preserves the new finite observation; it does not authorize the overwrite or restore the prior trace bytes. The old trace content is recorded as lost from the available scratch state, and no recovery or further write was attempted.

## Frozen receipts

- Contract SHA-256 `09ec84441d05ecaa8ac8a281528453f016cc89a965b26ec3e3baac57b3e10004`; baseline `yulang3` / `8467531b5`.
- Source handoff SHA-256 `81155ee332d121577512b3d894c7eb582aa0dc217742eb5c9d103ae680cb4f2f`.
- Driver `name_entry_trace.rs` SHA-256 `63e82792b8a4923f0ef7609abb5932a13acaf3c6e19105e0539170ce0ff3a85c`; runtime `machine.rs` remained at admitted SHA `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d`.
- Copied command stdout at the newly leased output `source/name-entry-sequence-20261028.txt` SHA-256 `41fb580c9bbe68270d6f43c524741bdc480d3a314a893663f1e713d8db53e57c`.
- Previous frozen output `source/name-entry-trace.txt` was supposed to remain at SHA-256 `ff8a8d88e29533f2d207206f492f7ed811ce9d705692ede5e99f5d388080b51c`; it now has SHA-256 `41fb580c9bbe68270d6f43c524741bdc480d3a314a893663f1e713d8db53e57c`. The source worker stopped without attempting recovery.
- Other admitted runtime, receiving, module and Lean input hashes remained unchanged.

## Execution and review

Source ACK/start `2026-10-27 16:16:25 UTC`; cessation ACK `16:18:07 UTC` (102 seconds, within 300). All five admitted hashes matched before edits. Exactly one locked Cargo run started `16:16:51 UTC`, exited 0, tool wall 1.434691 seconds; one build job. CPU/RSS UNKNOWN; 1 GiB was a target. Tests=0; Lean/Lake=0; no retry/fallback. The run wrote its output to the old frozen path because `SCRATCH_OUTPUT` was not updated, then the source worker copied the captured stdout to the exact newly leased output path. This is recorded as a lease deviation, not contract-compliant output capture.

Fresh reviewer `/root/name_sequence_review` ACKed `16:18:42 UTC` and completed `16:19:45 UTC`; elapsed 63 seconds of 180. Technical verdict: Sequence observation PASS. Contract verdict: INCOMPLETE because the old frozen output was overwritten. Reviewer also disclosed one read-only `git diff` command despite the contract's Git=0 restriction. There were no Git mutations, edits, Cargo, tests, Lean or descendants. This minor reviewer-protocol deviation is retained; it does not erase the source lease violation.

## Accepted finite observation

The direct positive still has one target attempt in invocation 1 / entry parameter 1 and accepts receipt 0 from Parameter 0 / Name site 8.

In the selected braced conditional arm, Parameter `x` at site 15 / receipt 1 and subsequent Local `z` at site 16 / receipt 2 both return through actual `Frame::Sequence`. Both carry value/view 2/2 with cell count 3; no cell is added between them. The unique subsequent target ValueEntry attempt in invocation 1 / parameter 1 receives value/view 2/2 at cell count 3, binds fresh cell 3, and accepts no token or receipt. The else arm is not executed. This resolves the earlier distinction between a standalone BlockExpression and the actual Sequence path for this finite runtime case.

The result establishes no native semantic seed/readback, ReturnAlignment, original theorem, parent/A-B, full Call, effect hygiene, principality, termination or production gate. No runtime code changed in this packet; only the driver fixture changed. The previous sprint's MAJOR overclaim remains preserved and is adjudicated by its own outcome.
