# Name-entry Sequence source receipt — INCOMPLETE lease deviation

Sprint: `NAME-ENTRY-SEQUENCE-20261028/r1`; contract SHA-256 `09ec84441d05ecaa8ac8a281528453f016cc89a965b26ec3e3baac57b3e10004`; baseline `8467531b5`. Source ACK/start `2026-10-27 16:16:25 UTC`. All five admitted hashes matched before edits/Cargo.

## Source path and execution

Inspected and grounded the path in existing source:

- `crates/yu-hir/tests/conditional_local_source.rs:53–77` retains a braced conditional's arm body as ordered `LocalSourceForm::Sequence` occurrences.
- `tools/inference-playground/src/runtime/program.rs:888–890` lowers `LocalSourceForm::Sequence` to `Instruction::Sequence`.
- `tools/inference-playground/src/runtime/machine.rs:1070–1075` pushes `Frame::Sequence` before evaluating the first item; `1864–1873` evaluates remaining sequence items and returns the final result.

The exact contract candidate was installed in the leased driver, preserving the direct Name/Name positive. The single authorized command ran once: `CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-name-entry-correspondence-20261028/source/target RUSTC_WRAPPER= cargo run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`. Cargo arguments: `run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`. Clock start `2026-10-27 16:16:51 UTC`; exit 0; tool wall time 1.434691 seconds; completion approximately `16:16:53 UTC`. Cargo reported a successful dev build in 1.44 seconds and launched the binary. One Cargo job. Actual CPU/RSS are UNKNOWN; 1 GiB was a target only. Tests=0, Lean/Lake=0; no retry or fallback. `git diff --check -- tools/inference-playground/src/bin/name_entry_trace.rs` exited 0.

## Captured stdout and result

The exact command stdout is preserved as a copied byte-for-byte trace at `/tmp/yulang-name-entry-correspondence-20261028/source/name-entry-sequence-20261028.txt`, SHA-256 `41fb580c9bbe68270d6f43c524741bdc480d3a314a893663f1e713d8db53e57c`. The driver mistakenly wrote the original command output to the prior frozen `name-entry-trace.txt`; I copied those stdout bytes to the newly leased output path after the run. This is explicitly a copied command stdout artifact, not a claim that the command wrote its output to the contract path. Compiler stderr contained existing yu-hir dead-code and yu-solver dead-code/private-interface warnings; no separate stderr log was created.

The direct positive completed and had one target attempt (entry parameter ordinal 1): invocation 1, value 2/view 2, cells-before-bind 2, bound cell 2, cells-after-bind 3; receipt 0 from Parameter ordinal 0 / Name site 8 was accepted.

The selected reviewed braced-conditional arm completed with these observations:

- Parameter `x`, Name site 15, receipt 1, source cell 1, value 2/view 2, cell count 3, returned through actual `Frame::Sequence` with the token present.
- Subsequent Local `z`, Name site 16, receipt 2, source cell 2, value 2/view 2, cell count 3, returned through actual `Frame::Sequence` with no token.
- Exactly one target ValueEntry attempt ran in invocation 1 (entry parameter ordinal 1): value 2/view 2, cells-before-bind 3, fresh bound cell 3, cells-after-bind 4; no token/receipt was accepted. No intervening binding changed the cell count between the two Name observations and target attempt.
- The selected result was `Completed(ValueHandle(2))`; the else arm was not executed. The output independently labels historical trace presence and queries the actual target attempt, so prior sticky trace state cannot satisfy the target query.

## Lease deviation and frozen artifacts

The driver output constant was not changed from the previous packet's `name-entry-trace.txt`. The Cargo run therefore overwrote a frozen prior trace. The contract-admitted expected prior SHA-256 was `ff8a8d88e29533f2d207206f492f7ed811ce9d705692ede5e99f5d388080b51c`; the overwritten file is now `41fb580c9bbe68270d6f43c524741bdc480d3a314a893663f1e713d8db53e57c`. No recovery or further write to that frozen path was attempted. The authorized new output is a post-run copy of the command stdout as described above.

Final hashes: leased driver `tools/inference-playground/src/bin/name_entry_trace.rs` `63e82792b8a4923f0ef7609abb5932a13acaf3c6e19105e0539170ce0ff3a85c`; unchanged `machine.rs` `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d`; unchanged `receiving.rs` `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd`; unchanged `runtime/mod.rs` `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f`; unchanged Lean data `OriginalNameEntryTrace.lean` `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115`; built executable `source/target/debug/name_entry_trace` `36a3c2561a51b1277fb5d2867e1efabb575552bab193f088f88e2c948acc1c82`.

The runtime observations satisfy the requested Sequence-value/view/cell-count and target no-token conditions, but the frozen prior output path was written outside this packet's exact output lease. Therefore the run is **INCOMPLETE for contract-compliant evidence capture** and cannot be treated as an accepted source claim without Luna's disposition and independent review. No semantic, theorem, native-seed/readback, ReturnAlignment, or production gate advances.

Source cessation ACK: no further source, trace, Lean or scratch writes will be made. All leased paths remain held pending Luna's disposition.
