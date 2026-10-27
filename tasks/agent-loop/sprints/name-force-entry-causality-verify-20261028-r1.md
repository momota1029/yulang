# Sprint NAME-FORCE-ENTRY-CAUSALITY-VERIFY-20261028/r1

Status: READY; verification only. Fresh ceiling **480s**. This does not reset any prior usage or revise either STOPPED_RESOURCE outcome. No code edits are authorized.

Baseline: `yulang3` / `7ce561c02` (`7ce561c02` is the pushed candidate checkpoint). Scope: determine whether the frozen immediate-return token candidate compiles, preserves the direct Name/Name trace, and prevents stale provenance across the driver’s intervening Sequence/Condition cases. This is research instrumentation only. All original parent/A-B, complete Call, native seed/readback, effect hygiene, principality, termination and production gates remain OPEN.

## Frozen inputs and leases

Frozen source handoff r5 SHA-256 `751ae04350ba6124ef691756069b4dcd85f7cad85c2e851dec1ad553e8103a25`. The source acknowledged cessation. Candidate code hashes:

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `ba3d054be3988df00dd7025948ff50eccc0ce80f268b8dfb5f6268d490698fd8` |
| `tools/inference-playground/src/bin/name_entry_trace.rs` | `0a27356a8cfb5cb2096203017c38aaf9c0052bff746986a4f067bec7bcc43876` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |

Verification operator owns no source changes. It may run the existing binary once and write only the already leased trace output(s) and append the source handoff as revision 6. Existing source scratch: `/tmp/yulang-name-entry-correspondence-20261028/source/`. If any frozen hash differs, stop without running Cargo. No new source, test, fixture, dependency, or output path.

## One bounded command

Exactly one command, total cap 120s, one CPU/1 GiB RSS target:

`CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-name-entry-correspondence-20261028/source/target RUSTC_WRAPPER= cargo run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`

No retry, fallback, second invocation, tests, Lean/Lake, or code repair. Record actual start/stop UTC, exit status, stdout/stderr, command/session evidence and resource observations; UNKNOWN stays UNKNOWN. If it fails, times out, or lacks required evidence, freeze INCOMPLETE and stop.

**Evidence limitation:** the frozen Sequence candidate is `my main = (\\x -> (\\y -> y) {x; x}) 41` and the Condition candidate is `my main = (\\x -> (\\y -> y) (if x then x else x)) true`. These are not the reviewer's original stale-Local examples. In particular, the condition syntax may be unsupported and the Sequence case may not preserve the exact equal-value/view/cell-count structure. Report unsupported syntax or a non-equivalent shape as UNRESOLVED; a clean run is not by itself a negative proof of every stale join.

## Fresh independent reviewer

Fresh non-author `compiler_referee`, identity different from `/root/name_entry_correspondence_review` and the source author. Read-only, independently timed ≤180s. Inspect frozen code, every token create/take/drop/escape/failure path, and the single runtime receipt. Check that only the immediate matching ordinary ValueEntry frame can consume eligibility, intervening frames drop it, mismatch/error paths clear it, and direct positive evidence remains. A passing receipt for the current driver does not establish excluded Sequence/Condition/BlockExpression cases. Keep the source claim within executable evidence and explicitly unresolved cases; any false join, compile failure, or missing required evidence leaves outcome INCOMPLETE.

## Budget and stops

Total **480s**: verification operator ≤150s (preflight + one ≤120s Cargo + handoff/cessation), fresh independent reviewer ≤180s, Luna ≤110s, dispatcher ≤40s. Capture actual start/stop timestamps for operator and reviewer. Lean=0, tests=0, Astra=0, no descendants or renewal. Source operator assignment starts only after the exact contract and hashes are rechecked. Reviewer starts only after the operator freezes outputs and acknowledges cessation. Freeze all six leases after disposition. Acceptance, if earned, covers only bounded instrumentation correspondence; it never closes an original theorem or parent gate.
