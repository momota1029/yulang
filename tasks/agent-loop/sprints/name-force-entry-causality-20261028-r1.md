# Sprint NAME-FORCE-ENTRY-CAUSALITY-20261028/r1

Status: READY for live source assignment; research only. This is a new sprint with a fresh **600s ceiling**. It does not reset, erase, or reinterpret prior source/reviewer time, UNKNOWN observations, or the r3 STOPPED_RESOURCE outcome.

Branch / baseline: `yulang3` / `84a93a1b1722c62d34d032ccc157881b18b1a24a`.
Authority: unchanged original obligations in `notes/theory/2026-10-08-call-semantic-input-realization.md` §§4.1–4.3 and source/proof boundaries in the Name Force notes. No semantic decision or production authority.

## Exact goal

Repair the known research-instrumentation stale-provenance defect. Current `pending_name_entry` can survive an intervening Sequence, Condition, or BlockExpression and falsely join a Parameter `x` receipt to a later Local `z` ValueEntry when invocation owner, value, view, and cell count happen to match.

Use a one-use token tied to the immediate return consumer:

1. `consume` takes and discards any prior candidate before processing the current Name. Retain a candidate only for the matching lexical Parameter/Observe and the actual appended receipt index.
2. `return_value` takes the candidate unconditionally before dispatching the popped frame. Only that immediate matching ordinary `Frame::ValueEntry` can emit a trace.
3. Every other frame, mismatch, failed consume, or abandoned return drops eligibility. Never restore or carry the token across a frame.

This is observational instrumentation only. Preserve runtime decisions and the prior direct Name/Name positive result. The bounded driver must attempt the Sequence and Condition stale-join candidates, requiring no false trace when an intervening return consumer occurred. Any unsupported parse/shape stays explicitly unresolved. No generic source-form exclusion, test/expectation edit, fixture file, dependency, or output path is authorized.

The result is only a bounded runtime provenance repair. The conditional Lean packet remains frozen; Lean=0. The source handoff and original r2 trace remain append-only; increment the handoff revision. All original parent/A-B, complete Call, source/native, effect-hygiene, principality, termination, and production gates remain OPEN.

## Leases and frozen admission inputs

Source owns only these existing paths: `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/runtime/receiving.rs`, `tools/inference-playground/src/runtime/mod.rs`, `tools/inference-playground/src/bin/name_entry_trace.rs`, `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean`, and `tasks/agent-loop/inbox/name-entry-correspondence-20261028-source.md`. The preceding source handoff is frozen at SHA-256 `26268c0f4411a423491a08071131bfb923e9fb57b75ec0c96bec07526d3d9267`; source cessation was explicitly acknowledged before admission. The r2 MAJOR reviewer finding and r3 outcome are immutable.

The admitted r2 source bytes at baseline are:

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `c0c448acdce452eb896addec1056870e5653126bfde7e6cf66d2a715335dc009` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `tools/inference-playground/src/bin/name_entry_trace.rs` | `d4e2f98e3f02c4a806277cb69a624cab8dc86269df5abaf86ca1094098f3c061` |
| `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |
| `tasks/agent-loop/inbox/name-entry-correspondence-20261028-source.md` | `26268c0f4411a423491a08071131bfb923e9fb57b75ec0c96bec07526d3d9267` |

Before writing, source verifies these exact bytes and confirms no other writer. Use the existing source scratch `/tmp/yulang-name-entry-correspondence-20261028/source/`. Preserve old trace and receipts. `tools/inference-playground/Cargo.lock` is absent in this checkout; do not claim or require its prior hash. No new dependency or scratch/output path.

## Independent review

Fresh non-author `compiler_referee`, read-only, identity distinct from `/root/name_entry_correspondence_review`. Start and stop timestamps must be recorded from clock evidence. Review the frozen diff, every token create/take/drop/escape path, and the actual single Cargo receipt. Confirm the direct positive trace remains; the stale Sequence/Condition candidates do not join; runtime behavior is not changed; and no source form is broadly excluded. A major or unresolved false join rejects the reusable source claim. Review ≤180s, one verifier, tests=0. Do not reuse or reset the old reviewer’s UNKNOWN allowance.

## Fresh resources and stop conditions

Total **600s**: source ≤240s; fresh reviewer ≤180s; Luna ≤120s; dispatcher ≤60s. Source slice: ≤90s repair/hash freeze, exactly one `cargo run --locked --bin name_entry_trace` ≤120s, ≤30s final handoff and write cessation. One Cargo command total, ≤1 CPU and ≤1 GiB RSS target; no fallback, tests, Lean/Lake, new fixture/dependency/output, or additional source changes. Record actual start/stop timestamps and receipts; unknown remains UNKNOWN. No automatic renewal and no descendants.

The Cargo command is gated by Luna after frozen hashes and a capacity ACK; no command runs before that written gate. Stop if the implementation, command, or review cannot fit its exact cap. Freeze an INCOMPLETE handoff on failure or unsupported probes. Luna alone updates compact state, stages explicit files, and integrates. Checkpoint only the bounded reviewed or explicitly unreviewed research result; do not promote any parent gate.
