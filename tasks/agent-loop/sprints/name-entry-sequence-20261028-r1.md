# Sprint NAME-ENTRY-SEQUENCE-20261028/r1

Status: READY; fresh source-only evidence packet. Ceiling **600 seconds**. Baseline: branch `yulang3`, commit `8467531b5` (reviewed targeted instrumentation checkpoint). This packet addresses only the actual `Frame::Sequence` evidence gap recorded in `NAME-ENTRY-TARGETED-CAUSALITY-20261028/r1`; it preserves that sprint's MAJOR overclaim and adjudicated BlockExpression-only result.

## Fixed outcome

Retain the direct positive Name/Name case and execute the actual Sequence-frame path with an equivalent stale-Local `z` comparison. The fixture candidate, grounded in the existing `conditional_local_source.rs` braced-arm shape, is:

```yu
my main = (\\x -> {
  my z = x;
  (\\y -> y) (if true {
    x
    z
  } else {
    z
  })
}) 41
```

The executed selected arm must show, in one invocation and before the unique target ValueEntry attempt:

1. Parameter `x` returns to an actual `Sequence` frame.
2. The subsequent Local `z` returns to an actual `Sequence` frame.
3. Both carry equal raw value and view, and the same cell count before and after both observations; no intervening binding may manufacture a new cell.
4. The actual target ValueEntry runs once and accepts no token from the earlier Parameter receipt.

The case label, successful compilation, target no-token record, or a different return frame is insufficient by itself. Unsupported syntax, unexecuted arm, mismatched value/view/count, ambiguous target, or `BlockExpression` instead of `Sequence` leaves the result INCOMPLETE. Preserve the direct positive fixture and report its target-specific accepted receipt separately.

This is finite observational instrumentation only. No semantics, expected outputs, tests, Lean, runtime instrumentation, dependency, proof file or production behavior may change. Native semantic seed/readback, ReturnAlignment, original theorem, parent/A-B, full Call, effect hygiene, principality, termination and production gates remain OPEN.

## Exact leases and frozen inputs

Source writes are limited to:

- `tools/inference-playground/src/bin/name_entry_trace.rs` — driver fixture/query only.
- `tasks/agent-loop/inbox/name-entry-sequence-20261028-source.md` — new source handoff.
- Exactly one new trace output: `/tmp/yulang-name-entry-correspondence-20261028/source/name-entry-sequence-20261028.txt`.

Existing scratch directory remains bounded to this packet. `machine.rs`, `receiving.rs`, `runtime/mod.rs`, all Lean files, prior source handoffs, the prior trace and all other paths are read-only/frozen. No tests or fixture files may be added or changed. The prior overclaim text remains preserved; this contract and its outcome narrow the accepted conclusion.

Admitted baseline SHA-256:

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/bin/name_entry_trace.rs` | `1bdc20af3157a8df34d93a2872607e282927eb9ab851c3d505b135d6f5c1598e` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fe3de685650761767be313285321e548964b41900c3aae7f5f434d48034395d` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |

Verify every hash before editing or Cargo; any mismatch stops the lane. Freeze final hashes and acknowledge source cessation before independent review.

## Source envelope and sole command

One source envelope ≤300 seconds from recorded ACK through the hash gate, driver edit, sole Cargo invocation, output capture and cessation ACK. The source lane must inspect and cite the existing braced-conditional lowering/runtime path before the run. No separate internal stage cap.

Exactly one command, ≤120 seconds, one CPU and 1 GiB RSS target:

`CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-name-entry-correspondence-20261028/source/target RUSTC_WRAPPER= cargo run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`

No retry, fallback, test, Lean/Lake or additional Cargo command. Record actual UTC command start/stop, exit, stdout/stderr, exact targeted records, and resource observations; UNKNOWN remains UNKNOWN. On failure or inconclusive evidence, stop and freeze INCOMPLETE with no renewal.

## Independent review and limits

Fresh non-author `compiler_referee`, distinct from both earlier Name-entry reviewers and the targeted-causality reviewer; read-only and independently timed ≤180 seconds, after source cessation. Inspect final driver/code and the unique trace. Confirm actual Parameter `x` then Local `z` returns through `Sequence`, equal value/view and unchanged cell count, unique target ValueEntry with no stale token, and preserved direct positive. Verify source-site distinction, branch execution and no claim based only on label or sticky prior trace. Reviewer Cargo/tests/Lean/Git=0.

Fresh budget **600 seconds**: source300, reviewer180, Luna90, dispatcher30. No transfer, retry, descendants or renewal. All previous receipts, UNKNOWN measurements and the earlier MAJOR remain unchanged. If actual Sequence evidence is not present, freeze INCOMPLETE; do not renew this probe packet again. Next work should pivot to the native receipt seed/readback seam. This bounded result cannot close a parent theorem or any production gate.
