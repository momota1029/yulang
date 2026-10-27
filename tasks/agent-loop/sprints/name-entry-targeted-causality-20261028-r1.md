# Sprint NAME-ENTRY-TARGETED-CAUSALITY-20261028/r1

Status: READY. Fresh ceiling **720 seconds**. Baseline: branch `yulang3`, commit `36a4867038a7d44e866e841c6194cf6223b98960`. This is a bounded runtime instrumentation sprint for the Name/Force correspondence seam. Prior STOPPED_RESOURCE, UNKNOWN-time, overrun, MAJOR and INCOMPLETE records remain unchanged.

## Fixed outcome

Obtain executed, target-specific evidence that (a) the direct Name/Name fixture joins its current receipt to its fresh ValueEntry and (b) reviewed Parameter→Local cases do not let an earlier Parameter receipt attribute the target Local `z` ValueEntry. The target observation must identify the actual invocation, entry parameter, transition, and accepted token/receipt or explicit absence. Keep any earlier successful trace as a separate observation; sticky historical trace presence cannot satisfy the target query. Show that each intended target path executed.

The previously reviewed source-level counterexample shape is `my main = (\\x -> { my z = x; (\\y -> y) (if x: z else: z) }) true`; use only syntax accepted by this source. Preserve Local `z`, equal value/view and unchanged cell count at the causal comparison. A Sequence variant must retain those same conditions. If supported syntax cannot realize the reviewed shape, or if the target path is unidentified/unexecuted, record the case UNRESOLVED. No weakening the counterexample to a non-equivalent example.

This is observational research instrumentation only. No language semantics, expected output, test contract, Lean theorem or production behavior may be changed. All original parent/A-B, full Call, native semantic seed/readback and ReturnAlignment, effect hygiene, principality, termination and production gates remain OPEN. Keep the conditional Lean packet frozen; Lean=0.

## Baseline and exact leases

At admission, the previous source worker and reviewer are terminal; all other previously recorded UNKNOWN identities remain UNKNOWN and their existing quarantined paths remain quarantined. No prior unknown path is released. Source writes are re-leased only for this sprint:

- `tools/inference-playground/src/runtime/machine.rs` — source worker, writable.
- `tools/inference-playground/src/bin/name_entry_trace.rs` — source worker, writable.
- `tasks/agent-loop/inbox/name-entry-targeted-causality-20261028-source.md` — source worker, new handoff.
- Existing trace output(s) under `/tmp/yulang-name-entry-correspondence-20261028/source/` — source worker, writable only as needed by the single run.
- Existing source scratch `/tmp/yulang-name-entry-correspondence-20261028/source/` — source worker, bounded to this packet.

All other paths are read-only or frozen. In particular, `receiving.rs`, `runtime/mod.rs`, both Lean files and the existing proof/source handoffs remain frozen. No new fixture, test, dependency, output path, descendant or nested sprint.

Admitted source hashes at baseline:

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/runtime/machine.rs` | `ba3d054be3988df00dd7025948ff50eccc0ce80f268b8dfb5f6268d490698fd8` |
| `tools/inference-playground/src/bin/name_entry_trace.rs` | `0a27356a8cfb5cb2096203017c38aaf9c0052bff746986a4f067bec7bcc43876` |
| `tools/inference-playground/src/runtime/receiving.rs` | `e6b22598a0d11a21fba260cdbc5b4ace3690cf9b21e51beb61d8cc967511fffd` |
| `tools/inference-playground/src/runtime/mod.rs` | `b7184e3869b4790cb0e2e72704e4a1b2f12df7772b441144b8ef63ab33e2fe4f` |
| `notes/theory/lean/YulangClosure/OriginalNameEntryTrace.lean` | `a6d1ec061b5d3bcd9bf85a56405e16ff0d8f02037a870f2c6ab139d82efb9115` |

Any baseline mismatch stops the source lane before edits or Cargo. Freeze exact final hashes and source cessation before independent review.

## Source lane and bounded run

One source envelope, ≤400 seconds from recorded ACK through edits, the single Cargo invocation, output capture and cessation ACK; no separate internal edit cap. Implement a discriminator tied to the actual target ValueEntry attempt and a bounded driver query that cannot be satisfied by an earlier trace. Preserve the positive fixture `my main = (\\x -> (\\y -> y) x) 41`, and execute equivalent reviewed stale-Local cases with supported syntax if available.

Exactly one command, ≤120 seconds, one CPU and 1 GiB RSS target:

`CARGO_BUILD_JOBS=1 CARGO_TARGET_DIR=/tmp/yulang-name-entry-correspondence-20261028/source/target RUSTC_WRAPPER= cargo run --locked --manifest-path tools/inference-playground/Cargo.toml --bin name_entry_trace`

No retries/fallbacks, tests, Lean/Lake, or other Cargo invocation. Record actual UTC start/stop, exact command and exit, stdout/stderr, target-specific records, and observed resource evidence; unknown measurements remain UNKNOWN. A failure or nondiscriminating observation freezes INCOMPLETE with no renewal.

## Independent review

Fresh non-author `compiler_referee` reviewer, distinct from both prior Name-entry reviewers; read-only, independently timed ≤180 seconds, after source freeze and cessation ACK. Review the discriminator and final records; verify direct positive evidence, actual target-path execution, counterexample equivalence (Local `z`, same value/view and cell-count condition), supported syntax, and that no previous trace can satisfy a negative target query. Audit edits and behavior scope against frozen baseline. Unsupported syntax, non-equivalence, false attribution, missing target evidence or behavior change means INCOMPLETE. Reviewer runs Cargo/tests/Lean=0.

## Budget, stop and disposition

Fresh total **720s**: source400, fresh reviewer180, Luna100, dispatcher40. No budget transfers; prior UNKNOWN receipts and historical usage are not overwritten. Tests=0, Lean=0, Astra=0. Source stops before the 400-second ceiling and acknowledges cessation; reviewer starts only after freeze. On any missing or inconclusive evidence, stop, preserve exact receipts, freeze leases and report INCOMPLETE without extending the sprint. Acceptance closes only this bounded causal instrumentation seam and does not instantiate a semantic seed, ReturnAlignment, original theorem or parent gate.
