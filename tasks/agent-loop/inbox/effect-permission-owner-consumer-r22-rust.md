# R22 Rust handoff — CLOSED_INCOMPLETE / PREFLIGHT_REJECTED

Disposition from Luna: `CLOSED_INCOMPLETE — PREFLIGHT_REJECTED`. Cargo was NOT RUN. This handoff records provisional source instrumentation only; it is not runtime evidence and does not close any parent proof or production gate.

## Frozen source identity

Primary-verified hashes for the rejected isolated source set:

| Leased source | SHA-256 |
| --- | --- |
| `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/machine.rs` | `2e118422c44e8849529e6bfe9bb4dd31fdd565aa6a121c6d4d18295dc5f36d1a` |
| `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/receiving.rs` | `8b507eef8dde72a0cd277e4bdbf8df8005b989745054c45b73ef78adbc1a076a` |
| `isolated/ep-owner-consumer-r22/project/tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |

An earlier Rust freeze message reported machine hash `3c1cd801e2f8eaf5e20fad6b29506c3558bcd77a0f048f6f95a248f726994593`. That value was stale, not a typo: I made a final source-only edit after measuring it and incorrectly reported the old value as frozen. The primary then independently measured the hash above. No source edits followed the primary's measurement.

## Review history and blockers

1. The first pre-execution review rejected the initial baseline-hash set because `machine.rs` had changed from the admitted baseline after a freeze message stated there were no pending edits. That set was invalidated. No Cargo was run.
2. A later fresh preflight rejected the revised frozen set. The referee review identified these exact blockers:
   - The callback-use observation at `machine.rs:2552` is out of scope and occurs after the request. The test build cannot compile with it there; move it to the successful `callback_use` constructor near `machine.rs:1656`.
   - `same_source(lambda, apply)` incorrectly equates distinct source occurrences. Join the actual enclosing lambda/formal ownership instead.
   - The validator order `Request → Catch → integer → ResultConsumer` is reversed. `OperationResultConsumer` at `machine.rs:1400–1417` runs `callback_execution` before `execute_with_substitution` emits the Request around line 3000. Validate the real order and shallow-handler lifetime/discard.
   - Request/selection payload IDs, selected arm identity, and entry formal receipt are ignored; the Name-receipt/schema mismatch rejection case is absent.

   The rejected set hashes were machine `2e118422c44e8849529e6bfe9bb4dd31fdd565aa6a121c6d4d18295dc5f36d1a`, receiving `8b507eef8dde72a0cd277e4bdbf8df8005b989745054c45b73ef78adbc1a076a`, and program `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`. The reviewer consumed approximately 90 seconds, with approximately 110 seconds remaining in the shared review budget. No ACCEPT was recorded, and Cargo was not run. In the review before this final preflight, Luna also identified and requested correction of two production-path deltas: cloning `call`/`provider` outside test-only code and computing a test-captured Grant in production. Those paths were split with `cfg(test)`/`cfg(not(test))` before the later freeze. No assertion is made that the rejected set passed review.

The test-only provisional validator encodes the runtime-observed callback ordering as invocation → entry → use → request → Catch commit → selected integer `1` → operation result-consumer event → successful callback execution return. The companion validator encodes signal request → write request → write-handler Catch commit. These are source assertions only, not observed event traces. The rejection cases encoded in the provisional test include sibling invocation, missing permission, missing contribution, failed export/direct selection, failed handler selection, wrong handler owner, wrong view, premature result receipt, lost write residual, and wrong outer receiver owner. None has been executed or validated by a compiler or test run.

## Outcome and limits

- Only the three leased isolated runtime source files were edited. `program.rs` remained unchanged at the measured hash. Observation instrumentation is intended to be under `cfg(test)`; there is no production authorization or behavior claim from this handoff.
- The approved callback and companion source occurrence mapping remains as specified by the sprint contract. No source occurrence was executed, so there are no actual runtime IDs, authenticated owner joins, trace ordering observations, runtime outcomes, or first failed runtime transition to report.
- No Cargo command, compiler invocation, test, or runtime trace was produced. The receipt JSON was not created or written. No Lean result or theorem application to an authenticated Rust trace exists.
- The exact preflight ACCEPT required for the measured hashes was not recorded; the later referee preflight rejected them. Thus no invocation argv, exit status, elapsed time, CPU/RSS sample, or raw stdout/stderr exists.
- Active Rust time is UNKNOWN; it was not measured. Process/descendant cessation is confirmed by the primary's close disposition. No Git operation occurred.
- Source writes stopped before this handoff. After this handoff is written and hashed, no further writes or Cargo invocation are authorized in this lane.

Parent theorem, source/native correspondence, effect hygiene, soundness, principality, termination, and production gates remain OPEN. This provisional instrumentation is not a proof, source-owner authentication, accepted observation, or cutover.
