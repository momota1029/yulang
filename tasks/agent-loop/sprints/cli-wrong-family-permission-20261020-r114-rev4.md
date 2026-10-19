# R114 continuation: split private Machine and public CLI witnesses

Status: **DRAFT_FOR_PRE_EXECUTION_REVIEW**. Luna is primary and sole Git
integrator. Rev1, rev2, and rev3 outcomes remain immutable history. The original
195-byte source, wrong-family permission question, predicted `HandlerEvidence`,
CLI failure/empty stdout, all falsifiers and exclusions remain unchanged.

## Fixed parent and reviewed evidence

Parent/source authority: rev1
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261019-r114-rev1.md`,
SHA-256 `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`;
exact source SHA-256
`91c015cf7dce0132b0d7faa5cd7d30f87eb1fe3c3cadc5bd18db1595061a771f`.
Current source proof: `notes/theory/2026-10-20-r114-source-identity-current.md`,
SHA-256 `2835bca1ea5612fb4a6806540a94f6a225feef1ddc38a58db896838974a36ecf`.
Three fresh rev3 reviews are CLEAN. The rev3 command failed at compilation
before the test body because `RuntimeProgram::start_source_schedule` is
`pub(crate)` but the integration test called it. This established no runtime
or CLI observation. Preserve that failure; rev4 is a new harness grant, not a
retry under rev3.

## Harness repair and observable contract

Use the same fixed source and source name `-` throughout. Split the witnesses
so the private Machine API is used only inside the crate:

1. Add a crate unit test in the existing `tools/inference-playground/src/lib.rs`
   test module with the same test function name
   `wrong_family_permission_withholds_runtime_and_cli_result`. It forms the
   same HIR with `FileKey("inference-playground", "-")`, solves ordinary
   `CandidateInference` and requires no candidate conflicts, constructs the
   `RuntimeProgram`, calls the existing crate-private
   `start_source_schedule`, and requires direct
   `Unavailable(HandlerEvidence(site))`. In this same unit test, call the
   public `execute(source, "-", "main", 10_000, false)` and require its error
   to equal `runtime unavailable: {direct_error:?}`. This dynamically checks
   the exact HIR-backed diagnostic without numeric spans.
2. Keep the integration test in
   `tools/inference-playground/tests/cli_permission_boundary.rs` with the same
   test function name, but remove the inaccessible direct Machine construction.
   It feeds the same source to the public stdin child
   `--run main --steps 10000 -`, requires unsuccessful exit and empty stdout,
   and requires stderr to contain `runtime unavailable: HandlerEvidence(`
   and end in newline. The in-crate unit test above checks the exact public
   `execute` diagnostic; current `main` passes that error to stderr and writes
   no result. Fresh review must assess whether these two frozen witnesses
   compose without weakening the original claim.

No public visibility change, compiler/runtime/WASM source change, source
change, expected outcome change, fixture change, or Web edit is authorized. If
the current `execute` signature differs, a required owner is missing, or the
two-test decomposition cannot preserve the original correspondence, stop and
report the obstruction before writing.

## Frozen direct inputs and exact leases

The complete current dependency table in rev3 remains binding and must match;
rev3 proof and all three CLEAN review receipts are also frozen. Additional
test harness inputs:

| Input | SHA-256 |
|---|---|
| `tools/inference-playground/src/lib.rs` | `bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b` |
| `tools/inference-playground/tests/cli_permission_boundary.rs` | `3efcf117612a513250a4396f5f21c15a0a3b2b89ac4ce27518979df8b3b93f13` |
| `tools/inference-playground/src/main.rs` | `75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100` |
| `tools/inference-playground/Cargo.toml` | `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56` |

- **Correspondence proof, Sol/high, max 120 seconds:** write only
  `tasks/agent-loop/inbox/20261020-r114-rev4-proof-bridge.md`. Explain how
  the direct Machine + `execute` unit witness and the CLI child integration
  witness compose for the unchanged source. If no additional source lemma is
  needed, return `WAITING` with the exact already reviewed proof locator and
  why the harness split adds no semantic premise. No code or test command.
- **Implementation, Luna/high, max 180 seconds:** after prospective CLEAN,
  edit only `tools/inference-playground/src/lib.rs`,
  `tools/inference-playground/tests/cli_permission_boundary.rs`, and
  `tasks/agent-loop/inbox/20261020-r114-rev4-implementation.md`. Implement the
  two tests exactly as specified. Freeze hashes and an implementation handoff.
  Do not execute tests, builds, formatter, compiler, CLI, or Git.
- **Prospective spec review, max 60 seconds:** review the test decomposition
  and exact assertions before edits. Output only
  `tasks/agent-loop/inbox/20261020-r114-rev4-prespec-review.md`.
- **Fresh final reviews, 120 seconds total:** independent compiler/source,
  spec/authority, and regression reviewers, max 40 seconds each, inspect the
  frozen tests, proof bridge/WAITING receipt, rev3 proof, current direct pins,
  and failure-preserving behavior. Exact outputs:
  `tasks/agent-loop/inbox/20261020-r114-rev4-compiler-review.md`,
  `tasks/agent-loop/inbox/20261020-r114-rev4-spec-review.md`,
  `tasks/agent-loop/inbox/20261020-r114-rev4-regression-review.md`.
- **Verification, Luna only:** after all fresh final reviews are CLEAN, run
  these exact commands sequentially and once each, stopping on any failure:

  ```sh
  CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --lib wrong_family_permission_withholds_runtime_and_cli_result -- --nocapture
  CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test cli_permission_boundary wrong_family_permission_withholds_runtime_and_cli_result -- --exact --nocapture
  ```

  The library test validates preparation, candidate acceptance, direct
  source-scheduled Machine outcome and exact public `execute` diagnostic. The
  integration test validates the public stdin CLI outcome. These are the only
  authorized commands; no retry or repair after either fails.
- **Closeout, Luna, max 60 seconds:**
  write only `notes/progress/2026-10-20-r114-rev4-closeout.md`. Preserve the
  rev1–rev3 closeout and all OPEN parent gates.

## Resources and stop conditions

Preserve **2,221 seconds charged** from rev1–rev3. Rev3's 119 unused seconds
are reallocated exactly once by this versioned grant. Rev4 envelope: 60
inventory + 60 prospective review + 180 implementation + 120 proof bridge +
120 final reviews + 240 sequential verification + 60 closeout = **840
seconds**. New cumulative ceiling: **3,061 seconds** (2,221 prior charged +
840 rev4). This is a 721-second increase over rev3's 2,340 cap after applying
its 119 unspent seconds. No other spending resets; unknown reservations remain
charged. Astra 0; one heavy process maximum and verification stays serial.

Any input mismatch, new owner, non-CLEAN final review, failed command, or
changed observation stops without retry, alternate command, semantic rewrite,
or production promotion. Rev3's compile failure remains in permanent history.
All Simple-sub/evaluator A/B, R85 adoption, effect-hygiene, source-law and
production gates remain OPEN. Luna alone owns state, review adjudication,
commands, closeout and Git integration.
