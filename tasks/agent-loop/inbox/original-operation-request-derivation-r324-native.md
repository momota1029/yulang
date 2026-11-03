# R324 native structured Request/resume witness

Sprint: `tasks/agent-loop/sprints/source-request-resume-r324.md`, SHA-256
`c3af8363ab642c9cbe879a8df018f8edad59a82cdf458e49af1f3db7f05c4636`.
Assignment: `original-operation-request-derivation-r324-native`; handoff
revision 1. Baseline `773e96901`. Parent: unchanged R159 Call/effects objective
and R311/R293 source obligations. Worker `/root/r324_native`; descendants none;
runtime session/launch receipt unavailable. Requested model/effort: Luna/high.
Observed model/effort: UNKNOWN.

## Outcome and source/native correspondence

Outcome: **provisional source/native evidence**. The test-only R323 witness now
exports a structured `R314Artifact.OperationIdentity` with its declaration
positions, source family, visibility, and recursively typed signature. Request
and resume owners use `R314Artifact.ExecutionOwner`; payload/response retain
typed `Received` plus dereferenced runtime values and source sites. Ordered
saved/template frame rows use typed R323 variants for Callee code operands,
BlockExpression code label/site/next/environment, RootCompReturn view/receipt/
occurrence, and Owner. Owner replay rows retain typed owners, control edges,
and source-qualified call/provider sites. These constructors are the exact
supported suffix subset exercised by the source witness; any other saved frame
or template node fails closed.

The observed accepted source is the R315 fixture:
`make seed = { io::tick seed; \\argument -> argument }`, called through
`relay`, caught by the source handler, resumed with value `10`, and completed
with result `7`. The exporter joins the actual `tick` Request event, its
captured ordered continuation, and the response delivered to that template in
the same R324 Machine. It checks HIR source ownership through the R314 source
export and code/source sites, and compares live template operands against the
captured structured frame witnesses. The receipt ordinal is available through
the newly authorized `#[cfg(test)]` accessor in `receiving.rs`.

This is native execution evidence only. It does not establish the original
declaration-owned `Request`/resume primitive, typed response/current-world
domain, original guards or observation projections, lawful joint restriction,
source-semantic continuation meaning, Union membership, EI, Checking, or the
R159 parent. R323 and R315 run tokens differ; no same-run equality between
those artifacts is claimed. The fixture’s handler response and runtime value
do not supply an independently fixed original semantic premise.

## Reused/rejected evidence and exact residual

Reused R323’s actual same-Machine request/template/response tracing, live
template graph validation, ordered suffix, R314 source-site exporter, R315
source/code artifact shape, and R314 typed operation identity/signature
encoder. Replaced Debug-rendered operation identity/signature, Debug-rendered
owners, Debug frame labels, and the BlockExpression pointer fingerprint.
Machine pointer identity remains an internal same-Machine provenance guard and
is not exported as semantic identity. Unsupported frame/node variants remain
negative controls. Existing R323 native handoff revision 3 was read as prior
evidence, not copied as proof of semantic admission.

TODO `R324-NATIVE-TO-PROOF-1` for the R324 proof owner: consume this artifact
with R315 and the original R311/R293 constructors; derive and apply the first
original typed response/current-world and lawful whole-tuple action premises
for the actual source occurrence, or stop at the first missing source-law
constructor with its owner. Preserve all alternatives and the original joint
restriction. Do not join the distinct R315/R324 runs by their local event,
template, or machine indexes. Falsifier: a supported original response/world
or suffix whose original guard, owner, view/receipt, or continuation field
cannot be reconstructed from the independent original laws and the exact
source-owned constructors. This handoff requests evidence; it grants no proof,
semantic, or production authority.

## Changed and frozen artifacts

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `7dec51aa5d57b3ef7b5217a4c772355aa75ddf3a88adffae017cdd637ee485ef` |
| `tools/inference-playground/src/runtime/receiving.rs` | `476ef914bb11449f106c900a233e9677025830e6923cd5db6a1dc6edbcc6d613` |
| `/tmp/yulang-r324-native/r324-operation-source.lean` | `85e663b65a893b0acd5de46b7b1b59e940098bf5e5a7815cada4736a3e983551` |
| Read-only `runtime/program.rs` | `2c03ff8681c50520e0527f139a86ac8427097c27aeafcf247e76673310be4b0c` |
| Read-only `runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| Read-only R323 native handoff | `4fe31abd6e25e6e8f3cfd6c44b5b809367dd19b4f618af586143eb7541ceeb98` |

Both Rust edits are test-only; no production API/behavior changed. No expected
output, diagnostics, source domain, or natural inference behavior changed. The
`receiving.rs` accessor was added only after Luna granted that exact path for
this `#[cfg(test)]` receipt ordinal. No program/dispatch/dependency/lockfile,
Git, central state, or unleased path was changed.

## Checks and resources

- `CARGO_TARGET_DIR=/tmp/yulang-r324-native/target YULANG_R323_LEAN_WITNESS=/tmp/yulang-r324-native/r324-operation-source.lean cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — **1 passed**, 94 filtered. The test includes source-site, signature, response value/handle, owner-resolution, template root/order/count/link, Callee operand/environment, and View receipt mutation rejection.
- Pinned Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -M2048 /tmp/yulang-r324-native/r324-operation-source.lean` — **passed**, exit 0 on the final generated artifact.
- `git diff --check -- tools/inference-playground/src/runtime/machine.rs tools/inference-playground/src/runtime/receiving.rs` — passed.
- One early Rust parse failure and two initial Lean schema/constructor failures were repaired; final focused Rust and Lean checks passed. No production-mode Cargo check was run. No benchmark or full suite was run.
- Cargo emitted existing warnings in `crates/yu-hir/src/lib.rs`, `crates/yu-hir/src/shadow.rs`, `crates/yu-solver/src/candidate_receiver.rs`, `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/candidate_value_graph.rs`, and `tools/inference-playground/src/runtime/program.rs`. These owners are outside this lease; Luna should route any safe cleanup as separate owner-path work. The pre-existing unused `frame` binding in the leased R315 exporter was removed as a small safe warning fix.
- Resource budget: sprint allowance 1800 seconds; actual per-command wall/CPU/RSS were not instrumented. Cargo used only the granted heavy slot and isolated target directory; Lean ran after Cargo completed. No background process remains.

## Provisional boundary, scratch, and worker state

New repository paths: this handoff and the two leased Rust files above. All
scratch is under `/tmp/yulang-r324-native/`: generated Lean artifact and
`target/` Cargo build tree. These are disposable after Luna accepts the frozen
artifact and finishes proof/native review. No other scratch path was created.

The artifact remains provisional until fresh independent native/source review
and proof-owner consumption. Tests and Lean elaboration establish artifact
consistency only, not the theorem. Writer work is complete for this result;
no descendants remain. Luna owns review, cleanup, state synchronization and
integration. No Git operation was performed.
