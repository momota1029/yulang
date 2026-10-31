# Handoff: EFFECT-PERMISSION-CONSTRUCTOR-REALIZATION-20261028/r1 — Rust

Handoff ID/revision: `EFFECT-PERMISSION-CONSTRUCTOR-REALIZATION-20261028-RUST/r1`
Contract SHA-256: `ffa32721d0c293d50f4a1a972e3da6955b4f0344c2ed6de037843ea8d73a2e35`
Contract integrated baseline: `6f9d7314f`; observed worktree HEAD: `c70183498ea99c42b3ef7e0202d7c57b5ff6b13e`. The sole commit over the pinned baseline changes only `tasks/agent-loop/current.json`; all compiler and frozen dependency hashes below match the contract.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, with original quantifiers/source domain. Effect hygiene meaning remains governed by `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–5. A/B, whole-language soundness, principality, progress, termination, source/native and production gates remain OPEN.

Author: `/root/effect_permission_constructor_realization_rust` (registered implementer assignment; requested model `gpt-6-luna`, requested effort `high`; observed model/effort `UNKNOWN`, no runtime model telemetry available). Sole repository writes were the two leased Rust source files and this leased handoff. No Git operation was performed.

## Outcome class and behavior

Outcome class: **provisional test-only source evidence instrumentation; focused execution NOT_VALIDATED**.

Added per-capture test-only IDs, carried on the private captured graph, and trace events connecting the capture ID to the negative formal root, capture return, exact definition owner and retained formal-domain term. The existing ordinary `CandidateInference::solve`/`export` permission test now checks that the same owner/domain is carried by one identified graph and that each exported permission port belongs to the graph exported for that source owner. A second ordinary source-solve case records symbolic formal-effect memo miss/hit and the signature-constructor delegation route, then checks owner/domain/capture/export-root linkage.

All added recorder state and graph identity fields are `#[cfg(test)]`; no preflight route, solver choice, recovery, public API, runtime behavior, expected output, source domain or language semantics changed. The recorder remains lazy and dormant unless the focused test enables it. This is finite source evidence only; it does not prove universal correspondence. Cleanup owner: Luna, after the evidence is reviewed. Falsifier: a source-approved constructor whose owner/domain is absent from its captured graph, or a successful export that returns a permission at a different image/owner while occurrence and path are preserved.

The intended source path is ordinary source lowering/preflight → `CandidateInference::solve` and constructor constraints → captured owner graph → definition export and `formal_effect_permissions`. The two intended focused tests did not execute, so this assignment establishes no new completed source-to-export evidence. No source refusal was observed; compilation stopped before any source case ran.

## Frozen artifacts and prior evidence

- `crates/yu-solver/src/candidate_effect.rs` SHA-256: `f7dd1d1bf1e66e98d969aa9f7cadc1faad4c1325acf65e8d9da56e2593a84bec`
- `crates/yu-solver/src/candidate_scheme.rs` SHA-256: `0c3d87610452f78f27189d0f6554d52d9422e2fcc2a4d38d93014538002553a4`
- Frozen dependency `crates/yu-solver/src/shadow_apply.rs`: `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- Frozen dependency `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- Observed `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- The failed `FormalPermissionSourceOrigin.lean` and previous Rust/Lean evidence were preserved/reused as context; no Lean file was read or changed under this lease. Reused Rust evidence: the preceding source-origin outcome reports a corrected parameter-row fixture and ordinary solve/export trace. Rejected as closure evidence: the earlier `FormalPermissionLiveCapture` direct internal producer fixture bypasses preflight, and the source-origin trace did not carry an explicit identity through exact owner, graph and export. Prior reports are not revalidated by this invocation.

## Check and resource receipt

One Cargo invocation was authorized and consumed; **no retry** was made. Exact argv is in the scratch `argv.txt`. It omitted the crate-required `--features shadow-apply-candidate`, so the library compiled without the cfg-gated `candidate_scheme`/`candidate_source` modules. Cargo exited 101 before the two filtered tests compiled or ran. This is an invocation feature-selection failure, not a source refusal or semantic counterexample.

- Raw stdout: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/stdout.raw`
- Raw stderr: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/stderr.raw`
- GNU time receipt: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/time.txt`
- Frozen argv: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/argv.txt`
- Frozen sources/dependencies and launch receipt: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/frozen-inputs.txt`
- Exit: 101; elapsed: 23.78 s; user: 20.31 s; system: 2.29 s; CPU: 95% (one pinned CPU); peak RSS: 522,452 KiB; swap: 0; launch available memory: 23,900,647,424 bytes.
- `git diff --check` passed on the two leased Rust sources before freezing. No Cargo test passed in this assignment.
- Rust assignment wall grant: 600 s; 23.78 s observed. The single invocation allowance is exhausted, regardless of nominal wall remainder.

Generated/scratch path: `/tmp/yulang-effect-permission-constructor-realization-20261028-r1/rust-target/` (Cargo target tree plus the five frozen receipt/log files above). Cargo target contents are disposable after Luna retains the receipt. No other new repository path was created.

## Missing evidence and next in-envelope boundary

TODO to Luna: decide whether to issue a new exact run authority/packet with the required `shadow-apply-candidate` feature, since this r1's one Cargo invocation/no-retry limit is exhausted. Do not interpret the build failure as a source refusal or as validation of the tests. If a new run is authorized, first verify these frozen source/dependency hashes and preserve the present failed receipt unchanged; use the exact corrected command and its own fresh resource receipt.

Proof/source mutual TODO: the proof lane can use the intended Rust trace schema only after a successful source-owner capture/export observation exists. Its remaining row/bound/evidence/context recurrence, canonical transport and native bridge remain the proof lane’s exact open premises; this Rust handoff closes none of them.

Worker state: writes stopped after this handoff; no descendant workers or processes remain. No review or primary adjudication has occurred. Source/native evidence remains provisional; production and all parent gates remain OPEN.
