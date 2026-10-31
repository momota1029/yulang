# R107 Rust baseline reconstruction and Lean output-protocol audit

Status: **ADMITTED** under the standing user-authorized Yulang Rust/Lean goal.
Parent goal, original Simple-sub source domain, claims, quantifiers, semantic
authority, expected outputs and production gates remain fixed. Baseline commit:
`d177c46ec61fcadd70a3d587c2f8934f6bc91f46`.

## Selector outcome and Rust question

R106 closed with a reviewed evidence checkpoint and no source promotion. The
selector recommends a read-only baseline/provenance audit across the six dirty
`yu-solver` files below, because this directly addresses the user's request to
understand the remaining Rust implementation work. This assignment may identify
a coherent candidate subset, but it does not grant code-edit or source-staging
authority. In particular, preserve the uncertain `candidate_effect.rs` bytes.

Rust author's sole mutable path:
`tasks/agent-loop/inbox/effect-permission-baseline-reconstruction-r107.md`.

Read-only Rust source scope and frozen working-tree SHA-256 pins:

| Path | HEAD blob SHA-256 | Working-tree SHA-256 |
|---|---|---|
| `crates/yu-solver/src/candidate_effect.rs` | `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-solver/src/candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` | `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf` |
| `crates/yu-solver/src/candidate_scheme.rs` | `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070` | `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/lib.rs` | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `crates/yu-solver/src/shadow_apply.rs` | `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d` | `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f` |

Within 300 seconds, map each file's changed responsibility, provenance
evidence, prior review/check outcome and whether each delta is ordinary compiled
behavior, feature-gated compiled behavior, `cfg(test)` or observer-only.
Identify dependencies among changes and distinguish passed, failed, superseded
and unrun evidence. Recommend the smallest dependency-closed integration
component that can be recovered from exact reviewed bytes, or report the exact
obstruction per component. Do not claim that a subset is stageable: Luna decides
after fresh independent review. A component depending on uncertain
`candidate_effect.rs` bytes is blocked; unrelated components may proceed.

Rust author restrictions: no source edits, no Cargo/Rust/build/test command, no
scratch/cache/environment, no Git mutation, and no access to quarantined runtime
paths. Do not alter protected assertions, fixtures, diagnostics or expected
outputs. Do not reconstruct missing bytes by guesswork.

Fresh reviewer: `compiler_referee`, 180-second bound, on the frozen author
handoff and exact source pins. Review whether provenance and ordinary/test-only
classification support the proposed boundary, whether protected obligations
and prior failures are accurately represented, and whether a safe component
exists. Reviewer does not certify its own work; Luna adjudicates.

## Proof-support lane

One registered `lean_prover` may write only
`tasks/agent-loop/inbox/effect-permission-module-output-protocol-r107.md` and
may read the pinned R106 runner failure receipt, installed Lean 4.35.0 source,
and exact runner/tool sources. This is a protocol audit only: identify Lean's
temporary `.olean` naming/publication behavior and the runner's handling of
temporary files, process termination and cleanup. Recommend a concrete guard
and cleanup protocol for a separately admitted future execution. No Lean, Lake,
checker, build, test, version or compiler invocation; no cache/output creation;
no retry of R106. Pin every inspected source file. Fresh compiler-referee review
is bounded at 180 seconds.

Known installed sources already pinned: `Lean/Environment.lean`
`6c90105aecc4d28efe94cc9aef1704c284e7a748b28270b5f8513d2562331e43` and
`Lean/Util/Path.lean`
`52cf9aa41a82db18d0d3c93bf6257d064f773af9e62b8b43be89ce1b0e00055f`.
The proof lane must add exact pins for any further source it inspects.

## Shared budget and completion gate

At most 300 seconds per author, 180 seconds per independent reviewer and 240
seconds for Luna reconciliation; aggregate active work ≤1,200 seconds, Astra
0, at most four known assignments. No persistent scratch or build outputs. No
compiler or test execution in this sprint. Do not read, edit, stage or clear
quarantined runtime files or unrelated untracked material.

Close only after both handoffs are frozen and independently reviewed, findings
are adjudicated, exact changed-file provenance and verification status are
recorded, and a dependency-closed Rust integration boundary is identified or
explicitly obstructed. This sprint does not authorize Rust source edits,
source integration, semantic promotion, proof closure, or production. Push a
coherent reviewed evidence checkpoint promptly; source commits require a
separately authorized, fully reviewed and verified gate.
