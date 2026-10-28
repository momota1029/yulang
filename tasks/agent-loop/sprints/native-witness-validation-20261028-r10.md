# NATIVE-WITNESS-VALIDATION/r10

Status: CANDIDATE FOR LUNA ADMISSION; new packet after R9 `CLOSED_INCOMPLETE`, not an R9 retry. Branch `yulang3`; parent outcome `tasks/agent-loop/history/native-witness-frame-repair-20261028-r9-outcome.md` SHA-256 `260153b7ed59e1ea9d9f5922d7ac1a05390e9d1f6435bc176e573b0fdc77909d`. Input manifest `tasks/agent-loop/sprints/native-witness-validation-20261028-r10-inputs.json`, SHA-256 `36e54c93c486fb15ba1a01af15104216031335f5bd6c39d6b62c624e1513e9bd`; 89 pins, zero mismatches at preparation.

## Original goal and bounded outcome

Preserve the unchanged parent `YulangClosure.SourceProblem.InferenceSoundness` and its full source domain, quantifiers, one shared source witness, immutable-birth Value qualification, and effect-hygiene policy. This packet has exactly two success predicates: (1) the pinned focused Rust fixture executes to completion and passes on the frozen R9 Rust source; (2) all seven unchanged R9 conditional Lean theorem declarations elaborate, print complete types, and pass complete transitive axiom audits without `sorryAx` or a project axiom. `extract` remains an explicit conditional premise. Native/source correspondence, original parent, effect hygiene and production remain OPEN.

R9 remains CLOSED_INCOMPLETE. Its Cargo attempt stopped at its 90-second wall limit before fixture execution; its Lean attempt exposed `.sink` ambiguity and three downstream `sorryAx` audits. R10 uses a new resource admission and a separate Lean output. It does not alter R9's source, evidence, disposition or unused attempts.

## Exact inputs and fixed Rust source

The 89-entry input manifest authenticates the R9 76-pin dependency cone, the final R9 candidate Rust/Lean bytes, proof handoff, independent review, outcome, contract and manifest, and all eight retained first-attempt logs. Every pin matched at admission. R9's two initial-output pins were replaced by the authenticated final bytes from the R9 review. R10 Lean output is an exact initial copy of the pinned final R9 Lean candidate SHA-256 `747150d9627b84830389ff1b088f43b78da64c3b1f432dbc868a7466b51d1ad9`; its R10 path is revisioned output, not an immutable input.

Rust source stays at `isolated/native-witness-frame-repair-r9/crates/yu-solver/src/candidate_scheme.rs`, SHA-256 `9701321450cda1500a7aa77c0417bcec4a502e006b3c080591a82b7831e9e4bb`, with pinned R9 `candidate_context.rs` and `candidate_extrusion.rs`. No Rust source writer is assigned. The exact focused test, source, feature flag and expected assertions remain unchanged. The prior R9 build-target cache may be reused for speed; cache contents are not evidence or a success criterion. The R9 workspace source files remain read-only.

## Lanes, leases and resource limits

Aggregate fresh envelope: **1,300 seconds**, no renewal; proof 300s, independent review 400s, Luna primary verification/integration 600s; Astra 0. Heavy processes run sequentially.

- Proof: registered `lean_prover`, Sol/high, maximum 300 seconds. May edit only `isolated/native-witness-validation-r10/NativeExternalEffectFrameR8.lean` and `tasks/agent-loop/inbox/native-witness-validation-r10-proof.md`. Fix only the existing `.sink` constructor ambiguity and any directly resulting local elaboration obligations. Preserve all seven theorem types, all assumptions, `WriteAll`, every represented prefix and the exact `extract` premise. No new axiom, `sorry`, `admit`, semantic weakening, new model state or source-domain narrowing. One local repair after the first Lean diagnostic is pre-authorized within the same 300s lane; freeze and fresh review before Lean attempt 2.
- Review: fresh independent `compiler_referee`, Sol/medium, maximum 400 seconds. Authenticate all 89 pins; read governing/source inputs before candidate explanation; accept both fixed Rust source and initial Lean revision before any checks; re-review a changed Lean revision before a second Lean attempt; after checks audit final output and all logs. No checks, writes beyond Luna's persisted receipt, or descendants.
- Luna: primary check/integration lane, maximum 600 seconds; exact check owner and sole Git integrator. No source edits.

Conditional checks only after initial review accepts both outputs:

1. One Cargo attempt, maximum **180s wall**, one CPU (affinity CPU 0), maximum **2 GiB sampled process-group RSS**:

```text
CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target cargo test --manifest-path isolated/native-witness-frame-repair-r9/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

This is one new R10 attempt against the exact R9 source after the distinct 90-second R9 attempt. R10 authorizes no Cargo retry. Timeout/resource boundary closes R10 incomplete.

2. At most two Lean attempts, total Lean wall at most **60s**, each at most 45s, one CPU and `-j1 -M1024`. Lean cwd is `isolated/native-witness-frame-repair-r9/notes/theory/lean` so it uses the pinned Lake/Lean environment; it reads the R10 copy by absolute path:

```text
lake env lean -j1 -M1024 /home/momota1029/rust/yulang/isolated/native-witness-validation-r10/NativeExternalEffectFrameR8.lean
```

The first frozen revision must be reviewed before attempt 1. Only a diagnostic local to the named `.sink` ambiguity/elaboration may use the one repair round. Any changed Lean output is rehashed, reauthenticated against unchanged dependencies, and freshly reviewed before attempt 2. No third attempt. No resource boundary extension.

Retain exact argv, tool versions, complete stdout/stderr, exit, wall/CPU/RSS data in these exact paths:

```text
isolated/native-witness-validation-r10/logs/cargo-1.argv
isolated/native-witness-validation-r10/logs/cargo-1.stdout
isolated/native-witness-validation-r10/logs/cargo-1.stderr
isolated/native-witness-validation-r10/logs/cargo-1.resources.json
isolated/native-witness-validation-r10/logs/lean-1.argv
isolated/native-witness-validation-r10/logs/lean-1.stdout
isolated/native-witness-validation-r10/logs/lean-1.stderr
isolated/native-witness-validation-r10/logs/lean-1.resources.json
isolated/native-witness-validation-r10/logs/lean-2.argv
isolated/native-witness-validation-r10/logs/lean-2.stdout
isolated/native-witness-validation-r10/logs/lean-2.stderr
isolated/native-witness-validation-r10/logs/lean-2.resources.json
```

Generated-path leases are the existing R9 `build-target/` and Lean `.lake/` cache directories under R10 primary ownership, plus only the 12 exact R10 log files above. The R9 source files and final evidence remain frozen/read-only.

## Stop, review and interpretation

Stop on pin mismatch, changed Rust source, fixture/assertion or expected-output change, theorem type/premise/prefix change, `sorryAx`/project axiom, semantic or source-model mismatch, failed required fixture, missing complete type/audit output, or any resource boundary. No check runs before independent initial review. No second Lean check runs before review of its exact revision. Keep all failures and logs. No R10 evidence closes `extract`, std I/O realization, source/native correspondence, `NativeCorrespondence`, the original parent, effect hygiene or production.

Proof handoff: `tasks/agent-loop/inbox/native-witness-validation-r10-proof.md`.
Review receipt: `tasks/agent-loop/inbox/native-witness-validation-r10-review.md`.
Outcome: `tasks/agent-loop/history/native-witness-validation-20261028-r10-outcome.md`.
