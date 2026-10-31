# R106 source admission and module-faithful bridge validation

Status: **ADMITTED** under the standing user-authorized Rust/Lean goal.
Parent goal remains Yulang inference/source soundness and effect hygiene. Keep
the original Simple-sub source domain, A/B claims, quantifiers, semantic
authority, production gates and expected outputs unchanged.
Baseline: `80d34e645` (R105 Rust evidence checkpoint).
R105 outcome: `tasks/agent-loop/history/effect-permission-source-contract-20261101-r105-outcome.md`.
R105 contract SHA-256: `7285a5d8cb6ca8d39c8f0427278c633ecccaf12d8591e9109825c7afce162e4d`.

## Fixed evidence and goal

R105 Rust review established a fixture/source-admission obstruction, not a
solver omission. The shared-tail helper bypassed `CandidateInference::solve`;
its terminal body shape does not match the named-header annotation. The other
three protected failures do not establish an owner-local defect. Do not change
existing fixtures or semantics.

R105's bridge source review passed, but its sole flattened Lean invocation
failed before the R105 declarations: the earlier `YulangClosure.Step` in
`Contracts.lean` shadowed the intended auto-implicit `Step` in concatenated
`NativeDictionaryDenotation.lean`. The flattened call allowance is exhausted.
R105's frozen bridge candidate is unverified, not rejected. Preserve its exact
bytes as the validation input.

## Rust lane: establish an admitted source path

Owner: Luna/high implementer; fresh independent compiler referee. Exact mutable
paths:

- `crates/yu-solver/src/candidate_effect.rs`, test code only.
- `tasks/agent-loop/inbox/effect-permission-source-admission-r106.md`.

Read-only source owners: `crates/yu-solver/src/candidate_source.rs`,
`crates/yu-solver/src/shadow_apply.rs`, and
`crates/yu-solver/src/candidate_scheme.rs`. Preserve their current bytes and
the four R104 fixtures/assertions. First trace ordinary `CandidateInference::solve`
preflight and determine what that route actually admits. Derive one correctly
shaped source witness for the named result annotation, returned function,
capture, fresh use and real consumer, or report `NO_SAFE_CODE_SLICE` with the
exact admission barrier. Do not manufacture graph constraints or infer a
solver omission from R104's unadmitted helper.

Only a separately named reviewed test candidate that uses the ordinary source
route may spend the single Cargo call. Exact command:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests::r106_ -- --test-threads=1 --show-output
```

Run once at most, CPU affinity 0, `timeout -k 5s 180s`, peak RSS ≤2 GiB, one
Cargo process, target
`/dev/shm/yulang-effect-source-admission-20261101-r106-target` ≤6 GiB, and
verify complete cleanup. No retry, second Rust command, persistent cache, or
semantics change. A rejected/missing candidate spends no Cargo call.

## Proof lane: compile with module boundaries intact

Owner: registered `lean_prover`; fresh independent proof reviewer. The R105
module and handoff are frozen read-only inputs:

- `notes/theory/lean/YulangClosure/SourceLogicalOwnerBridgeR105.lean`, SHA-256
  `6fecc134ac2009392f043331eb4d1a3dd479668208991e60c8a5d339e69b45b4`.
- `tasks/agent-loop/inbox/effect-permission-logical-owner-r105-proof.md`, SHA-256
  `32f3fcf62b5fbc14eb040d570e0752e0ab8a8ad65e44f5f6c2f7b65f14baf422`.

The only proof-author write is
`tasks/agent-loop/inbox/effect-permission-logical-owner-r106-module-validation.md`.
Inspect and pin every import edge for the 13 modules in the R105 handoff (12
dependencies plus the bridge).
Prepare a module-faithful validation plan that compiles each unchanged module
separately in topological order and then compiles the R105 bridge as its real
module, resolving imports only from a fresh unique `/dev/shm` output root.
This keeps each module's command/namespace scope intact and must not alpha-rename
or alter source declarations. Freeze all source hashes, dependency order,
commands, executable hash, target cap and cleanup proof for independent review.
The proof author runs no Lean/Lake/checker/build/version/test command.

After a fresh review PASS, Luna may execute exactly one module-faithful batch:
12 dependency module compilations followed by the one R105 bridge compilation
(13 module compilations total), in the frozen order. Each call uses Lean
4.35.0, `-j1 -M1024`, CPU affinity 0
and a 60-second hard timeout; aggregate Lean active time is capped at 1,200
seconds. Write `.olean` outputs only under
`/dev/shm/yulang-source-owner-module-validation-20261101-r106`, capped at 2
GiB; delete it after the batch and verify absence. No flattened retry, Lake
cache, persistent build, alternate Lean invocation or source edit is authorized.
If any dependency fails, stop the batch immediately, preserve the exact failure,
and do not run later modules. On success, record all actual bridge theorem
types and complete axiom reports. This establishes only the R105 syntactic
bridge; original logical admission, the parent theorem, source/native, A/B,
effect hygiene and production remain open.

## Shared envelope and integration

Total sprint active-work envelope: 2,400 seconds; Astra 0; at most four known
active/reserved assignments. Rust Cargo and Lean module batch are serialized.
No worktree, persistent environment, dependency change, root target or global
configuration change. Obtain independent pre-execution reviews on frozen hashes
and a fresh receipt review after each executed gate. Luna alone stages explicit
paths and pushes a coherent reviewed range. Preserve all unrelated dirty and
quarantined paths. Stop on source-semantic change, outside-owner dependency,
review rejection, resource/cleanup failure, or sprint completion.
