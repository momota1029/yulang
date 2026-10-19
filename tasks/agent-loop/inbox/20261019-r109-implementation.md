# R109 implementation inventory

Status: FROZEN FOR INDEPENDENT REVIEW; read-only inventory only.
Lease: `tasks/agent-loop/inbox/20261019-r109-implementation.md`.
Contract: `tasks/agent-loop/sprints/nested-handler-observation-20261019-r109-rev1.md`.
Contract SHA-256 at inspection: `834bf38f690b9fa9fc617a57e40e1c09bbce996949176aafdf5f6e995bc8eb43`.

## Frozen implementation input

The existing test is `tools/inference-playground/tests/runtime_handler_priority.rs`, 4,221 bytes, SHA-256 `cdcb06ceebcca48cd3ff6fbc1a429243e9013a148c5fc895d9926e5dc2ce07db`. Its sole test is `nested_handler_priority_and_shallow_arm_requests`. The exact file bytes match the R109 frozen test pin. No source, test, fixture, expected output, or production file was edited by this lane.

The file composes `IO` and `NESTED` as `format!("{IO}{NESTED}")`. `IO` declares `tick` and `other`, each `int -> int`. The fixed nested source is:

```text
my inner (thunk:[io] int) = catch thunk { io::tick(p), _ -> io::tick 11, io::tick(p), _ -> io::tick 23 }
my outer (thunk:[io] int) = catch thunk { io::tick(p), _ -> p }
my main = outer (inner (io::tick 7))
```

## Public preparation and execution route

The test itself exercises this route, in order:

1. `parse_file` with `scan_header` and an empty `SyntaxEnvironment`; require no syntax diagnostics.
2. `lower_module_with_local_source` using `ModuleIdentity::source_root` and empty semantic imports.
3. `CandidateInference::solve`; require no candidate conflicts.
4. Retain source operation declaration spellings/IDs from the lowered HIR.
5. `RuntimeProgram::from_hir(hir, RuntimeEvidence::default())`; select `main`, obtain `execution_roots`, then call `start`.
6. Call `Machine::run(10_000)` and inspect the returned `RuntimeOutcome` and value/source data.

The only authorized command target is the existing exact integration test:
`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_handler_priority nested_handler_priority_and_shallow_arm_requests -- --exact --nocapture`.
It remains Luna-only and NOT_RUN by this lane. No build, test, compiler, runtime, formatter, CLI, or Git command was run here.

## Three immutable cells and assertions

1. Baseline: exact `IO + NESTED`; `assert_completed_integer` requires `RuntimeOutcome::Completed`, an integer value, and string value `11`.
2. Inner-arm swap: one `replacen(..., 1)` swaps only the inner bodies `io::tick 11` and `io::tick 23`; `assert_ne!` ensures a changed source string; the same helper requires integer `23`.
3. Outer-operation mismatch: one `replacen(..., 1)` changes only the outer pattern `io::tick(p)` to `io::other(p)`; `assert_ne!` ensures a changed source string. The test requires `UnhandledRequest`, operation identity equal to the source module's `tick` declaration ID, integer payload `11`, and request source range equal to the inner `io::tick 11` span. It separately rejects the initial `io::tick 7` range and requires the selected bytes to be exactly `::tick 11`.

These are source-string construction and assertion facts only. They are not observed runtime outcomes until Luna's authorized one-shot command and fresh reviews complete. R101/R102 commands remain NOT_RUN; no static parser/CST completeness, universal hygiene, source-wide correspondence, native residual, Simple-sub, evaluator, or adoption claim is made.

## Pin audit and receipt

All 16 direct R109 pins were read-only SHA-256 checked and matched the contract: R101 rev2 contract, conditional proof, proof and implementation handoffs, R101 closeout, charter, ordinary-computation package, R88 source bridge and closeout, current `machine.rs`, `receiving.rs`, `program.rs`, `primitive.rs`, `local_source.rs`, `runtime_receiving.rs`, and this exact test. The current `program.rs` pin is the contract's current version; the separate historical R101 pin remains historical and was not substituted for it.

- New path: `tasks/agent-loop/inbox/20261019-r109-implementation.md`.
- Disposable scratch paths: none.
- Diff/checks: no source edits; read-only exact-file inspection and SHA-256 audit only.
- Command receipt: none; authorized test command is NOT_RUN.
- Budget: stopped after inventory freeze, within the 180-second implementation allocation; no command budget used.
- Requested model/effort: Luna/high per the fixed sprint role. Observed runtime model/effort is not exposed to this lane and remains unverified; no fallback or model change attempted.
- Frozen handoff ID: `R109-IMPL-20261019`; handoff SHA-256 is recorded by the primary after freeze.
- Next in-envelope step: independent post-output review of frozen inputs and this inventory; only Luna may decide whether to run the one authorized command.
