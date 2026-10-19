# R122 implementation handoff — Luna additive repair

Status: frozen pending three fresh delta reviews; no test/build/CLI/probe run.
Contract boundary clarification: R122 rev7, `tasks/agent-loop/sprints/receiver-permission-cli-20261019-r122-rev7.md`, SHA-256 `b29680fb01e98032dcf4472487190af97ddc19f8a4377d405cc7c0e586763cfd`.

## Preservation and result

The implementation lane initially wrote over a tracked R105 CLI target because
its candidate contract described the path as new. Regression review caught the
provenance before any command ran. Luna inspected the branch HEAD blob, restored
it byte-for-byte, then appended only a distinct direct-Machine test. The
existing `receiver_permission_controls_cli_publication` test, its `POSITIVE` /
`NEGATIVE` source constants, `run` helper, CLI arguments, and expected streams
are an unchanged prefix of the final file.

The original target baseline is SHA-256
`8c083bf45f889aa69f1bdaec13ebbc6bcc20f032f7e29167862ef189a11e99e4`; exact
prefix comparison returned `baseline_prefix_preserved = true` and 2,096
appended bytes. The final test file is SHA-256
`543271f4bea2f488c8997d82178fdf9cfdbcc6e85441bee58f8e5aa25cf0bb67`.

The appended `nested_receiver_permission_has_distinct_machine_outcomes`
reuses the preserved exact P/N constants. Each setup requires syntax success,
source lowering, successful CandidateInference with no conflicts,
RuntimeProgram construction, main selection, and machine start. P must complete
with integer 7. N must produce exactly
`RuntimeOutcome::Unavailable(RuntimeUnavailable::HandlerEvidence(_))`; it has
no completed value. The untouched existing CLI test runs with `--steps 10000`, asserting P
success/`7\n`/empty stderr and N failure/empty stdout plus the existing
`.contains("runtime unavailable: HandlerEvidence")` diagnostic check. The
separate direct-Machine test uses its 30,000-transition bound. One authorized
Cargo command will exercise both tests in this target; the Machine bound does
not imply CLI completion within 10,000 steps.

## Inputs, review, and resource accounting

All 26 rev4 source/dependency pins were checked by the implementation lane and
matched. Rev6 adds the exact target baseline pin above. The proof lane separately
reported all 26 source/dependency pins matched. The prior rev4 implementation
candidate SHA `52bed7c2368742f4f5cae86a150cf1f455fd049828c4007f880c83767a6a48da`
was not run and is superseded by this baseline-preserving repair.

The implementation lane charged 100 seconds before resumption. Resumed work was
not instrumented; rev6 conservatively charged the remaining 260 seconds, so the
original 360-second lane cap is fully spent. Luna's restoration, append and this
handoff update fit inside the separate 120-second closeout allowance. No test,
build, CLI, runtime probe, formatter or Git operation was run by the producer
or during this repair. No extra path or child worker was created.

Requested implementation model/effort Luna/high; observed model/effort
UNKNOWN/UNKNOWN. The implementation lane stopped before the preservation repair;
Luna owns the final additive bytes. The test and handoff are frozen for fresh
compiler/source, spec/authority and regression delta review. The existing CLI
assertions and 10,000-step budget are unchanged. No author certifies
this artifact. R117-JOIN-1, all effect parents, method/role premises, and the
original Simple-sub/evaluator A/B claims remain open.
