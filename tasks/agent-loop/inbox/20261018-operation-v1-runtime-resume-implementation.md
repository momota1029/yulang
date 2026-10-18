# Frozen assignment handoff

- Sprint: `operation-v1-runtime-evidence-and-callback-resume-20261018-r18`, revision 2; contract SHA-256 `225d4c59aad72d5731aed0adc97f0dc31adf5931f8a66484366a5b2058bdf07e` (revision 2 clarifies execution order only; revision 1 goal and constraints remain frozen).
- Assignment/handoff ID: `r18-runtime-resume-implementation`, revision 1, reconciled against sprint revision 2.
- Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original quantifiers and source/native correspondence preserved. Parent remains OPEN; original conditions closed **0**.
- Role/worker: implementation lane `/root/r18_runtime_implementation`, current session; assignment arrived through the parent collaboration message. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. No model-switch claim.
- Exact write lease used: `tools/inference-playground/src/lib.rs`, `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/tests/runtime_resume.rs`, and this handoff. `continuation.rs` was inspected but not changed. No scratch or generated paths.
- Outcome class: implementation candidate; fresh independent review and focused runtime checks pending. This handoff is not a theorem or production receipt.

## Result and source/native correspondence

Added `execute_operation_v1_runtime_research`, an explicit opt-in route. It lowers one HIR, runs `CandidateInference::solve_operation_v1_research` on that exact `Arc<HirModule>`, requires exactly one consumed FieldBoundV1 and no candidate conflicts, and passes the receipt into a `RuntimeProgram` built from that same HIR. A pointer identity guard rejects a receipt attached to a different HIR.

The runtime constructor rechecks the public receipt against retained source code: the ping request is an operation under its source Apply; the matching Catch contains the actual `k response` Apply; its callee resolves to that Catch binder and its argument resolves to the receipt's exact local response definition; that definition initializes the Lambda containing the receipt's callback Apply and operation use. The callback operation and its enclosing Apply remain distinct static identities.

Machine evidence is recorded only as execution occurs. The response name read supplies the actual closure value from the exact local cell; the saved `ResumeArgument` accepts a Function response only on this v1 path and only when that value is the exact source Lambda from that definition. It retains the closure's actual lexical environment and confirms the same handle/environment is applied at the recovered `k response` Apply. The callback operation-use occurrence must execute while that closure is active. Its request event must carry the callback Apply source, reach the statically recovered live outer handler and its exact arm, and the machine must finish with `Completed(Integer("42"))` before the receipt is returned.

The focused source places `(catch signal::ping() { ... k response ... }) 0` inside an annotated `[signal, outer] int` computation argument and wraps it in the live outer-operation handler. The handler arm evaluates `k response`; the raw saved continuation returns that exact closure; the surrounding source Apply then invokes it with its captured environment while the outer catch remains active; `outer::next` reaches that live arm and returns 42. The callback Apply is not claimed to be part of the captured suffix. Existing `Receiving::local_grant` remains required for both operation events. No family/type-only callback, candidate-only visibility grant, Simple-sub bypass, ordinary execute change, scoped-mode change or production default change was added.

No completed runtime receipt has been observed yet: checks remain gated on independent review. The code path withholds a receipt for candidate conflicts, absent or ambiguous source linkage, a different HIR, missing handler, mismatched request/closure, runtime failure, exhaustion, or a result other than integer 42.

## Prior evidence and remaining premises

Reused r17 r6 design and closeout only for the reviewed source identities, successful consumed static FieldBoundV1 receipt, and final conflict gate. The recorded r17 focused test result (16/16) is historical static evidence; it was not rerun and does not establish runtime behavior. Reused the proof lane's frozen baseline correspondence audit, artifact SHA-256 `0f13f02ad058c8b74b7c4f907a1b9b1fc89345b8c5498707f9c253f2455e3ceb`, and proof handoff SHA-256 `f3e35103057daf64fb4dc8a7fef24b729ac379212c4a448fd4b0516171d04627`. Its function-response, exact-source-join and local-grant findings are addressed by the opt-in source checks and the annotated computation-formal test shape. No inference is made from that audit to a running result.

Independent review must verify the function-response exception at both runtime consumers, the same-HIR/LocalSource join, actual closure handle and environment through `ResumeArgument`, exact callback event and Apply source, live handler installation, real `local_grant`, selected arm and final completion gate. The focused `yu-playground` runtime resume tests must then run after review is CLEAN. Whether the proposed source is accepted by the current solver and receives the expected runtime Grant is unresolved until that gated run. Original A/B premises, general source coverage, other callback forms, soundness, principality, termination, production admission and the parent theorem remain OPEN.

Frozen code hashes:

```text
bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b  tools/inference-playground/src/lib.rs
da2a1e74f95664516cb8ba5eafcf53e7386e9b12435da5fef069a965da26845f  tools/inference-playground/src/runtime/program.rs
a477e2eae57f826377d71d0d29cfffa5e6b46ca9c58bdc4b332f174d1a0955ef  tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs (unchanged)
4fd45306e68bc3665a38644c2369ab2a95e331a40b22ac68a777d1819a3a5cb6  tools/inference-playground/tests/runtime_resume.rs
```

Frozen read-only dependency checks:

```text
472ea2f65946bf815834decf599fd105f20dc0c97fde9711746b8d87c0fea1c4  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18.md
225d4c59aad72d5731aed0adc97f0dc31adf5931f8a66484366a5b2058bdf07e  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18-rev2.md
276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54  notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a  crates/yu-solver/tests/candidate_operation_catch.rs
```

## Checks, budgets and stop

- Added focused runtime controls in `runtime_resume.rs` for the successful source path, a same-family different callback operation, a same-family alternate response definition under a mismatched HIR receipt, no outer handler, non-42 result and exhausted execution.
- Checks/builds: **not run**, per the frozen review gate. No tests, Cargo/build/compiler probes, formatter, Git command, network action or nested CLI was run for this assignment.
- Resource grant: implementation allocation 1500 seconds; conservatively reserve/charge the full grant. Actual active elapsed time, CPU, RSS and tokens: UNKNOWN. Astra: 0. No budget extension requested.
- Review: NOT RUN; the author does not self-review. Focused test execution remains blocked until fresh independent review is CLEAN.
- Worker state: STOPPED; writes ceased after freezing this handoff. Descendants and unresolved descendant leases: none. No further in-envelope step remains for this author before review; next step is independent review, then the focused runtime target if CLEAN.
