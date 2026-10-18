# r18 — runtime evidence and callback resumption

## Fixed outcome

Complete one bounded Phase R path from the reviewed r17 static receipt to real execution. For one accepted research-only source, keep the same HIR and successful candidate, pass the exact callback argument closure and captured environment through the saved continuation, execute the callback, route its `outer::next` request to the still-live outer handler, evaluate that handler arm and return integer `42`. Emit a completed receipt only after the runtime reaches that result and the dynamic evidence is joined to the static FieldBoundV1 source identities.

Original parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, with all original quantifiers and source/native correspondence intact. This sprint may close only the stated single-source runtime obligation; it cannot close the parent theorem or infer production soundness.

## Accepted meaning and gate

Use the existing source semantics: `k response` applies the actual response value saved by the matched source Apply; a lambda keeps its lexical environment; the resumed saved continuation may issue `u_outer`; handler search selects the live matching outer catch. Do not synthesize a callback from family/type equality, replay a different candidate's receipt, discard or rebuild the HIR/candidate between checking and execution, or report completion before actual arm evaluation.

The research entry is explicit and opt-in. Ordinary `execute`, standard inference, scoped-experiment mode and production defaults remain unchanged. Failure, exhaustion, unhandled request or mismatched identity yields no completed receipt.

## Baseline and dependencies

HEAD: `2a3f2a47d5013761f0e0717b0c6073c54c62d36c`. The baseline also includes the reviewed, tested but uncommitted workspace bytes below; they are dependencies and must not be rewritten by r18:

- r17 design `notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md`: `276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`
- solver source `candidate_source.rs`: `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c`
- solver effect `candidate_effect.rs`: `6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0`
- solver candidate API `shadow_apply.rs`: `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`
- solver private mode `lib.rs`: `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee`
- r17 test `candidate_operation_catch.rs`: `7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a`
- runtime entry `tools/inference-playground/src/lib.rs`: `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`
- runtime program `program.rs`: `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`
- runtime machine `machine.rs`: `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82`
- continuation `continuation.rs`: `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`
- runtime tests `runtime_resume.rs`: `1c1a4f402c87088454bf31eee2c1eee8d5ff9ec716fe2282ed4fe421b6469859`

## Lanes, budget and exact leases

Total new cap: **3000 seconds**, no Astra. Allocation: constructive proof **600s**, implementation **1500s**, independent review **600s**, focused execution/integration/state **300s**. Do not transfer or reset spent reservations without a Luna/dispatcher decision.

- Luna/high implementation writes only `tools/inference-playground/src/lib.rs`, `src/runtime/program.rs`, `src/runtime/machine.rs`, `src/runtime/continuation.rs`, `tests/runtime_resume.rs`, and its single handoff `tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-implementation.md`.
- Sol/high proof writes only `notes/theory/2026-10-18-operation-v1-runtime-resume-correspondence.md` and its single handoff `tasks/agent-loop/inbox/20261018-operation-v1-runtime-resume-proof.md`.
- Luna owns this contract, the design note, `tasks/agent-loop/current.json`, integration and Git.
- Solver files and existing r17 design/test artifacts are read-only dependencies for both lanes.

## Evidence and falsifiers

Focused success requires all of: exact same-HIR accepted candidate; exact static callback Apply/operation/response-definition identity; the runtime closure actually selected from that definition with its lexical environment; saved application reaches that closure; exact `u_outer` request occurs while the expected outer handler is active; that concrete arm executes; returned runtime value is integer `42`; and the completed receipt joins these facts without identifying static and dynamic IDs as if they were the same type.

Negative controls: same-family but different callback definition, different HIR/candidate receipt, wrong runtime request, no live outer handler, exhausted run, and an arm that does not return 42. None may produce a success receipt. If current runtime structures cannot establish this join within the leased paths, stop at that seam and return the exact missing evidence; do not weaken the predicate.

## Review, test and stop

Freeze code and proof outputs, then obtain fresh independent review of the exact producer-to-runtime-consumer diff and proof dependencies. Run only the focused `yu-playground` runtime resume test target after review is CLEAN; distinguish unrelated known formatting/CI failures. Record actual pass/fail output and hashes. Keep the parent OPEN/closure 0 absent proof of the original theorem.

At closeout report: original unresolved conditions closed (likely 0); actual implementation/test behavior; remaining unproved condition and the next single owner-bound step. Git must record the unchanged branch if writes remain blocked; do not bypass approval or local `.git` restrictions.
