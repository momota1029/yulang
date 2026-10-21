# R272 — ordered Tuple runtime construction

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 playground and proof-backed compiler/evaluator goal; R149 Types/Console remain the immediate end-to-end increment.
Baseline: `9f5abce08` on `research/simple-sub-intrusion`.
Authority: approved arbitrary finite ordered product behavior and left-to-right evaluation in `notes/design/2026-10-20-r149-types-console.md`; runtime obstruction in `notes/theory/2026-10-21-r256-tuple-source-runtime-obstruction.md`; R270/R271 source candidate and Value graph repairs.

## Outcome

Compile a retained source Tuple into an ordered runtime constructor and evaluate each element left-to-right exactly once. Preserve each element's `ReceivedValue` (including its receiving view) across unhandled requests, handler capture, continuation copying and resume. Support arbitrary finite arity, including nested tuples. Keep the runtime's source-order and iterative evaluation model.

Success evidence: source Tuple no longer fails runtime compilation; direct and nested tuples complete with element order and value identities intact; a tuple whose later element requests an operation resumes through its handler without re-evaluating an earlier effectful element; focused runtime resume and tuple checks pass.

Falsifiers: child order changes; any child runs more than once across a continuation resume; element interface/view is discarded; tuple-prefix state mutates across copied continuations; or the constructor cannot resume after a request in a later element.

## Exact write paths

- `tools/inference-playground/src/runtime/program.rs`
- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/mod.rs`
- `tools/inference-playground/src/lib.rs`
- `tools/inference-playground/tests/runtime_resume.rs`
- this contract
- `notes/theory/2026-10-22-r272-runtime-ordered-tuple.md`
- `tasks/agent-loop/inbox/20261022-r272-runtime-ordered-tuple.md`
- primary-owned `tasks/agent-loop/current.json`

No public closed Tuple type, pattern/destructuring support, host `out::write`, standard-library resolution, unchanged sample acceptance, proof closure, or production promotion in this packet. Any CLI rendering added for the new public runtime value must recursively preserve tuple structure and be an actual rendering, not a placeholder. This runtime remains provisional.

## Method and limits

Add a source-ordered `Instruction::Tuple`. Evaluate one child at a time using an explicit frame. Store completed children as immutable nodes in a machine-owned prefix arena; frames carry only an index and prefix handle so `SavedFrame::Ordinary(Frame)` cloning shares prior prefix state and each resumed branch appends independently. Reassemble the tuple in source order only after all children return. Keep the continuation representation iterative.

Budget: 1200 seconds, no carryover, one heavy Cargo process. Solo primary work; no independent review is available under the user's instruction. Keep implementation/runtime evidence primary-only and provisional. Commit and push the coherent checkpoint after focused verification. Unchanged Y2 samples, public inference, import/publication, A/B, source/native proof, soundness, principality and production remain OPEN.
