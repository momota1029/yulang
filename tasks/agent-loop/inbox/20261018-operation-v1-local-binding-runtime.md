# Frozen R19 local-binding runtime handoff

- Sprint: `operation-v1-local-install-use-lineage-and-capture-20261018-r19`, revision 1; contract SHA-256 `75eba332166f8ffece47fe2ccbe6513058b151cc76fa74545ba56c3ca70977fd`.
- Assignment ID: `r19-local-binding-runtime`, handoff revision 1.
- Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original source/native domain and quantifiers preserved; parent OPEN, closure 0.
- Baseline: R18 `d51baa6db`; current workspace head at assignment start `eeafa05c58a62f0a447a061520620368bdc59a9e` (contract/state checkpoint only; runtime baseline bytes unchanged).
- Role/session: implementer `/root/r19_local_binding_runtime`, current session. Requested model/effort Luna/high; observed model/effort UNKNOWN/UNKNOWN. No separate launch/session receipt was available.
- Exact write lease: `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/tests/runtime_resume.rs`, and this file only. No scratch/generated output created.
- Outcome class: provisional implementation/source-lineage instrumentation. It does not establish a successful new execution trace or theorem result.

## Work and boundary

The research plan now derives an optional local lineage only when a spelling-`g` local has an initializer `Catch` whose source subtree contains the accepted operation request, and a resolved local `Name` is the callee of an Apply in that same source root. It rejects ambiguous/missing matching uses and Apply-site aliasing with the continuation Apply, response-invocation Apply, or callback Apply. Ordinary R18 sources without such a qualifying local `g` retain the old plan path.

The runtime trace is provisionally extended to require that the initializer Catch actually runs under the owner that completes the local initializer, that the exact local cell stores a closure with its retained environment, that the resolved Name reads that same cell/value, and that the exact Apply invokes that same closure/environment. The resulting invocation owner must be the callback operation's owner; the existing callback request/event, local-grant, live outer handler/arm, response closure, and post-`Completed(42)` checks remain in place. Public receipt fields and solver code were not changed.

The test source is derived from the existing R18 source by making the operation Catch the initializer of local `g` and calling `g 0`; its sibling control shadows `g` with a second local cell. This is not yet evidence that the unchanged solver accepts the transformed source or that its existing static receipt can be joined. By source inspection, the existing `source_apply_for_catch_result` searches for an Apply whose *callee subtree contains the operation Catch*. With this target shape the Catch is in `g`'s initializer and `g 0` is a separate use, so the first unresolved boundary is the unchanged source/runtime join. Do not widen or rewrite that join in this lane. The unchanged candidate and one-consumed, conflict-free FieldBoundV1 receipt remain an unverified precondition; no solver call was run.

## Evidence, checks, and limits

- Reused R18 evidence: frozen R18 rev4 implementation handoff and baseline runtime files; R18's existing `runtime_resume` cases and its reported 17/17 focused result. This assignment did not rerun those tests.
- Rejected as insufficient for R19: R18's direct callback trace alone has no initializer-Catch -> local binder/cell -> resolved Name -> local Apply join. It does not prove the new source precondition.
- Checks/builds/formatters: **NOT RUN**, as required before independent review. No source acceptance or execution result is claimed.
- Diff/direct dependency check: solver files, `tools/inference-playground/src/lib.rs`, continuation runtime, and the two governing design files retained their pinned SHA-256 values. This was read-only inspection, not a test.
- Exact changed artifact hashes at freeze:

  ```text
  eb7f80345ac938fad671bae5ac6cedc1d9da94dbdf1d9bd0df193aaa2dfd3956  tools/inference-playground/src/runtime/program.rs
  fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46  tools/inference-playground/src/runtime/machine.rs
  7f59ba693829c7568c057450ccdde77b768466033b668e8199fc19b7c07339e1  tools/inference-playground/tests/runtime_resume.rs
  ```

- Resource: assignment cap 600 seconds, conservatively charged on issue; actual elapsed/CPU/RSS/tokens UNKNOWN. Astra 0. No renewal requested.
- Independent review: NOT RUN; author does not self-review. No code/test repair after freeze is authorized absent a new acknowledged lease or review delta boundary from Luna.

## Parent/source/native correspondence and TODO

The provisional runtime identity chain is source initializer Catch -> exact local `HirLocalId` -> resolved Name occurrence -> local Apply occurrence, then runtime installed cell -> closure handle/environment -> read cell -> invocation owner -> callback operation/request owner -> R18 live outer handler arm -> `Completed(42)`. The chain is fail-closed and is not yet observed for the new source shape.

Runtime lineage alone does **not** establish FieldBound Capture, FreshUse transport, a use-specific native consumer, or the original parent theorem. The solver constructors/consumers remain read-only and unchanged.

- TODO `R19-RUNTIME-SOURCE-JOIN-01`, owner: Luna/source-owner lane. Using the unchanged candidate and exact source/action owners, determine whether a source with initializer Catch `g`, separate resolved `g` Apply, and the existing response-invocation Apply can produce the existing consumed/conflict-free FieldBoundV1 receipt and satisfy `source_apply_for_catch_result`. Inputs: this frozen source/test artifact and R19 baseline solver hashes. Output: exact accepted source and source/native identity map, or the first existing owner/premise that cannot form the join. Falsifier: sibling `g` binder/cell supplies the use, or the existing candidate/runtime join has to be remapped to another Apply. No semantic/source-domain change is requested.

## Stop and hygiene

Writes stopped after these four leased paths. No review target was changed after freezing; no independent reviewer was assigned by this worker. Known pre-existing quarantined/disposable paths observed at startup remain outside this lease and untouched: `notes/theory/2026-10-18-replay-constructor-lineage.md`, `notes/theory/2026-10-18-replay-constructor-separate-test.md`, `tasks/agent-loop/inbox/20261018-replay-constructor-separate-test-proof.md`, and `tools/__pycache__/`.

Next in-envelope step: independent review of these frozen bytes, then Luna-owned focused `cargo test -p yu-playground --test runtime_resume` only after CLEAN review. The test/source acceptance boundary above may stop the target before any new runtime receipt exists. No cutover or native-consumer claim follows from this handoff.
