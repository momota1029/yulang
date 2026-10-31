# Sprint EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15

Status: admitted by Luna under the unchanged ongoing Simple-sub inference/executor goal after R14 `CLOSED_INCOMPLETE` and the recorded sprint-end selector recommendation.

Baseline: R14 proof candidate archived at `tasks/agent-loop/history/artifacts/FormalPermissionTermCallControl-r14.lean`, SHA-256 `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`; R14 failed audit receipt `19a8aacc9932ea3003103b71b5b728340bc3ed8b46bc4497aaa5e110a65bf86b`; all Rust source pins remain unchanged from R14. R12/R13 declarations and the original goal are inherited unchanged.

Authority: unchanged original Simple-sub inference/executor research goal. This is a proof-construction repair only. It does not establish Rust execution correspondence, constructor or sampler availability, primitive authenticity, native publication, or production.

## Fixed outcome

Repair the one failed R14 proof in `control_test_fields` while preserving the theorem declaration, source-directed control model, all assumptions, and interpretation. In the `accounting = true` branch, use `loop_test_fields` on `loopState events (drained constructor events s)`, then simplify the unconditional constructor/event drain's instrumentation projection. The false branch remains the existing drain-only proof. The repair must not strengthen hypotheses, alter definitions, change theorem statements, narrow the source domain, or modify inherited modules.

Success requires one full pinned Lean 4.35.0 audit printing theorem types and complete transitive axiom reports for all 38 roots: 9 R12, 10 R13, and 19 R14 roots. If Audit 1 fails and the proof lane still has budget, the same worker may make a proof-only repair and freeze rev2/rev3 before the one remaining audit. A successful complete audit enables one fresh independent `compiler_referee` review. R14 remains an incomplete proof candidate until this gate passes.

## Lanes and exact permissions

Proof owner: fresh registered `lean_prover`, 300 seconds. Write only `notes/theory/lean/YulangClosure/FormalPermissionTermCallControl.lean` and `tasks/agent-loop/inbox/effect-permission-term-call-control-r15-proof.md`. The existing R14 artifact path is re-leased sequentially after R14 writer cessation and byte archive. Reuse inherited declarations unchanged.

Source lane: primary Luna, read-only, 100 seconds. Frozen handoff: `tasks/agent-loop/inbox/effect-permission-term-call-control-r15-source.md`; no source edits or execution.

Independent reviewer: fresh nonauthor `compiler_referee`, 250 seconds, only after a complete successful primary audit; write only `tasks/agent-loop/inbox/effect-permission-term-call-control-r15-review.md`.

Primary Luna: 150 seconds for contract/manifest/evidence, no more than two primary audits, review adjudication and closeout. Total envelope 800 seconds. Zero Astra and zero descendants.

## Audit and resource limits

Use pinned Lean 4.35.0 and the exact 38-root inventory in a fresh isolated project copy. At most two separately frozen primary audits, each no longer than 90 seconds, combined wall time no longer than 120 seconds. Use one primary-owned build/cache, `-j1`, `-M1024`; call the checker with its absolute repository path and keep helper temporary files under the sprint scratch directory. Preserve stdout, stderr, status, resource and input-copy receipts for each actual invocation. Do not run probes, tests, Cargo, Rust code, instrumentation, package updates or Git operations.

## Stop conditions and open gates

Stop if `control_test_fields` cannot be repaired by applying `loop_test_fields` and simplifying the existing drain without changing the theorem/model; if any inherited root fails; if the worker or audit budget expires; if the exact paths conflict; or at user STOP/session end. A failed proof audit is not a mathematical counterexample. Do not start review before all 38 roots pass.

R14 control-flow theorem, sampler availability, actual Rust-to-model execution linkage, primitive/alias authenticity, native publication, original parent, effect hygiene, consumer residual, soundness, principality, termination and production remain OPEN until their own evidence is established.
