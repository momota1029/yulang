# Sprint EFFECT-PERMISSION-INTEGRATION-CANDIDATE/20261102-R127

Status: ADMITTED bounded in-memory composition of previously reviewed Rust candidate patches. The standing Yulang soundness/effect-hygiene goal remains open.

## Objective and delivery boundary

At the common immutable baseline, compose R111's three-file compile-repair candidate with the reviewed R117 and R119 receiver patches. Produce exact full-file candidate hashes and hunks, or the first exact context collision. The receiver target must be derived from the R111 four-repair candidate plus R117 then R119 in the same exact patch order already reviewed in R120; no fuzzy/context-dropping application. Preserve all source lines outside the authorized hunks.

This is an in-memory candidate composition, not source integration. Do not create a worktree, copy, synthesized source file, scratch/cache, environment, or storage probe. Do not edit Rust/Lean/tests, run compiler/build/test/Lean/checker, mutate Git, stage or push source. R111's hard private aggregate 6 GiB verifier gate remains unmet; its single compile allowance remains unused and blocked. R127 cannot relax or replace that gate.

## Inputs and exact leases

The current branch baseline is `yulang3` commit `b5f4df250` (full commit recorded in the manifest). R111 source input is baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`; Luna has authenticated that `lib.rs`, `candidate_receiver.rs` and `candidate_effect.rs` have identical full-file hashes at both commits. Reuse R111's independently reviewed target hashes for lib/effect/receiver. R117/R119 patches and the R120 composition receipt are frozen direct inputs in the manifest.

- Implementation lane owns only `tasks/agent-loop/inbox/effect-permission-integration-candidate-r127-implementation.md`; max 300 seconds.
- Registered `lean_prover` lane owns only `tasks/agent-loop/inbox/effect-permission-integration-candidate-r127-proof.md`; max 300 seconds. It inspects the immutable proposed target description against R126, R121 and R119 evidence, with no Lean execution or new declaration.
- Luna owns contract, manifest, admission, review, current state, outcome and Git.
- Fresh independent compiler referee after both handoffs freeze; max 180 seconds. Primary integration max 240 seconds. Total ≤1,020 seconds; Astra 0.

The proof lane may independently inspect already frozen R126/R39/R121/R119 evidence while implementation composes, but it cannot assert properties of the combined receiver until the implementation handoff freezes. A newly reached dependency, overlapping patch context, changed guard/borrow/source behavior, or discrepancy with a reviewed target stops composition and returns the exact conflict to Luna.

## Required result

Report baseline and all input/patch hashes; full candidate hashes for all three source files; exact changed hunks and actual input/output line ranges; exact ordered composition method and match counts; no omitted bytes; and whether `U=T` or R126 source equations are affected. The proof handoff identifies the actual constructor → borrow/capture → indexed consumer path and any theorem premise changed by the composed target. Distinguish a proposed source candidate from a compiled implementation and from semantic/proof closure.

No test, build, compiler, Lean, checker, source materialization, cache, environment/storage probe, filesystem patch application, dirty/quarantined source read, Git mutation, staging, commit or push is authorized in this sprint. A successful composition is a research candidate only. R111 requires fresh independent source/storage-gate review and the exact private capped compile invocation before Luna may integrate source.
