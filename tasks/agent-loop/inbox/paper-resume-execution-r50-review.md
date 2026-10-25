# R50 independent compiler review (r5 frozen snapshot)

Disposition: semantic review CLEAN; minor process-evidence finding remains unresolved. R50 is not accepted for integration.

## Finding: native executable provenance incomplete

Location: primary verification receipt lines 14–23. The recorded commands use bare `lake`/`lean`; call 02 is `lean --version`. The governing `.agents/skills/yulang-lean-proofs/SKILL.md` requires read-only native Lake resolution and `env lean --version` through the resolved Lake executable. The output versions are consistent with Lean 4.35.0, but the receipt does not establish the required executable relationship. No additional checker run was requested or performed during review.

## Finding: wall and monotonic duration differ

Call 03 UTC start/end span 34.257784 s; recorded monotonic duration is 33.185073003 s, a 1.072710997 s difference. A clock adjustment is possible but unproven. Both values remain in their original receipt; no cause is inferred.

## Semantic and audit review

Reviewed the manuscript's resume rule and preservation claim, actual typing/substitution declarations, R49 construction and traces, frozen R50 source and audit, complete primary output, and root delta. Empty-owner response substitution uses the existing substitution relation without assuming freshening. The response type Q remains separate from result type A. Two resumes independently reuse the same immutable saved continuation and operation instance. Prefix preservation uses R49 Trace; erasure embeds the actual reduction relation.

All 18 public theorem names have ordered audit markers, complete printed types and axiom reports; each axiom list is `[propext, Quot.sound]`. Candidate, audit, contract, handoff, worker/primary process outputs and dependency-cone pins match their supplied hashes. The isolated primary root delta is exactly `import YulangClosure.PaperResumeExecution`.

No BLOCKING or major source/proof correctness finding. Remaining parent obligations stay OPEN: nonempty-owner freshening and lifetime, full-state/source/native correspondence, handlers/effects, whole executor, inference A/B, and production promotion.

Review activity: read-only; no Lean/Lake/checker/build/test/Git/network invocation, writes or descendants. Exact active duration UNKNOWN; conservatively charge the full <=180 s review grant.
