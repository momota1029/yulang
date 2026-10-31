/-!
NATIVE-FRESH-USE-VALIDATION/r2: theorem construction NOT_STARTED.

Contract SHA-256:
9764890e7d430cefa9765ead51d5496b7078cf077c0937f5555617b3f685a0f2.

NO_SAFE_CODE_SLICE for the complete authenticated FreshUse recipe under the
admitted interfaces. In pinned candidate_context.rs, State.weights and
State.contexts are private (lines 948 and 950); fold_context is private
(line 1739). CircuitEvidence.contexts/weights (1090/1094) expose only the
relation-selected closure built by retained_input (1167--1316), whose result
is explicitly Incomplete. No complete readback of every detached output in
FreshUse.context_remap is established. rename_fresh_contexts (1684) is a
mutating constructor; its success is not an independent output-readback
equation. The exact recipe must return to the native Context owner.

Contribution.instance and View.source_weight/closed_weight/tail are accessible
at their pinned owners; they are not classified as opaque here. Their full
recipe and exact map domains have not been constructed. No theorem, assumed
root image, alternative source language, or parent-closure claim is supplied.

The returned-root site remains candidate_scheme.rs:4277--4278. Its authentic
independent FreshUse recipe is still missing. Original
YulangClosure.SourceProblem.InferenceSoundness and the whole effect-hygiene
obligation remain open with the original source scopes and shared witnesses.

Execution and cache ownership belong to the primary. This comment-only file
has not been checked by Lean. See the assignment's sole handoff:
tasks/agent-loop/inbox/native-fresh-use-validation-r2-proof.md.
-/
