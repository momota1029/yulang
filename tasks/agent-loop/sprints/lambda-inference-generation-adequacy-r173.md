# Sprint R173 — Lambda inference-generation adequacy

Status: ADMITTED under the unchanged user goal: prove Yulang type and inferred effect-row soundness against the original source typing rules. Runtime/machine correctness is excluded.
Branch / baseline: `yulang3` / `a80f58d4f`.
Contract revision: 1. Primary: Luna. Source dependencies are pinned below.

## Original outcome and success evidence

Parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:127–130`, unchanged:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Keep all original source forms, scope, quantifiers, accepted semantics and the single shared witness. Do not equate `p.generates` with `Build`, or `p.solves` with `Satisfies`, by definition or stipulation.

R172 independently reviewed the Lambda source-rule map and located the decisive missing bridge: concrete `generates`/`solves` do not yet yield the independent `Kernel`/`Satisfies (Build ...)` inputs needed by `OriginalSource.generated_constraints_imply_source_judgment`; that theorem also does not build the parent `sameScoped` witness. R171’s prepared-formal origin application remains separately blocked by `entry = none` versus required `some port` and missing record-field recipe events.

Success is either (a) a constructive Lambda generation/solution implication derived from the actual approved inference construction and original Lambda rule, with no invented semantic premises and an explicit application toward the parent shared witness; or (b) a precise `BLOCKED_ORIGINAL_INTERPRETATION` result naming the first missing independent semantic registration, its owning definition, and the exact constructor equation needed. A conditional origin lemma alone is not success. Preserve genuine subsource induction hypotheses; they cannot supply the Lambda’s own admission, annotation, effect-flow, Shared or body obligations.

## Proof lane

Owner: registered `lean_prover`, bounded 900 seconds. Read only the pinned theorem/meaning files and R172 frozen outputs. Locate authoritative meanings of generated constraints, solutions, source judgment and shared witness. Inspect the actual Lambda inference generation/solution path and test whether its emitted constraints derive the original Lambda premises in description → invocation → receipt → Shared → body order, covering both entry modes and annotation boundaries. Apply any obtained implication to the unchanged parent; explicitly retain all remaining premises.

May write only:
- `notes/theory/lean/YulangClosure/LambdaInferenceGenerationAdequacyR173.lean` (only if a constructive result is available)
- `tasks/agent-loop/inbox/lambda-inference-generation-adequacy-r173-proof.md`

At most two pinned Lean 4.35.0 checks using existing dependencies; no new environment/cache/build/Cargo/test/scratch. If dependencies are absent, stop with the exact missing input.

## Rust inference/source lane

Owner: registered read-only `researcher`, 600 seconds. Inspect only `lib.rs` and `candidate_source.rs` at the pinned hashes plus R172 handoff. Trace one exact registration and Lambda parameter through session construction/preparation (`lib.rs` session construction and `initialize_candidate_source_levels`), `FormalEntry` dispatch, and `admit_lambda_fact`; record the constraint/effect endpoints and source annotation/body identities consumed. The goal is exact equations for the proof lane, not evaluator/runtime correctness. No code edits; report `NO_SAFE_CODE_SLICE` absent a demonstrated reachable defect under approved semantics.

May write only `tasks/agent-loop/inbox/lambda-inference-generation-adequacy-r173-source.md`.

## Inputs and frozen hashes

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `InferenceConstruction.lean`: `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0`
- `OriginalProofProgress.lean`: `21e361962538d5e2738041b58186682a4a9fb3ad10c75f4c39dc97e32a443f39`
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- R172 theory note: `3558480ed78086ad7471b96a6e41aa88db3b7b8a6d8b54e092fae7b6dce26ef9`
- R172 proof handoff: `388b20cfa8698c5e6a71b31661fbbc428a72bb2c1c720562a225da439ec7b37c`
- R172 source handoff: `568a16bc3ca177e57ba0915c4b9dc96cf6c9aa6c364df0c31d57e61333e20a9e`

All hashes must match before work. Runtime subtree, quarantined paths, and unrelated dirty/untracked artifacts are excluded.

## Review, stop and integration

After both writers stop, Luna freezes outputs and assigns a fresh independent reviewer (300 seconds) for the proof/source seam. Acceptance requires exact theorem types/axiom audits if Lean ran, source mapping at pinned hashes, no overclaim of parent closure, and an owner for the first remaining parent premise. A reviewer cannot be a producer/coauthor.

Stop on a changed dependency, missing semantic authority, reachable counterexample, requirement to alter semantics/source domain, exhausted checks/budget, or need for new leases/resources. No production authority is granted. R171 application and all non-Lambda parent obligations remain open unless directly proved here. Only Luna stages/commits/pushes the reviewed exact output set; unknown/quarantined owners remain untouched.
