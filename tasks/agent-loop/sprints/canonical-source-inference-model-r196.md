# Sprint R196 — canonical source-level inference model

Status: ACTIVE; exact leases granted in `tasks/agent-loop/history/canonical-source-inference-model-r196-activation.md`.
Branch / baseline: `yulang3` / `84f0ff11e`;
Contract revision: 1.
Authority: current user direction; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5; `notes/theory/2026-11-01-parent-backward-inference-plan.md`.

## Original outcome and success evidence

Parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`, with its unchanged quantifiers, original source domain, exact scope, one shared source witness, and same assignment. The other three roots remain independent.

Construct the canonical mathematical source/inference model from original source syntax and accepted algorithm operations, then try to derive the parent implication from generated constraints and their solution. A complete reviewed model removes package 1 of 5; only a reviewed proof applied to the original implication can reduce root 1. Before: 5/5 dependency packages open, 0/4 roots closed. After: report the same counts unless evidence satisfies those predicates.

Keep source payload domains directly. Do not require `CoreSyntax`, convert/truncate payloads, change supported syntax, define `solves` by restating the target, or assume the missing source judgment/admission/readout as a hypothesis. Preserve Call and contextual effects, both value/effect rows, all four Function ports, generalization boundaries, and the original shared witness.

The typed-Union question at `questions/2026-11-02-original-typed-union-rule/question.md` is pending. Do not invent or adopt its missing selected-branch/result equations. If it is a necessary input, stop at that exact owner and leave the source case and parent open; continue only with independent constructions that preserve the full domain.

## Proof lane and review

Owner: registered `lean_prover`, leaf assignment, 2400 seconds maximum. Build one complete source-level interpretation and apply it to `InferenceSoundness`; a partial conditional model is not success. If the theorem cannot proceed, freeze an exact first missing original equation and its authority/owner, with the package/root delta still zero.

One fresh independent `compiler_referee` or `spec_auditor` reviews the frozen source/model correspondence and confirms that no constructor, Call/effect obligation, shared scope, or supported source case was weakened. The author cannot review their own result. The primary applies the result to the parent and updates counts.

No Rust implementation lane in this sprint: the user has directed mathematical correctness before Rust simulation. Do not inspect Rust owners to fill missing equations.

## Exact leases, pins, and resources

Proposed exclusive outputs, subject to primary activation:

- `notes/theory/lean/YulangClosure/CanonicalSourceInferenceModelR196.lean`
- `tasks/agent-loop/inbox/canonical-source-inference-model-r196.md`

Frozen inputs and SHA-256:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `OriginalSourceSyntax.lean`: `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `OriginalSourceInterpretation.lean`: `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `OriginalSourceChecking.lean`: `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `SimpleSubLatticeInference.lean`: `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- `SimpleSubGeneralizationSoundness.lean`: `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246`
- `InferenceConstruction.lean`: `576d69266da62c0f75fa9748ff0f0691a9f0bc3aca5148be9d25cef82d2010f0`
- `CoreSyntax.lean` reference only (not a required dependency): `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375`.

One verifier owns the existing pinned Lean 4.35.0 project cache; at most two targeted checks of the assigned module and each delivered theorem, with full type and axiom audit. Do not create environments, caches, targets, scratch trees, or broad builds/tests. Stop if required dependencies are missing rather than expanding resources.

## Stop and integration conditions

Stop for a missing authoritative source equation, the pending Union boundary, a counterexample, changed input hash, output collision, unknown lease conflict, or budget exhaustion. Do not close a root based on a definition, conditional theorem, or local structural result.

On completion, Luna records the before/after package and root counts, exact theorem types/axioms, omitted cases, independent review, and downstream open premises. Commit and push only the reviewed intended paths; exclude pending question directories and all unrelated dirty/quarantined files.
