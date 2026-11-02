# R208 — reflect selected annotation hygiene into the original Lambda rule

Status: **CLOSED_INCOMPLETE / superseded by the user's root-first replan**.
Branch / baseline commit: `yulang3` / `4ff4f75ef`.
Parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`; preserve original syntax, support, scope, one solution and one shared witness.
Authority: user-approved Simple-sub top-level principles and annotation effect hygiene policy §§1–1.2. No accepted source behavior is narrowed or changed.

## Objective

Construct one concrete, noncircular resolved-annotation interpretation and connect its generated constraint evidence to the original source `sourceFormalRole` / Catch hygiene obligations at the same annotation ID, owner, position/path, scope, operation identity and assignment witness. Consume the reflection in the original Lambda/Catch soundness construction; a traversal theorem or residual-only algebra by itself is not a parent result.

Use `notes/theory/lean/YulangClosure/StaticAnnotationConstraintInterpretation.lean` as the sole new Lean model output and `tasks/agent-loop/inbox/static-annotation-hygiene-r208.md` as the frozen handoff. Preserve the exact annotation tree, resolved effect identities and type arguments, nested Function polarity, symbolic dependencies, row positions, owner/scope and original event. Permission, allowance, actual inflow, handler subtraction and residual are distinct relations. Permission alone never creates inflow or performs subtraction. Reuse existing hygiene results only with their actual hypotheses.

The generated clause and original source rule must read one independently defined resolved annotation algebra. Do not define solving as source typing, use a desired source judgment/admission predicate as a constraint premise, infer source facts from successful native guards, or move obligations into `LocalLaws`. Preserve both Value and retained Computation entries and all original alternatives.

## Success gate and falsifiers

Success requires a kernel-checked theorem that generated annotation evidence yields the exact original Lambda/Catch hygiene premise and is applied at its source-generation/soundness induction site. Print theorem types and complete axiom audits. Fresh independent review is required before parent-premise accounting changes.

Falsify the candidate if any of these occur: `[signal, write]` is rejected at a contravariant `[signal]` position; `write` is removed by the annotation; empty inflow acquires an effect; a covariant allowance creates flow; equal row images merge sibling permissions; a type variable loses its symbolic connection; a different owner/path/scope/event is used; or a second witness is introduced.

The original parent count changes only when the theorem is consumed under the unchanged `InferenceSoundness` quantifiers. If no actual source rule/generator equation can be constructed, record the exact source owner and missing relation without claiming progress. Do not reopen literal mappings or declare any of the four roots closed in this packet.

## Inputs and staged lanes

- Annotation policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`, SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- Original source syntax: `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- Original source generation: `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean`, SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- Original parent: `notes/theory/lean/YulangClosure/Contracts.lean`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Existing residual/hygiene results: `EffectPermissionResidualR38.lean`, SHA-256 `e5657e0b8affaaa0ffef6543c8e329957a1519a04a194392dbd245064a623642`; `OriginalSourceInterpretation.lean`, SHA-256 `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- R197 stop: `SourceFormalEntryPermissionR197.lean`; R199 §§2.3–4.3 records the selected policy and open equations.

Primary Luna first constructs/freezes the independent model equations. After that freeze, one registered `lean_prover` gets a disjoint proof-module lease and proves the exact reflection/application. One fresh eligible reviewer audits the frozen model/proof and parent application. Luna alone adjudicates and integrates.

## Budget and boundaries

Primary modeling: at most 600 seconds. Proof assignment: at most 1200 seconds. Independent review: at most 300 seconds. Astra: 0. Reuse pinned Lean 4.35.0 and the existing project cache only; no new environment, cache, target, scratch tree or worktree. At most two bounded Lean checks, one verification owner. No Rust changes in this proof-first packet; read-only clean Rust source inspection is allowed only to authenticate a direct crosswalk. Do not touch dirty or quarantined paths or pending question bundles.

The next material boundary is the frozen model equations, a source-equation blocker, or a reviewed theorem applied to the original parent. Semantic changes require the normal authority/review/approval gate.

## Closure disposition

The annotation model was not frozen, compiled, reviewed or applied to the
original `InferenceSoundness` derivation. R208 establishes no theorem and no
parent-premise reduction. Its module remains only as an unverified local
candidate; it is not leased, staged or part of the R209 model. Revisit this
annotation path only after the whole abstract source/constraint model is fixed.
