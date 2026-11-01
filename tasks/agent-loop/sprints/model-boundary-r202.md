# R202 — Static model boundary audit

Status: ACTIVE
Budget: 1,200 seconds construction; one fresh 300-second independent review.

## Goal

Work backward from the unchanged `InferenceSoundness` and `sameScoped` roots to determine whether Yulang type-inference soundness can be stated and proved against an independent declarative static type/effect judgment, without requiring Rust runtime `Inputs` as the first meaning of source typing.

This is a method/model-boundary audit. It does not change source semantics, select new primitive meanings, narrow syntax, or close a theorem. Parent delta stays zero until an independently reviewed derivation discharges an unchanged parent premise.

## Frozen authorities

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `notes/design/2026-10-08-source-generalize-definition.md`, SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- `notes/theory/lean/YulangClosure/Contracts.lean`, unchanged root, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Current R201 outcome, SHA-256 `7f0e93f174a26b6470cf39a283f5d9a7eb8548040fb5e0db0fb157844755bddd`.

## Required deliverable

Return one bounded, read-only report that:

1. Defines a candidate declarative judgment such as `Γ; Ξ ⊢ s : τ ! ε ▷ W`, with interfaces, scoped obligations, and the one shared witness. Its rules must not mention solver success or generated constraints.
2. Gives concrete Literal, branch-join, Lambda, and App rules. Retain both branches in the approved `if true {1} else {"str"}` example (`int | str`), and retain all four Function ports and effect polarity for formal-use constraints.
3. Accounts for all 13 expression, 11 pattern, and 3 statement forms, distinguishing specified rules from exact unresolved equations. Preserve annotation identity, both entry modes, full Call, contextual effects, recursive publication, and correlated uses/futures.
4. Derives correspondence to the selected original source judgment and its `sameScoped` package, or identifies the exact selected clause that prevents correspondence. It may not silently replace `sourceJudgment` or claim that runtime obligations are unnecessary without this derivation.
5. Lists the exact unchanged parent premises this model would discharge, and explicit falsifiers: dropped branch, missing Function port, permission/inflow conflation, omitted Call challenge, split witness, or unsupported source correspondence.

## Inputs and limits

Use only the frozen design/theory sources named above and the exact source-form inventory/parent definitions needed for this audit. Do not read Rust implementation, quarantined paths, pending question bundles, or unrelated histories. Do not run Lean, Lake, Cargo, builds, tests, or benchmarks. Do not create environments, targets, caches, worktrees, scratch artifacts, or additional files. The output is a message only.

## Stop and acceptance

Stop if exact selected-source correspondence cannot be established from approved authority. Report the precise missing clause/equation and leave all original roots open. A plausible new judgment or a list of local rules alone is not accepted. Independent review must verify scope preservation, source correspondence, and falsifier coverage before any future semantic adoption or parent-premise delta.
