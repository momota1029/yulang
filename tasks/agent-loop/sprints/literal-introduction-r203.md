# R203 — All-payload static literal introduction

Status: ACTIVE
Budget: 600 seconds primary construction; one fresh 300-second specification review.

## Goal

Add an explicit all-payload literal introduction clause to the existing abstract inference model candidate, using the original raw literal constructors and the already formalized paper value/type rule. This is the first concrete static source-typing rule under the user's standing authority to select natural definitions for Lean soundness.

Do not narrow the source domain or claim that literal base typing exhausts every original checking/declaration alternative. Do not replace the selected Source-Generalize relation, identify the static clause with runtime `LiteralDeclaration`, or claim a parent premise is discharged.

## Frozen inputs

- User-approved source-directed inference principles, `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Existing model candidate, `notes/theory/2026-11-01-abstract-inference-model-r199.md`, SHA-256 `f60b89d98ced17cabf860c6dd65aa3929796c85a407c8f82af25607adf0017cb`.
- Raw source literals, `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`, SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- Paper value/type syntax, `notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean`, SHA-256 `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d`.
- Original core base/literal syntax, `notes/theory/lean/YulangClosure/CoreSyntax.lean`, SHA-256 `c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375`.
- Selected Source-Generalize construction, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.

## Required deliverable

Write one model addendum defining a payload-preserving map from all eight `OriginalSource.Literal` forms to `PaperTypes.Literal`, and the static introduction clause:

```text
sourceLiteralType(l) := PaperTypes.literalType(toPaperLiteral(l))
sourceLiteralValue(l) := PaperTypes.Value.literal(toPaperLiteral(l))
PaperValueTyped.literal : sourceLiteralValue(l) : sourceLiteralType(l)
```

Spell out every constructor and resulting base type. State that the local introduction contributes no immediate performed operation; do not use that fact to erase contextual Call/effect permissions, inflow, residuals or scoped obligations. Retain the whole original payload without machine-width conversion or new validation restrictions.

Distinguish this concrete static rule from: (a) all other legal checking/declaration alternatives; (b) the selected SG §3.1 complete literal local relation and its Return/effect/world/event laws; (c) the Simple-sub generator/solver reflection theorem; and (d) later runtime realization. Name the exact remaining bridge from satisfying literal constraints to the original same-occurrence/same-scope source judgment. Keep all other constructors and all parent roots open.

## Review and stop boundary

One fresh `spec_auditor` must independently check constructor/payload fidelity, type mapping, compatibility with the approved `if` example and paper typing rule, scope of the purity claim, and all non-adoption/open-bridge statements. Stop on any claim that changes payload validity, changes observable effects, makes the base rule exhaustive, or conflicts with selected source authority. No Rust reads/edits, Lean/Lake/build/test execution, environment/cache/target/worktree/scratch creation, pending-question access, or quarantine access. Parent delta stays zero unless a theorem is actually applied to an unchanged parent premise.
