# R216 — resolved annotation equations for original source soundness

Status: ACTIVE, bounded model construction. This contract keeps the original
`InferenceSoundness` statement and its source domain unchanged.

Branch/baseline: `yulang3` at `5454bf6f5`; R215's post-checkpoint current-state
edit is part of this admission. R215 model SHA-256:
`c3044d07f4290b019e2a181b032e314501ddc1bc9e37e9d8725cec3898973866`.

## Original outcome and success evidence

Original parent (`Contracts.lean:128–130`):
`∀ s x d a, supported s → generates s x d → solves d a → ∃ e,
sourceJudgment s x e ∧ sameScoped s x e a`.
The assignment and witness must be the same across source scope, all binders,
uses, futures, Call and contextual effects. Accepted annotation hygiene keeps
permission, allowance, actual inflow and residual separate.

R215 leaves roots 0/4 and packages 0/5. R216 targets the exact source-annotation
construction premise: connect the original annotation ID/declaration/scope and
entry to emitted type/effect constraints, their independent denotation, and
the original `Kernel.atom` site `sourceFormalRole` (`OriginalSourceGeneration.lean:135–140`).
Success requires concrete constructor equations and a reviewed same-assignment
application to the original atom. If original syntax or effect laws do not
determine such equations, name the first missing semantic owner/equation and
stop as incomplete; do not invent an arbitrary predicate table, narrow support,
or count a conditional classification theorem as parent progress.

## Fixed lanes

- Model author: Luna, up to 1,800 seconds. Read only pinned source syntax,
  generation, interpretation, Simple-sub syntax, adopted L1, effect hygiene,
  and Source-Generalize authority. Write the model note and this handoff.
- Implementation: `NO_SAFE_CODE_SLICE`; no Rust edits/build. R215 inspected
  two relevant owners and found no mathematical denotation owner in Rust.
- Lean: after equations are fixed, one registered `lean_prover` may implement
  only those exact equations in the separately leased optional module. If the
  model gate fails, no theorem packet is admitted.
- Fresh independent reviewer: up to 600 seconds, read-only, message-only. Review
  exact source fidelity, constructor coverage, denotation independence, effect
  hygiene, and original Kernel application. PASS may admit only the stated
  candidate/checkpoint, not full soundness.

## Authority and dependencies

Use the original `Contracts.InferenceSoundness` claim without changing its
quantifiers or `supported` domain. Reuse `OriginalSourceSyntax.Source`,
`OriginalSourceGeneration.sourceRules`, and the original `Kernel`/`Satisfies`
interfaces; do not replace them with R208's generic grammar or `SourceFormalRole`.
Pin R215, `OriginalSourceSyntax.lean`, `OriginalSourceGeneration.lean`,
`OriginalSourceInterpretation.lean`, `SimpleSubConstraintSyntax.lean`, adopted
L1, annotation-effect hygiene, and Source-Generalize design/proof. Rust source
annotation grammar is implementation evidence only.

The solution assigns only Simple-sub variables/graph data. It cannot choose or
replace a declaration, annotation owner, scope, occurrence, entry, or handler.
Any candidate resolved declaration remains fixed source/signature data. Its
definition is not adopted semantics until it is shown to cover the unchanged
original source grammar and receives independent review.

## Exact write leases and resources

- Author: `notes/theory/2026-11-02-resolved-annotation-equation-r216.md`
- Handoff: `tasks/agent-loop/inbox/resolved-annotation-equation-r216.md`
- Contract and current state: primary only.
- Optional post-equation Lean module:
  `notes/theory/lean/YulangClosure/ResolvedAnnotationEquationR216.lean`
- Existing pinned project cache `.lake/build` is permitted by the user's
  explicit authorization in this conversation; keep it the sole verification
  owner. No new Lean environment, dependency update, Rust build or Cargo.
- Lightweight probes: one CPU, at most 1 GiB and 120 seconds each; Lean build
  at most 1 CPU, 1 GiB and 600 seconds total. One reviewer reserves 600 seconds.

## Stop, application, and checkpoint

Stop at the first source-owner conflict, uncovered original annotation form,
unsound type/effect encoding, decisive countermodel, review, or budget bound.
Report the exact equation, source locator, and first remaining premise. Apply
any proved implication to the unchanged `sourceFormalRole` atom and then to the
original soundness induction; measure parent delta only after that application
is independently reviewed. Keep whole Catch/Lambda, App, principality and
termination claims open unless separately proved. Only Luna integrates and
pushes an exact reviewed coherent checkpoint; unknown leases remain quarantined.
