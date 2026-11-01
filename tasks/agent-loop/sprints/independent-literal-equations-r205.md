# R205 — independent literal generator and denotation equations

Status: ACTIVE under the user's standing Yulang inference goal and R204 end-dispatch selection.
Branch / baseline commit: `yulang3` / `b589333d2`.
Authority: user's fixed-source Simple-sub plan; approved top-level inference principles; selected Source-Generalize §§2–3 and L1/L2. No semantic adoption authority is inferred.

## Parent target and success evidence

Unchanged parent: `YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128–130`) with its original quantifiers and one `sameScoped` witness. Current parent delta is `0/4 roots; 0/5 packages`. This packet constructs only the literal generator syntax and its independent denotation, a prerequisite to proving the literal case; it does not count as parent progress unless an original premise is actually discharged.

Sequentially revise only `notes/theory/2026-11-01-abstract-inference-model-r199.md`. Define concrete equations for the original literal case, with an independently meaningful fixed signature `Σ`:

```text
GenerateLiteralΣ(scope, occurrence, payload)
InterpretLiteralConstraintΣ(constraint, assignment)
ReadLiteralΣ(scope, occurrence, assignment)
```

The equations must state actual Simple-sub constraint syntax and solution denotation. Preserve payload, declared interface, original occurrence/scope, contextual-effect obligations, event/world and the same witness coordinates. The denotation may use independently specified declaration/domain laws also consumed by source typing; it must not assume `sourceJudgment`, the desired SG conclusion, a reflection theorem, or an opaque successful-check predicate. Do not substitute symbolic `Build` for actual generation/readout.

Success requires equations whose unfolding provides a specific original L1/L2 premise without assuming the desired source conclusion. Merely restating the target implication, listing fields, or assuming an L1/L2 certificate is not success. If the already selected authorities do not fix an independent literal primitive interpretation, stop at the exact missing definition and state alternatives and semantic consequences for review; do not adopt one.

## Frozen inputs and boundaries

Use R204 model candidate SHA-256 `9473d0c2d09fa5fbae15a64ab8d00cea12d160fd57bda01ab6fb39494b2de1a8`; selected SG construction SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; unchanged `Contracts.lean` SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`. Preserve R204 and its review history.

No Rust reads or edits, Lean/Lake/build/test execution, new theorem wrappers, new files/storage, environment/cache/target/scratch/worktree creation, or quarantined/pending-question access. Primary construction only until substantive equations exist; then one fresh read-only independent review of the exact final candidate. Any change to accepted typings, payload validity, effects, alternatives or scope requires user approval before adoption.

Budget: primary construction up to 900 seconds; one review up to 300 seconds. At the end, report exactly which original parent premise changed, if any. Do not count theorem/lemma totals as progress.
