# R218 — reconstruct original annotation meaning from source inputs

Status: ACTIVE after primary validation of the sprint-end selector recommendation.
Branch/baseline: `yulang3` at `ef1873b5e9507192bc97fcdcbb1074eaae70f2e4`.
Original parent: `YulangClosure.SourceProblem.InferenceSoundness`
(`notes/theory/lean/YulangClosure/Contracts.lean:128–130`):

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Keep this theorem, all quantifiers, `supported`, original source semantics,
and adopted effect-hygiene policy unchanged. R218 starts at roots 0/4,
packages 0/5, parent delta 0 and effect-hygiene theorem delta 0.

## Outcome and falsifier

Determine whether the original annotation meaning required by the Lambda
`sourceFormalRole` premise is definable from the actual original source inputs.
Construct a concrete source-to-meaning equation and apply it to the unchanged
Lambda source rule, or freeze the exact missing input with its real source
producer and consumer. Do not infer impossibility from `Annotation := Nat`
alone, add an ungrounded signature lookup, narrow the source domain, or treat
the current carrier as semantic authority.

Preserve the distinction between an `Effectful` wrapper on a value and an
effect row under `TypeArrow`; use `([E] int) -> int` as the discriminator.
An equation that maps both to the Function argument-effect port is falsified
by the frozen Oracle builder/constraint-lowering behavior. Success must
construct the required original source premise from the exact source data,
not just restate it as a `Kernel.atom` assumption.

## Authority and exact inputs

- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`
- `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`
- `notes/theory/2026-11-02-source-annotation-elaboration-r217.md`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean`
- `notes/theory/lean/YulangClosure/OriginalSourceRecordBoundary.lean`
- `notes/theory/lean/YulangClosure/StaticAnnotationConstraintInterpretation.lean`
- `notes/theory/lean/YulangClosure/Contracts.lean`
- Current source evidence: `crates/yu-hir/src/module/source_annotation.rs`,
  `crates/yu-solver/src/candidate_effect.rs`.
- Frozen Oracle `main` `a58eefc31e22141574b6f20c6a5748151c6d79f1`:
  `crates/infer/src/annotation/builder.rs` and
  `crates/infer/src/annotation/constraints.rs`.

Freeze direct dependency hashes in the model note and handoff. Rust files are
read-only evidence in this sprint.

## Lanes, exact outputs, and resources

- Primary source/model construction and parent application: Luna, 1,800 seconds.
- Complementary read-only source audit: `/root/r218_original_annotation_source_audit`;
  no writes, build, tests or Git. Runtime model/effort UNKNOWN unless reported.
- Lean construction: one registered `lean_prover` after the exact equation is
  fixed; maximum 600 seconds, one CPU, 1 GiB. Reuse pinned project and existing
  cache; cache creation is authorized for this goal. No dependency updates.
- Implementation lane: `NO_SAFE_CODE_SLICE` pending resolution of row mapping
  and original source inputs. No Rust edits, Cargo or Rust build.
- Independent fresh `compiler_referee` review after the equation/countermodel
  and parent application are frozen; maximum 600 seconds, read-only.
- Exact primary artifact leases:
  `tasks/agent-loop/sprints/original-annotation-reconstruction-r218.md`,
  `notes/theory/2026-11-02-original-annotation-reconstruction-r218.md`,
  `notes/theory/lean/YulangClosure/OriginalAnnotationReconstructionR218.lean`,
  `tasks/agent-loop/inbox/original-annotation-reconstruction-r218.md`,
  `tasks/agent-loop/history/20261102-original-annotation-reconstruction-r218-outcome.md`,
  `tasks/agent-loop/current.json`.

Stop at a source-model equation applied to `sourceFormalRole`, a concrete
source-qualified missing-input result, an uncovered original supported form,
independent review, or the resource bound. Record exact theorem types and
axiom audits for every Lean theorem. No theorem, model definition, static check,
or Rust observer closes the original parent by itself.

## Review and integration seam

Fresh reviewer checks actual original input availability and dataflow,
row-position fidelity against the frozen Oracle, no hidden signature/kernel
assumption, full source-domain quantification, and whether the constructed
evidence removes any premise from the original Lambda induction. A coherent
reviewed checkpoint may be committed and pushed by Luna after explicit-path
staging and outbound-range inspection. Next dispatcher consultation is at the
result/counterexample, a material source-data decision, or a genuine blocker.
