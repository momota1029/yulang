# R213 fixed inference model — primary handoff

Sprint/contract: R213 / 1 / SHA-256 `3d7a654bb77be30a77911558477fcebb1d17e26842f6c6e3549543d562be49c7`
Baseline: `yulang3` / `7c25f1cce`
Parent gate: unchanged `Contracts.SourceProblem.InferenceSoundness`,
`SourceScopedCoverage`, `PrincipalCoverage`, and `InferenceTermination`
(`Contracts.lean:128–154`).
Primary model author: `/root`; requested Luna/high, observed model/effort
UNKNOWN.
Source-rule evidence: `/root/r213_source_rule_map`, read-only explorer;
runtime/model metadata UNKNOWN.
Exact primary outputs: `notes/theory/2026-11-02-fixed-inference-model-r213.md`
and this handoff. No Lean module is leased in R213.

## Fixed target

Soundness remains the original same-assignment statement:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

The same `s`, `x`, `d`, and satisfying `a` must be used through the source
derivation and scope/witness readout. Do not assume an accepted run in this
theorem. A separately proved endogenous solver result may later supply
`solves d a`; it is not part of the theorem's quantifier structure.

## Frozen interpretation

The source syntax and generated original rule-tree are fixed inputs. The full
Simple-sub algebra retains distinct Value/Effect kinds, Union/Intersection,
all four Function ports, metadata, and recursive regular-graph comparisons.
The original `Build`/`Satisfies`/`reconstruction` bridge is reusable only after
independent generated-constraint satisfaction yields each actual local source
premise under the same source scope and assignment.

The R213 model file records the constructor inventory, equation status, root
composition, and the gap between source meaning, independent generation,
regular solutions, and actual solver transitions. It intentionally does not
introduce a new source equation or a record of assumed `Kernel` laws.

The read-only source map checked every expression, pattern, statement,
container, operation arm, and client constructor in the pinned
`OriginalSourceGeneration` equations. It confirmed that App's two recursive
operand derivations do not supply the complete Call phase law; contextual
effects have no generic row equation in `Source`/`sourceRules`; and
`RuleTree.choice` existing in syntax does not establish generated alternatives.
The exact source equation owner remains the primary abstract model.

App has five base atoms and a sixth conditional
`roleAndInitialCallOrigin` atom when `singletonFormalCall context callee
argument` is true. This branch remains under the same `viewLogic` witness and
same App coordinates. Its condition is the unannotated single-use Value formal
callee plus Value formal Name argument; the independent interpretation remains
OPEN. R159 contains a nonvacuous source fixture for this branch.

Known adopted boundaries:

- Literal L1 source meaning is authoritative for every raw payload, intrinsic
  value/type and pure Return at the original occurrence/root/event/scope/shared
  witness. Its independent Simple-sub generation/readout remains OPEN; keep
  written-target and synthesis endpoints distinct for annotations.
- Structural Union remains in the abstract core and both conditional branches
  contribute. The pending typed-Union question is only the dependent selected
  branch/result telescope transport for Call/incidence; it remains untouched.
- Complete Call and contextual effects remain in scope wherever the original
  rules place them. They may not be erased by a structural Function comparison
  or filled from Rust-only identifiers.

## Parent-premise accounting

R212's endogenous readout and run gate are separate from solution-indexed
source soundness. This corrects a potential dependency mistake: requiring the
full `CoreRun` theorem before proving the direct implication from independent
`solves d a` would unnecessarily block source soundness. Conversely, the
existing symbolic `Build` theorem and structural Store results do not discharge
any source root.

R213 outcome is `MODEL-INCOMPLETE`: the concrete all-source independent
generator, source-independent regular `solves`, same-assignment source-scope
readout, and complete Call/effect compatibility equations are not fixed by the
current definitions. The original source `Kernel` still supplies local
meanings, and no existing concrete `SourceProblem` instance binds those to the
Simple-sub constraints. The model author has not started a theorem under these
missing assumptions.

The first bounded source construction is the all-payload literal generation
and readout equation consuming the adopted L1 rule, preserving the same
`(q,r,e₀,ξ,ω)` and keeping annotated `synthesis` distinct from
`writtenTarget`. This is not a request to re-adopt L1. The whole model must
still connect every other independent atom/check and effect/Call obligation to
that same assignment.

Parent delta remains **0/4 roots; 0/5 packages**. Principality's original
instance/factorization order and complete inference accessibility remain
separate open obligations.

## Exact next action and stop boundary

Obtain fresh read-only review of the frozen model for source-authority fidelity,
independence/noncircularity, full constructor scope, and the exact first
missing equation. If review agrees the model is incomplete, keep the parent
roots open and use the next dispatch to select one missing equation whose
authority already exists and whose definition can be constructed without
changing source semantics. If a source decision is required, stop at that
equation and use the existing approval process. Do not dispatch a theorem
worker until the reviewed model fixes every premise of its original scope.

No Lean, Lake, checker, build, test, Rust, Cargo, cache, scratch, worktree, or
question-board mutation occurred in R213. The source-map explorer is read-only.

Independent review initially found one major documentary omission: the
conditional sixth App atom. The model and contract now include the exact branch
and pin `SourceAppAdmissionR159.lean`. The fresh delta review passed the repair,
found no additional documentary correctness finding, and matched all revised
target hashes and enumerated source pins. The review accepts preservation of
the explicitly incomplete checkpoint only; model gate remains
`MODEL-INCOMPLETE`, with **0/4 roots; 0/5 packages** and no theorem or parent
premise discharged. Review was read-only; no builds, tests, Lean, checker,
scratch, or cache generation. The model SHA-256 remains
`17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e`.
