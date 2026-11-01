# R209 — instantiate the abstract source inference model

Status: **BLOCKED_AT_SOURCE_SPECIFICATION / MODEL-INCOMPLETE**

Parent roots: `Contracts.lean:128–154`; baseline branch `yulang3`, commit
`4ff4f75ef`.

## Outcome

Create one concrete, typechecked Lean model for the original source-level
Simple-sub algorithm, then instantiate the unchanged `SourceProblem` root
predicates over it. This packet is model construction; it does not claim
soundness, principality, termination, or parent-premise closure.

The model must define, independently and concretely:

1. The original source typing rules and primitive/declaration interpretations.
2. Generated constraints and their satisfaction, without defining satisfaction
   as source typing, source admission, reconstruction, or the desired theorem.
3. Actual generation, accumulation, propagation, level-aware extrusion,
   birth-qualified intrusion, and generalization states/transitions.
4. The complete assignment, source scope, and shared witness relation consumed
   by `sameScoped`.
5. The original principal predicate and `instanceOf` relation, separately from
   proofs about them.
6. Actual initial-state and `inferStep` relations for the termination root.

Preserve the full source domain, all constructors, both entry modes, four-port
Functions, unions/intersections, annotations, symbolic effects and shared
dependencies. Include Call/contextual-effect equations wherever required by the
original abstract rules. Defer only the genuine Rust/native simulation and
readout bridge. Do not specify the mathematics from private candidate Rust.

## Acceptance gate

The sole Lean output is
`notes/theory/lean/YulangClosure/AbstractSourceInferenceModel.lean`; handoff is
`tasks/agent-loop/inbox/abstract-source-inference-model-r209.md`.

Require pinned Lean 4.35.0 typechecking and fresh independent review of the
frozen definitions and unfolded root statements. Reject `sorry`, arbitrary
success predicates, renamed `Build`/`Satisfies`, omitted transitions, narrowed
support, or fields assuming any root theorem. A constructor inventory or a
parameterized list of missing laws is not a completed model. If a source rule
is not determined by existing authority, preserve the constructor and report
the exact missing equation and its owner; do not invent semantics.

## Subsequent root order and accounting

After model review, apply generated-constraint/phase results directly to the
original `InferenceSoundness` derivation. Then prove `PrincipalCoverage` and
`InferenceTermination` as separate obligations; use a reviewed
principal-to-`SourceScopedCoverage` corollary only for the same concrete model.
Close Call/contextual source obligations at their genuine cuts, without
narrowing the roots. Prove Rust simulation/readout last.

Report the exact root premise, consumed reviewed theorem, application site, and
remaining goal. Model completion, theorem count, local lemma count, and
implementation progress alone never change the 0/4 root count.

## Resource and boundary

One primary model-construction lane, at most 3600 seconds; one fresh independent
review, at most 600 seconds; at most two bounded checks using the pinned Lean
project and existing cache only. No new environment, cache, target, scratch
tree, worktree, Cargo run, Rust edits, pending-question edits, or writes to
quarantined paths. Freeze exact dependency hashes before the first Lean check.

## R209 audit disposition

The bounded inventory covered these modules and declarations: `OriginalSourceSyntax`
(source constructors and `RuleTree`), `OriginalSourceGeneration` (`Kernel`,
`SourceJudgment`, `Build`, `Satisfies`), `OriginalSourceInterpretation`
(`LiteralDeclaration` / `LiteralAtom`), `SimpleSubConstraintSyntax` (`Term`,
`Sub`, `Constraint.Satisfied`), `SimpleSubConstraintSoundness` (`State`,
`Step`, `History`), `SimpleSubGrowingInference`,
`SimpleSubLatticeGrowingInference`, `SimpleSubGeneralizationSoundness`,
`OriginalPrincipality`, and `OriginalInferenceTermination`. This is a targeted
inventory of modules directly needed by the R209 roots, not a claim that every
Lean file in the repository was inspected.

The read-only inventory found concrete raw source syntax, symbolic `Build`,
structural Simple-sub terms/subtyping, conditional store-preservation steps,
generalization fragments, scoped-environment machinery, and partial
principality/termination results. These do not instantiate one independent
source/type/effect semantics together with one endogenous inference transition
system. R209 stops before creating a replacement parameterized model or running
Lean.

The exact source specification blockers are:

1. Original SG L1: literal declaration/local typing at the same
   source/root/event/scope, plus its Return and contextual-effect law. `Build`
   retains a symbolic `literalDeclaration` atom; `Kernel` still supplies its
   meaning. The base `PaperTypes` table alone is not this rule.
2. Typed Union: the selected-branch-to-result relation and dependent governed
   field transports, retaining both branch schemas, the original result
   telescope and shared coordinates. The existing user question is
   `questions/2026-11-02-original-typed-union-rule/question.md`, revision `q1`.

The first whole-model equation needed beyond these source rules is an
independently defined generator/solver relation such that solving generated
constraints constructively yields every original local premise at the same
source scope, endpoint, world and shared witness. The actual
generation-through-generalization transition relation must also be endogenous;
arbitrary `ConstraintStep` histories with supplied references, births and copy
names do not instantiate `inferInitial`/`inferStep`.

R209 established no theorem and removed no parent premise. Keep **0/4 roots;
0/5 packages**. Resume this same whole-model packet when the source rules are
authenticated or the authorized design process supplies reviewed equations.
Do not start another local constructor packet meanwhile.
