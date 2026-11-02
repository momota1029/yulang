# R238 source annotation constraint model — primary handoff

Sprint/contract: R238, revision 1  
Contract SHA-256: `437b2052b98a45136f0f323b3272605ff2fd746693ec02768d68c7454e305c7d`  
Assignment: Luna primary, source/model construction gate  
Baseline: `yulang3/ee5977573c045088d9f5f12883393e522fec4a96`  
Parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`  
Outcome class: blocked definition construction; no theorem or parent premise reduced.

## Exact source-to-consumer chain inspected

`OriginalSourceGeneration.sourceRules` constructs a Lambda `entryPremises`
list containing the exact atom
`.atom { (atom .sourceFormalRole formal.site formalContext) with
  annotation := formal.annotation, entry := some formal.entry }`.
That list is included in the Lambda `node .lambda`'s local rule tree. `Build`
compiles that tree, and `Satisfies` maps a local atom to
`OriginalSource.Local.atom`, which requires `kernel.atom environment value`.
`SourceJudgment` is the corresponding original `Judgment` over the same tree.

The root `SourceProblem.InferenceSoundness` is only a generic contract over an
arbitrary `SourceProblem`; it does not select that `Kernel`, generated
constraint language, or solving relation. `InferenceConstruction.lean` and
`OriginalProofProgress.lean` explicitly say that their imports do not construct
a complete source problem. A bounded search found the only concrete
`SourceProblem` record literal in `OriginalPrincipalityResolution.lean`, a
deliberate Unit/Bool countermodel, not the Yulang source instance.

## Why the annotation bridge cannot yet be defined authoritatively

1. `SourceAnnotationElaborationR217.Declaration` gives an immutable candidate
   declaration table and owner/scope resolution from the raw annotation ID.
   Its `AnnotationType.EffectRow` retains only `EffectId` and symbolic IDs; it
   does not represent type arguments on effect instances. The adopted hygiene
   policy requires resolved concrete effect identity, including type arguments.
   No inspected authority gives an equation embedding these `EffectId` values
   into `StaticAnnotationConstraintInterpretation.EffectInstance`.
2. R217 is explicitly a candidate representation. It does not give a reviewed
   source equation for every row's location or for translation into R208's
   `Annotation` tree and declaration-derived variances. R218 separately
   falsifies collapsing a value `Effectful` wrapper row into a Function arrow
   row; its two external readouts are not original resolution authority.
3. R208's `AnnotationEnvironment` is an arbitrary
   `Nat → Option ResolvedAnnotation`. Its generated clause takes a
   `FormalUse` with annotation/owner/scope/event/witness coordinates, and its
   `Solves` assumes the same environment returns the stored resolved object.
   Nothing connects that environment to R217's original declaration table,
   derives the event and shared witness from `OriginalSource.Environment`, or
   proves that clause satisfaction under the parent's assignment `a` yields
   the exact `sourceFormalRole` atom.
4. Although the Lambda rule tree and atom are concrete, the generic parent has
   no Yulang `SourceProblem` instance in which a kernel interpretation consumes
   this atom. Thus an isolated reflection theorem would not apply to the
   unchanged soundness root.

R169's `successful_nonempty` and `selected_endpoint_application`, R41's
`entry_to_exact_use`, and R38's finite residual laws remain reusable after an
authentic source producer, assignment, arrival and exact original consumer
exist. They do not supply these missing equations. No conditional theorem was
added to restate them.

## Before/after and next discriminating evidence

- Before: R217 has candidate raw declaration resolution; R208 has a separate
  resolved-tree profile model; the original Lambda generator has a
  `sourceFormalRole` atom; no independently generated annotation clause is
  connected to that exact atom under one parent assignment.
- After: same. No source/model definition was justified without choosing
  unapproved identity, row-location or environment-to-witness equations.
- Parent-premise delta: **0**. Soundness, principality, termination and
  production status remain open.
- Rust lane: **NO_SAFE_CODE_SLICE**. Existing clean
  `candidate_source.rs` already retains source annotations, and
  `candidate_effect.rs` already publishes/authenticates permission records.
  The receiver has existing indexed-permission checks. The two changed runtime
  files remain UNKNOWN/quarantined and were not read or modified.
- Cache/build/test use: no Lean/Lake invocation, tests, or cache growth. The
  user authorized existing-cache generation, but this model gate did not
  reach a checkable declaration. No new environment, worktree, cache path,
  target, or scratch path was created.

First missing source equation for any theorem packet:

```text
resolved original annotation declaration at the actual formal and scope
  ↔ typed resolved annotation tree with exact effect-instance identities,
    wrapper/arrow row ownership and declaration variance
  → independently generated clause denotation under parent assignment a
  → original sourceFormalRole atom in the same Environment and shared witness
  → a concrete Yulang SourceProblem Lambda consumer.
```

Do not activate a prover until that chain is defined and the last arrow is
typeable. Next dispatch should compare this blocker with the user's broader
parent-first plan and select a source/model construction that can instantiate
the unchanged parent, not another local permission or residual lemma.

## Verification, review and write status

Primary inspection reauthenticated the contract's listed frozen hashes at
admission. This handoff is a gate record, not a checked Lean result. A fresh
`spec_auditor` returned **BLOCKED for the full chain; definitions-only model
feasible; parent-premise delta zero**.

Independent reviewer findings:

- **BLOCKING — declaration interpretation:** R217's `EffectRow.concrete` is
  only `List EffectId`; it lacks effect type arguments and independently owned
  Function arrow rows. Mapping an ID to `EffectInstance operation []` or
  equating child root rows with arrow rows would invent semantics. Closure
  needs an independently justified equation from the actual declaration into
  a representation preserving those identities and row ownership.
- **BLOCKING — original coordinates:** R208's arbitrary
  `Owner Scope Event Witness` do not derive from the original Lambda's
  description/view/invocation/receipt frames or receipt environment. R217's
  numeric type scope is not derived from the original formal syntax. Closure
  needs source-owned lookup and assignment interpretation retaining event path,
  frames and the shared witness, then a proof that the generated clause gives
  `kernel.atom environment` for the exact original `sourceFormalRole` atom.
- Existing R208 reflection does not reduce the parent premise: it classifies
  the supplied tree, while original `Kernel.atom` remains independent. No
  concrete Yulang `SourceProblem` instance is present in the inspected source.

No module was written. No Lean/Lake, tests or cache generation ran. The exact
next safe work remains a primary-owned definition of the source declaration
interpretation, retaining unresolved effect/arrow correspondence explicitly;
that wrapper alone cannot be counted as parent progress. Writes stop after
this frozen receipt and central state update.
