# R213 — Source-qualified candidate Capture-frontier witness

## Adjudicated evidence class

The R187 local-source fixture provides a source-qualified candidate counterexample to the universal local Capture-frontier preservation law recorded as R183-FRONTIER-COVERAGE-1. It is stronger than R183's abstract three-row skeleton: the source HIR, completed source Origin, physical owner/emission, exact local callee binding, Capture graph, FreshUse row map and actual same-use Replay inputs are joined in one candidate run.

It remains a candidate-solver counterexample. The original native forwarding-preservation theorem, source/native correspondence, A/B claims, implementation approval and production gates stay OPEN. Independent review and Luna adjudication have not run. No production change follows from this witness.

## Exact same source and use

The HIR fixture is the unchanged R187 construction documented in `notes/theory/2026-10-21-r187-post-lambda-name-age.md` §3. The local call Apply occurrence 18 resolves by exact `HirLocalId` to local binding `relay`; its callee Name is occurrence 19. The actual local route is route 1, with boundary 1. The candidate solve succeeds and the observation is not truncated.

The `relay` Lambda at occurrence 12 emits these completed source Origins:

- slot 2: its positive Function/Value construction, captured as relation 74;
- slot 4: body effect `q_u` ≤ Lambda return `r_u`, relation 71, exact task Effect(10) ≤ Effect(31).

The slot-4 admission and emission are retained: admission 64 is an OwnerEmission on relation 71; emission 61 reads back Effect(10)'s `EffectUpperRow` slot 0 with the same key. The direct Origin receipt completed. R187's constructor audit identifies both q_u and r_u at level 2, above this route's boundary 1.

## Capture and row map

The positive Function node in the route Capture has argument-effect port Effect(23), result-effect port Effect(31), and result-value port Value(12). Capture records Effect(31) and Effect(23) as local level-2 rows; their FreshUse images are Effect(32) and Effect(33), respectively. Effect(10) is not a Capture row. The exact canonical representative query returns Effect(10) for Effect(10), so this is not an alias to a captured shared row.

The complete retained effect-bound inventory for this route contains relations 72, 73, 56, 57, 62 and 53 (listed with exact keys in R212). None contains Effect(10), relation 71 is absent, and no bound connects Effect(10) to the FreshUse image Effect(32). The candidate Capture has therefore lost the source edge q_u≤r_u at the actual relay provider route. The only uncopied history is not a shared-anchor identity: q_u is a level-2 source owner; the required edge is absent from this route's finite Capture graph.

The same Apply's route observation retains Replay dependency source relation 95, child 96, lower relation 92, upper relation 95. Its ordered lower and upper inputs are both the actual ValueRow(18) Function comparisons recorded in R210. This rules out a different-use substitution for the call observation; it does not create the omitted effect slot-4 edge.

## Countermodel boundary

R187 §3.3 supplies the finite candidate interpretation: preserve the original source suffix and all captured constraints, set shared/prefix effect rows to `{m}`, the FreshUse image of r_u (Effect(32)) and this call's result/output to empty. The captured edge Effect(31) positive ≤ Effect(28) positive becomes the compatible image edge Effect(32)≤Effect(28); the actual source edge Effect(10)≤Effect(31) stays in the original graph and is not transported to Effect(32). The same-use Replay Function inputs remain satisfied. Thus the candidate graph does not entail the source-required mapped inclusion.

This interpretation is a counterexample to the candidate Capture/FreshUse preservation claim for this source route. It is not a native evaluation, not evidence that the production compiler accepts an unsound program, and not a refutation of the original theorem without its source/native correspondence premises.

## Gate application and next action

R183-FRONTIER-COVERAGE-1 now has a fully source-qualified finite candidate witness: the actual Lambda slot-4 owner at level 2 is not visited by the same provider's Capture, while r_u is local and freshly mapped. The proof lane should replace the abstract skeleton as the first exact obstruction and retain the original theorem's full source/use quantifiers. A fresh independent compiler/proof review must verify the source/native correspondence and candidate countermodel against the frozen parent and R183 artifacts before Luna adjudicates.

No other source cases are discharged. Current/reuse, aliases across other histories, rollback, alternatives, repeated/simultaneous entries, F1/FK1, foreign continuations, pending matching and all remaining parent cases retain their original status. No inference behavior or expected output changes were made.
