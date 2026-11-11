# I-19: arbitrary survivor relations do not guarantee local totality

Status: question for supervisor, not a new language decision. 2026-11-11.

The requested inspection-pending repair is implemented in B4TargetV3, including
K2 priority and the extra guard only on empty-candidate rejection. Local and
Classify are functional. The old empty-source and failed-child regressions are
retained; a stable, known-root, unfinished-inspection fixture is now pending.

A separate requested claim cannot hold for every existing SourceBoundary, even
under classical logic: Survivor may give one key two different child lists.
With no pending/K2 flags, there is no Unique candidate, but there are not two
different keys either. All four Local rules fail. The Lean countermodel is
B4TargetV3TotalityRegressions.conflicting_no_local; all its states are stable.
This is an abstract-interface countermodel, not a valid Yulang program.

Source-shaped example of the missing implementation obligation:

    impl Parent (box 'a) where Left 'a, Right 'a

For one source demand and the same selected Parent declaration, two derivations
must not supply [Left ?x, Right ?x] and [Left ?y, Right ?y] with different source
identities without proving their agreed canonical correspondence. Declared-key
uniqueness alone does not establish capture/allocation identity.

Options, delay first:
1. Recommended: retain the V3 target and the conditional local_total theorem.
   Derive SurvivorChildrenFunctional from actual item-3 candidate construction
   when that exists. No SourceBoundary or B4Bridges field is added here.
2. Add an explicit well-formed-source/coherence contract to the abstract totality
   statement. This changes that statement's premises and needs review.
3. Change same-key/different-children behavior to ambiguity or another diagnostic.
   This changes meaning and is not implemented or recommended as a proof fix.

The first option permits independent dictionary work now. Do not claim I-19's
unconditional totality, I-18 candidate completion, or any full B4 bridge closed.
