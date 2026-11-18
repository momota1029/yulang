# Cycle263 standalone audit guide

Each file imports only Yulang modules and is tested alone with lake env lean.

- Complete: explicit definitions, abbreviations and theorems' axiom sets.
- Full: every production constant in the cycle namespaces, including private/generated constants; only standard axioms allowed.
- Types: full quantified types, without eliding semantic premises.
- Reach: chosen intended end roots; outside-root declarations are not classified as dead code.
- Normalized: normalized-body/binder/default-center transport and concrete shadow-support examples.
- OwnerFoundation / RegisteredOwners: tagging, finite addresses and historical source provenance.
- MultiIndependent / UniversalIndependent: independently rebuilt multi-owner execution, Plan-free address coverage and result bounds.
- TwoOwner / UniversalRegression: two actual owners, real nonempty request writes; unused reservation can remain at a terminal state.
- Representatives: actual source representative selection and nonempty source installation example.
- SourceMeaningIndependent / LocalHeads: global and localized head-only context transport; strong assumptions remain visible.
- SourceContext: a concrete uniform assignment satisfies actual initial Models and all future heads; no matching nonempty mixed-installation example is claimed.
- FiniteStates: exact exponential list enumeration, retaining duplicate states for repeated basis facts.
- FiniteContext: inspector-wide head support iff head support over the explicit finite inspector-image list, still a semantic assumption.
- InitialBoundary: `initial_selected_empty`, `initial_inspector_noop`, `selected_is_committed`, `selected_cannot_be_novel`. Registered-only replay cannot discover the first source Plan; the same retained Plan at the same snapshot fails the new-install novelty premise. This does not exclude a different current Plan with the same owner or future source changes.

All these focused audits concern explicit interfaces. None asserts complete source execution, old Step termination, SAT, full packet/EvidenceNode or M1.

- ProspectiveEffect: source_frame_then_check and source_outcome on an actual current Frame, plus the reusable checked_effect. Selected-plan check is performed by cases, not presumed successful for every candidate.
