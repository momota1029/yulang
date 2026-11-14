# Mat prior evidence contract and output conflicts

Status: awaiting direction. Scope: I33 exact proof interface, not language semantics.

The existing exact type `B4SkeletonV5.EvidenceNode (B4TargetV6.prior (GeneralNominalCenteredHeadMatStepBoundary.boundary roles))` is false for the concrete role catalogue in `GeneralDictionaryMatPriorConflictSource199`. A checked terminal Int head produces nominal0[Int] into a named target independently constrained to Int. Its actual initial state is reachable, inhabited, stable, SafeKnown and head-Unique; children=[] and old Evidence is false. `GeneralDictionaryMatPriorConflict199.not_prior_evidenceNode` proves this negation. `output_conflict` and `rejected` establish that V6 correctly rejects the state.

Options, without applying either:

1. Defer the unrestricted I33 closure until its interface is revised. Continue only the independently verified current-frame/total-packet node fragments; do not claim the old prior field.
2. Have the supervising boundary owner specify a V6 selected-only evidence law, including absence of OutputConflict (or the actual V6 selected premise), then assign that exact type. This matches V6 rejection and is the recommended contract repair, but is not implemented here.

No change to language semantics, Existing Evidence, Step, Stable, Local, or the boundary is proposed by these files. This note asks which proof interface should replace the refuted one, rather than silently weakening it.

Independent review clarification: adding a conflict-exclusion premise removes this particular counterexample only. It does not establish the replacement law. The separate full-total-packet/partial-Instance obstruction remains relevant, and current-frame compatibility, materialization agreement and historic-context transport still require proofs. No universal claim that all role catalogues fail is made; one legal concrete catalogue suffices to refute a proposed theorem for arbitrary roles. The full V6 Statement is not refuted here.
