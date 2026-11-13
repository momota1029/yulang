# Observed finite request transport through reobservation

Draft, 2026-11-13. This work reduces the structural request premise used by V5 evidenceNode; it does not close that bridge.

The input certificate is `ObservedFiniteRequests.Tree`: a finite closed nominal tree with arbitrary finite arity, point source edges, and scalar leaves at existing source slots. For same-source `reobserve`, unchanged normalized view and `Refines` imply preservation of all recorded descriptors. Induction on the structural certificate therefore transports it. Neither Evidence nor generated Models is a premise.

Lift this to actual `FinishedTrace.Step` and finite traces (ordinary updates and certified, view-preserving actual feedback refreshes). For every final source model, transported certificates prove the generated materialization constraints. The final model is necessary; refresh may change model sets. No claim is made for arbitrary view-changing refresh, fresh targets, free binders, row arguments, general execution termination, or unconditional V5 evidenceNode.
