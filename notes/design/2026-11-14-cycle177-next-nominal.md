# Next-cycle research: nonpoint linear nominal candidates

Status: read-only source investigation after cycle177 implementation freeze. No change to the published Lean modules; no new general nominal producer or impossibility theorem is claimed.

## Conclusion

Extending the scalar producer directly to every current centered model is NOT justified merely by nominal invariance. Centered site Fits proves endpoint order and nominal invariance discharges semantic cross-comparisons, but a nonpoint nominal inspection captures each binder twice, generating equations for fresh merged capture identities. Current centered Models does not in general prescribe those fresh identities. Candidate.Prepared supplies some branch model, not validity of these equations in the chosen current model.

This is a concrete missing premise visible in existing definitions, not a completed counterexample theorem. Next cycle should first expose the residual merge obligation (or construct a counterexample), rather than claim unconditional candidate_holds.

## Exact reusable results

- `GeneralDictionaryCenteredScalarIntervals177.candidate_ordered`: from Candidate and centered Models, every successfully located packet bound is ordered. Uses `candidate.centered_recorded` and `Models.2.1` (centered Site.Holds); the raw SiteHolds only constrains positions with recorded origins and is insufficient on its own for arbitrary nonpoint bounds.
- `GeneralNominalIntervalLaws.nominal_endpoint_checks`: current state Models, lower/upper recorded descriptors, and endpoint Subtype yield equality of nominal declaration names and `ParameterChecks` at every corresponding descriptor argument. No point-endpoint premise.
- `GeneralNominalIntervalLaws.ParameterChecks`/`Checks`: the four own/cross inequalities. These suffice for shared interval compatibility, not fresh identity equations.
- `CommonNominalFullCarrier.nominal_regular_invariant_exact`: nominal Subtype iff same name, same list length, and pointwise ArgumentsEquivalent. Combine descriptor model equalities with endpoint order via subtype_trans.
- `GeneralNominalIntervalLaws.nominal_subtype_equivalent` and `nominal_sandwich`: invariance gives equivalence of nominal endpoint values and any intermediate actual value.
- `GeneralNominalProjections.parameter_binding_valid`: each descriptor argument supplies an actual observation and Fits, without point intervals.
- `GeneralNominalProjections.equal_all_observations` / `compatible_cross`: once a cross-origin equality witness exists, every observation has the same argument equivalence and cross parameter checks follow.
- `GeneralNominalLinearCaptureFacts.inspectMany_exact`: exact variable inspection for arbitrary finite names, bounds, origins and offset.
- `GeneralNominalLinearCaptureFacts.typeArguments_exact`: converts type-only descriptor parameters to the actual finite list of bounds.
- `GeneralNominalLinearCaptureFacts.projection_models`, `private_models`, `branch_models_iff_materialized`: retain one *outer* `(slot,slot)` premise. Their inner descriptor bounds are already arbitrary intervals. They do not solve a nonpoint outer pair.
- `GeneralNominalSharedCaptureFacts.compatible_of_coherent`, `private_models_of_merges`, `branch_models_iff_residual`: demonstrate the correct decomposition into source Models, origin coherence, explicit merge equations, and materialization Models. These also describe a single outer slot, so need a two-origin report analogue.

## Why the existing point proof does not transplant

`GeneralNominalRecursiveInspection.inspect`, nominal case:
1. inspect lower descriptor arguments;
2. if lower slot=upper slot, return that one report;
3. otherwise inspect the upper descriptor arguments with the same pattern/binder names and append both reports.

Thus even an injective name vector has two captures per name across the appended reports. `LinearCaptureFacts.filter_binding`/`occurrences_exact` yield singleton occurrences only for one report. `GeneralNominalAllocation.capture` preserves source bounds only for singleton occurrences; otherwise it creates fresh lower/upper IDs. `GeneralNominalAllocation.merges` then requires equations identifying those fresh IDs with lower-union and upper-intersection expressions. `propagate_models` explicitly requires their truth in the same assignment.

`GeneralNominalBranchProjection.append_projection` requires disjoint capture names, which fails for the two nominal endpoint reports. Replace it with an append lemma accepting cross-origin equivalence and the associated Fits obligations, rather than reusing the separation premise.

`GeneralDictionaryNonpointBranch.branch` is replay of an already-valid terminal depth-two branch under a specific revision. It assumes old BranchModels and current source Models; it is not a producer for an unrecorded candidate. Do not use it as evidence that arbitrary current models satisfy fresh merge equations.

## Minimal useful next implementation

1. Exact report for a same-name nominal pair with type-only arity n and injective binder vector (handle slot equality separately).
2. Derive cross-origin argument equivalence from descriptor Models and centered endpoint order; package append ProjectionModels and Compatible.
3. State and prove an exact branch equivalence with **fresh merge equations remaining explicit**, plus materialization, or show the terminal/no-output case reduces exactly to merge equations.
4. Concrete empty-journal counterexample: two distinct nominal endpoint slots with equal nominal values; choose the fresh capture-lower assignment to an incompatible scalar. Source/centered Models and Candidate branch existence can still hold, but same-model propagation fails. This must be formally verified before reporting an impossibility result.
5. For positive production, either use a recorded merge-equation invariant, or construct an assignment extension that preserves current source identities. The latter only yields Evidence in the extended model, and cannot fill the existing universal fixed-model EvidenceNode without an additional preservation/transport argument.

Existing `GeneralDictionarySharedCapturedModel` is a concrete example of assigning fresh identities separately while preserving old sources, not a general extension theorem. `GeneralNominalCaptureMerges.capture_interval_exact` and `propagated_capture_exact` assume merge equations/propagated Models; neither supplies them automatically.
