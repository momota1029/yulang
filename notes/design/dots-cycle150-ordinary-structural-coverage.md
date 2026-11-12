# Cycle150: ordinary histories with unrecorded structural leaves

Scope: EvidenceNode/dictionary soundness support, not closure of general V5. The general count remains 6/14 supplied, 8/14 unresolved.

`GeneralDictionaryBranchOrdinaryCoverage.Covered` retains a structural coverage obligation, but its recorded alternative requires only membership of an actual packet at the same occurrence. It does not request Extension for every packet, matching declaration IDs, Instance, Joint, or BranchModels. The other alternatives are the existing finite unary spine leaf and scalar leaf structural predicates.

For every finite actual ordinary trace from the empty initial journal, `coverage_from_trace` derives every packet's Extension using `initial_packets_extension`. The inverse `forget_growth` gives `covered_iff`: old and reduced structural criteria are equivalent on those traces. The proof does not silently assume refresh/reobserve preserve ordinary Extension; those steps are excluded by the existing ordinary Step relation.

`dictionary_evidence` applies this fact to arbitrary finite dictionary depth, a genuine InitialSource, and any current Models assignment, preserving the same assignment throughout. The finite Classify derivation and the reduced structural criterion remain hypotheses. This is broader than `GeneralDictionaryCoveredEvidence.ordinary_dictionary_evidence`: it permits unrecorded terminal leaves, which the old all-recorded criterion excludes.

`recursive_fixture` applies the ordinary-trace composition to the existing real recursive example with a recorded parent and unrecorded scalar child, for every current model. The concrete state already has a model in the fixture; no existential consistency is substituted for same-model evidence.

This does not derive structural coverage for arbitrary reachable stable sources, generalize spine leaves to arbitrary branching nominal patterns, prove executor termination, or supply any of the eight remaining V5 bridges.

## Verification

Direct Lean 4.35.0 `-DwarningAsError=true` check of the new module: exit 0. Dependencies were the parent's verified cycle149 build at 7a7b330. A separate `--trust=0 -DwarningAsError=true` run with all five public theorem axiom checks and exact `#check @...` types also exited 0. Only propext, Classical.choice and Quot.sound occur. Full build was not run. Full output: /tmp/y150-coverage-audit.log (to be incorporated in the cycle report by the integrating writer).
