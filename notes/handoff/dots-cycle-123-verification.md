# Cycle123 verification evidence

Exact source commit: `debaac8566a7b0b3a3063814abc74ac473a359f0`.

## Final focused aggregate

```sh
lake build Yulang.B4TargetV3 Yulang.B4TargetV3Functionality Yulang.B4TargetV3Totality Yulang.B4SkeletonV3 Yulang.B4TargetV3Regressions Yulang.B4TargetV3TotalityRegressions Yulang.GeneralDictionaryReadback Yulang.GeneralDictionaryModelEvidence Yulang.GeneralDictionaryReadbackExamples Yulang.GeneralDictionaryPayloadOrder Yulang.GeneralDictionarySemanticOrder Yulang.GeneralDictionarySemanticOrderExamples Yulang.GeneralDictionarySemanticUniqueness Yulang.GeneralDictionaryUniquenessExamples Yulang.GeneralDictionaryEmissionPlans Yulang.GeneralDictionaryEmissionPlanExamples Yulang.GeneralDictionaryPlanLookup Yulang.GeneralDictionaryPlanLookupExamples Yulang.GeneralDictionaryPlannedEvidence --wfail
```

Exit 0. Complete final command output:

```text
Build completed successfully (457 jobs).
```

## Trust-zero theorem audit

`lake env lean --trust=0 ../cache/yulang123/FinalAudit.lean`, exit 0. All 148 declarations, 29 axiom-free; only propext, Classical.choice and Quot.sound.

```text
'Yulang.B4TargetV3.tree_classifies' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.children_classify' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.render_resolves' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.renders_resolve' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.render_completed' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.renders_completed' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.classify_tree' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.classify_tree_iff' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.dictionary_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.dictionaries_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.diagnostic_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.diagnostics_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.same_diagnostic_refl' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.rejection_not_pending' does not depend on any axioms
'Yulang.B4TargetV3.safe_survivor_not_rejected' does not depend on any axioms
'Yulang.B4TargetV3.unique_not_ambiguous' does not depend on any axioms
'Yulang.B4TargetV3.inspection_not_rejected' does not depend on any axioms
'Yulang.B4TargetV3.local_functional' does not depend on any axioms
'Yulang.B4TargetV3.resolves_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.resolves_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.classify_functional' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.pending_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.pending_tree_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.completed_exact' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.local_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.B4TargetV3.inspection_pending_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.inspection_pending_tree_only' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3.rootK2_rejects' does not depend on any axioms
'Yulang.B4TargetV3.candidateK2_rejects' does not depend on any axioms
'Yulang.B4SkeletonV3.b4_of_bridges' depends on axioms: [propext, Quot.sound]
'Yulang.B4SkeletonV3.completed_of_bridges' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3Regressions.scalar_empty_classify' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3Regressions.scalar_empty_tree' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3Regressions.scalar_empty_not_rejected' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3Regressions.failed_child_tree' does not depend on any axioms
'Yulang.B4TargetV3Regressions.failed_child_not_root_rejected' does not depend on any axioms
'Yulang.B4TargetV3Regressions.failed_child_not_completed' depends on axioms: [propext]
'Yulang.B4TargetV3Regressions.failed_child_no_classification' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.inspecting_stable' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.inspecting_classify' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.inspecting_tree' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.inspecting_not_rejected' depends on axioms: [propext]
'Yulang.B4TargetV3TotalityRegressions.old_inspecting_rejected' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.inspecting_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.rootK2_inspecting_rejected' depends on axioms: [propext]
'Yulang.B4TargetV3TotalityRegressions.candidateK2_inspecting_rejected' depends on axioms: [propext]
'Yulang.B4TargetV3TotalityRegressions.conflicting_stable' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.conflicting_not_coherent' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.conflicting_no_local' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.unconditional_totality_false' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.nonempty_inspecting_stable' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.old_nonempty_inspection_hole' does not depend on any axioms
'Yulang.B4TargetV3TotalityRegressions.nonempty_inspection_closed' depends on axioms: [propext, Quot.sound]
'Yulang.B4TargetV3TotalityRegressions.inspected_empty_rejected' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.children_payload' depends on axioms: [propext]
'Yulang.GeneralDictionaryReadback.indexed_to_payload' depends on axioms: [propext]
'Yulang.GeneralDictionaryReadback.payload_to_indexed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.payloads_to_indexed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.payload_iff_erased' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.erased_evidence_node' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.indexed_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.indexed_children_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadback.payload_unique_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.stored_instance_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.indexed_all_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.erased_uniform_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.payload_all_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.stored_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryModelEvidence.stored_unique_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.stored_leaf' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.stored_tree' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.exact_readback' depends on axioms: [propext]
'Yulang.GeneralDictionaryReadbackExamples.stored_payload' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.nonvacuous_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.uniform_model_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.source_children_retained' depends on axioms: [propext]
'Yulang.GeneralDictionaryReadbackExamples.package_children_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryReadbackExamples.unique_indexed_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadOrder.equivalent_refl' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.equivalent_symm' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.equivalent_trans' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.equivalent_rootKey' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.eraseChildren_map' depends on axioms: [propext]
'Yulang.GeneralDictionaryPayloadOrder.erase_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadOrder.all₂_perm_right' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.all₂_replace_right' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.evidence_reorder' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.evidence_replace' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.equivalent_evidence' does not depend on any axioms
'Yulang.GeneralDictionaryPayloadOrder.equivalent_erased_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPayloadOrder.erase_does_not_reflect' does not depend on any axioms
'Yulang.GeneralDictionarySemanticOrder.unordered_intro' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.unordered_perm' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.unordered_idempotent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.unordered_children_perm' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.stored_invariant' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.model_invariant' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.indexed_stored_semantic' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.equivalent_stored_payload' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.equivalent_payload_all_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrder.equivalent_uniform_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.forward_stored' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.forward_backward_equivalent' does not depend on any axioms
'Yulang.GeneralDictionarySemanticOrderExamples.forward_backward_distinct' depends on axioms: [propext]
'Yulang.GeneralDictionarySemanticOrderExamples.left_wrong_key' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.backward_not_canonical' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.backward_semantic' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.backward_all_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.backward_nonvacuous' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.backward_uniform_source_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticOrderExamples.unordered_not_ordered_functional' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionarySemanticUniqueness.all₂_mono_members' depends on axioms: [propext]
'Yulang.GeneralDictionarySemanticUniqueness.align_roots' does not depend on any axioms
'Yulang.GeneralDictionarySemanticUniqueness.replace_all_children' depends on axioms: [propext]
'Yulang.GeneralDictionarySemanticUniqueness.evidence_unique' depends on axioms: [propext]
'Yulang.GeneralDictionarySemanticUniqueness.payload_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticUniqueness.unordered_package_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticUniqueness.stored_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySemanticUniqueness.model_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryUniquenessExamples.package_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryUniquenessExamples.stored_source_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryUniquenessExamples.model_source_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryUniquenessExamples.any_root_payload_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.declaration_key_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.plan_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.visible_plan' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.children_reorders' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.plan_reorders_forward' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.plan_reorders_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlans.selected_plan_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlanExamples.actual_child_plan' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlanExamples.wrap_plan' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlanExamples.wrap_plan_unique' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlanExamples.reversed_order' does not depend on any axioms
'Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmissionPlanExamples.reversed_same_plan' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPlanLookup.lookup_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookup.lookup_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookup.lookup_reorders' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookupExamples.actual_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookupExamples.missing_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookupExamples.wrong_role' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlanLookupExamples.reversed_lookup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlannedEvidence.planned_children_functional' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPlannedEvidence.lookup_node_stored' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryPlannedEvidence.lookup_node_all_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryPlannedEvidence.planned_unique_readback' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryPlannedEvidence.planned_reordered_uniform' depends on axioms: [propext, Quot.sound]
```

## Diff gate

`bash tools/verify-lean.sh . origin/integration/m1-final --no-build`, exit 0. Full output:

```text
verify-lean: . @ afaf89036 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

## Coverage of exact signatures

`lake env lean --trust=0 ../cache/yulang123/FinalSignatures.lean`, exit 0. All 148 names appear once in the inventory and their matching audit records; all 19 exact changed modules are imported. No full local lake build, full local Audit or supervisor AxiomGate was run.

## Source publication checkpoints

- `c5f7687f0bfc36ffc62a6ca40a2c36a5713fecaa`
- `bf924e21fe0c25334e81852a1e601739e0765097`
- `ed76e0b7c332bdc0822fb7399dd75afed3023691`
- `23ece79a370ef816c63761a99e29f2611a6a7603`
- `debaac8566a7b0b3a3063814abc74ac473a359f0`

## Hosted checks for the final exact source

{
  "source": "debaac8566a7b0b3a3063814abc74ac473a359f0",
  "tree": "043f0d36552375b87da887be7dc190f99baa4cb0",
  "sourceCI": [
    {
      "name": "core",
      "status": "completed",
      "conclusion": "success",
      "id": 130746860909,
      "url": "https://github.com/momota1029/yulang/actions/runs/43084974969/job/130746860909"
    },
    {
      "name": "proof",
      "status": "completed",
      "conclusion": "success",
      "id": 130746859714,
      "url": "https://github.com/momota1029/yulang/actions/runs/43084974670/job/130746859714"
    }
  ],
  "hosted": {
    "source": "debaac8566a7b0b3a3063814abc74ac473a359f0",
    "fullBuild": "1363",
    "printedDeclarations": 8529,
    "axiomFree": 224,
    "axioms": [
      "propext",
      "Quot.sound",
      "Classical.choice"
    ],
    "checkedOutExact": true
  },
  "checkpoints": [
    "c5f7687f0bfc36ffc62a6ca40a2c36a5713fecaa",
    "bf924e21fe0c25334e81852a1e601739e0765097",
    "ed76e0b7c332bdc0822fb7399dd75afed3023691",
    "23ece79a370ef816c63761a99e29f2611a6a7603",
    "debaac8566a7b0b3a3063814abc74ac473a359f0"
  ]
}
