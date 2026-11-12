# Cycle150 recovery verification

Source recovered from7a7b330, published639ab803. Commands rerun during150.

## build
`cd lean && lake build $(sed -n 's/^import //p' Audit/Cycle149.lean) --wfail`
exit0
```text
Build completed successfully (730 jobs).

```

## audit
`cd lean && lake env lean --trust=0 Audit/Cycle149.lean`
exit0
```text
'Yulang.GeneralDictionaryInstallationOrigin.origin_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.packet_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.steps_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.packet_generated' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.step_packets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.steps_packets' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.origin_member' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.member_iff_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.origin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.nonterminal_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.formed_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryInstallationOrigin.packet_history' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.models_of_membership' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.fold_membership' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.generated_models_of_same_schema' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.root_request_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.terminal_requests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.generated_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalFiniteAssociatedFacts.branch_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.RecordedPath.sound' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.RecordedPath.mono' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.nominal_observes_of_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.coherent_of_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.path_equate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.path_after_equate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.path_sound_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.merges_after_steps_of_journal_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSharedJournalPaths.branch_after_steps_of_journal_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCoveredEvidence.classify_node_parts' does not depend on any axioms
'Yulang.GeneralDictionaryCoveredEvidence.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryCoveredEvidence.dictionaries_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCoveredEvidence.reachable_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryCoveredEvidence.ordinary_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOrdinarySelectedReplay.selected_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOrdinarySelectedReplay.selected_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOrdinarySelectedReplay.selected_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySameContextSelection.selected_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySameContextSelection.selected_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySameContextSelection.selected_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySameContextSelection.selected_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.at_actual' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.step_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.at_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.steps_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.steps_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.steps_formed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.packets_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.initial_packets_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.initial_selected_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.initial_selected_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportOrdinaryExecution.installed_suffix_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.nominal_source_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.schema_source_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.fold_variables' depends on axioms: [propext]
'Yulang.GeneralNominalAssociatedSourceTransport.fold_tests' depends on axioms: [propext]
'Yulang.GeneralNominalAssociatedSourceTransport.generated_models_transport' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.generated_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.branch_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.generated_unknown_false' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalAssociatedSourceTransport.request_ready_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalFiniteHistoricalBranch.branch_after_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalHistoricalSelectedEvidence.packet_role' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalHistoricalSelectedEvidence.packet_root_defined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalHistoricalSelectedEvidence.selected_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.input_requests_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.emission_requests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.canonical_emission_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.request_witness' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.generated_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.branch_models_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.generated_unknown_false' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereAssociatedFacts.request_ready_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedCoverageLimit.ordinary_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedCoverageLimit.no_leaf_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedCoverageLimit.leaf_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedCoverageLimit.leaf_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecordedCoverageLimit.stable_selected_unrecorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.edge_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.no_packet_no_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.committed_nonterminal_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.selected_nonterminal_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.edge_iff_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEdgeOrigin.unrecorded_nonterminal_not_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.generated_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.children_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryLinearLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalHistoricalNodeEvidence.selected_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverage.dictionaries_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverageExample.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverageExample.every_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMixedCoverageExample.stable_success' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.branch_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.instance_of_shape' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.selected_leaf' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.selected_of_coverage' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarLeaf.recursiveDisplay_covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalMaterializedHeadRecovery.observed_argument' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMaterializedHeadRecovery.heads_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMaterializedHeadRecovery.materialized_head_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMaterializedHeadRecovery.component_membership' depends on axioms: [propext]
'Yulang.GeneralNominalMaterializedHeadRecovery.request_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalMaterializedHeadRecovery.packet_request_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.administrative_seed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.administrative_ordinary' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.step_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.step_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.steps_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.steps_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.recorded_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportSourceInvariants.packet_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.step_sites' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.steps_sites' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.packet_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.packet_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.ordinary_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJoint.initial_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNestedLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNestedLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNestedLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNestedLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNestedLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineCoverage.dictionaries_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineCoverage.of_mixed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySpineCoverage.recursive_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.linear_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySpineLeaf.nested_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.administrative_key' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.step_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.steps_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.packet_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.packet_translate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionarySupportMetadataInvariants.packet_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.root_find' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.root_request_member' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.root_outputs_equivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.output_target_allocated' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.child_target_same_seed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalHistoricalOutputRecovery.child_outputs_equivalent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.parent_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.nested_observation_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.nested_argument_bounds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.projection_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalNestedLinearFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalQueryRecoveredNodeEvidence.packet_head_name' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalQueryRecoveredNodeEvidence.selected_node' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalRecoveredNodeEvidence.selected_node_without_output_paths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalSpineFacts.source_matches' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.nominal_observation_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.point_child_matches' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.visit_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.variables_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.append_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.inspect_leaf' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.inspect_wrap' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.origin_default' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.spine_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.spine_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.spine_finished' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.spine_bounds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.spine_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalSpineFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalStructuralSelectedGraph.selected_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalStructuralSelectedGraph.branchAt_of_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalStructuralSelectedGraph.singleton_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalStructuralSelectedGraph.singleton_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalStructuralSelectedGraph.structural_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralNominalWhereRequestMembership.canonical_emission_member' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalWhereRequestMembership.child_request_member' depends on axioms: [propext, Quot.sound]

```

## gate
`tools/verify-lean.sh . origin/integration/m1-final --no-build`
exit0
```text
verify-lean: . @ 7a7b330f5 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: lean/Audit.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalCompletion.lean only appended (plus top import lines)
ok: lean/Audit/AstraCanonicalView.lean only appended (plus top import lines)
ok: lean/Audit/AstraConfluence.lean only appended (plus top import lines)
ok: lean/Audit/AstraOrder.lean only appended (plus top import lines)
ok: lean/Audit/Cycle136.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Finished.lean only appended (plus top import lines)
ok: lean/Audit/Cycle137Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Formation.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Joint.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Refresh.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Terminal.lean only appended (plus top import lines)
ok: lean/Audit/Cycle138Tree.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139.lean only appended (plus top import lines)
ok: lean/Audit/Cycle139Followup.lean only appended (plus top import lines)
ok: lean/Audit/Cycle140.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141.lean only appended (plus top import lines)
ok: lean/Audit/Cycle141Recorded.lean only appended (plus top import lines)
ok: lean/Audit/Cycle142.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)

```

Initial gate invocation omitted the required repo/base arguments and exited1 with usage; the corrected invocation above passed.
