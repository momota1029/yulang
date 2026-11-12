# Cycle151 integrated validation

28modules178public theorems. General V5 remains6/14supplied8unresolved.

## lake build Yulang.GeneralDictionaryEarlyMergeScalarClassification Yulang.GeneralDictionaryEarlyMergeScalarEvidence Yulang.GeneralDictionaryEarlyMergeScalarExample Yulang.GeneralDictionaryEarlyMergeScalarJoint Yulang.GeneralDictionaryEarlyMergeScalarReadback Yulang.GeneralDictionaryEarlyMergeScalarStable Yulang.GeneralDictionaryEarlyMergeVariableCoverage Yulang.GeneralDictionaryEmittedChildCount Yulang.GeneralDictionaryObservedAliasJoint Yulang.GeneralDictionaryObservedScalarRequests Yulang.GeneralDictionaryObservedTreeBranch Yulang.GeneralDictionaryObservedTreeExample Yulang.GeneralDictionarySelectedAliasConflict Yulang.GeneralDictionaryUnrecordedAliasLeafExample Yulang.GeneralDictionaryUnrecordedAliasLeafJoint Yulang.GeneralDictionaryUnrecordedVariableJoint Yulang.GeneralDictionaryVariableRequirements Yulang.GeneralDictionaryVariableStableCoverage Yulang.GeneralDictionaryVariableStableExample Yulang.GeneralDictionaryVariableTree Yulang.GeneralDictionaryVariableTreeChildSelected Yulang.GeneralDictionaryVariableTreeCoverage Yulang.GeneralDictionaryVariableTreeCycles Yulang.GeneralDictionaryVariableTreeEvidence Yulang.GeneralDictionaryVariableTreeExample Yulang.GeneralDictionaryVariableTreeInitialJoint Yulang.GeneralDictionaryVariableTreeInstallation Yulang.GeneralDictionaryVariableTreeSelected --wfail
Exit0
```text
✔ [771/771] Built Yulang.GeneralDictionaryObservedAliasJoint (2.0s)
Build completed successfully (771 jobs).

```

## lake env lean --trust=0 Audit/Cycle151.lean
Exit0
```text
'Yulang.GeneralDictionaryEarlyMergeScalarClassification.parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarClassification.acyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarClassification.child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarClassification.supported_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.child_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.full_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.edges_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.generated_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarEvidence.reachable_full_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.all_source_decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.query' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.schema' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.children_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.packet_guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.novel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.before_scheduled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.before_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.site_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.inputs_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.finish_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.actual_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarExample.inhabited_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.sites_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.alias_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.root_outside' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.related_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.packets_grow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.same_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.distinct_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.children_aliased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.unrecorded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.actual_two_unrecorded_joints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarReadback.parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarReadback.supported_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarReadback.classified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarReadback.actual_classified_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.models_of_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.varying_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.refresh_large_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.context_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.point_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.sameInputs_no_cross' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.merges_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.installs_committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.feedback_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarStable.stable_classified_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeVariableCoverage.ordinary_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeVariableCoverage.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeVariableCoverage.every_model_from_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeVariableCoverage.actual_stable_alias_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEmittedChildCount.children_length' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmittedChildCount.children_empty_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEmittedChildCount.empty_schema_nonempty_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedAliasJoint.selected_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryObservedAliasJoint.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryObservedAliasJoint.ordinary_stable_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedScalarRequests.source_scalar' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedScalarRequests.generated_shape' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedScalarRequests.requests_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedScalarRequests.generated_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeBranch.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeBranch.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeBranch.instance_of_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedTreeBranch.selected_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedTreeExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeExample.requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeExample.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryObservedTreeExample.named_request_present' depends on axioms: [propext]
'Yulang.GeneralDictionaryObservedTreeExample.nonterminal' does not depend on any axioms
'Yulang.GeneralDictionaryObservedTreeExample.every_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryObservedTreeExample.actual_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionarySelectedAliasConflict.branch_selected_key' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySelectedAliasConflict.joint_related_selected_key' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySelectedAliasConflict.different_selected_no_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionarySelectedAliasConflict.support_different_selected_no_joint' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafExample.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafExample.child_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafExample.actual_unrecorded_stable_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.leaf_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.covered_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedAliasLeafJoint.initial_trace_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedVariableJoint.selected_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedVariableJoint.covered_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedVariableJoint.initial_trace_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_nonterminal_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryUnrecordedVariableJoint.stable_instances_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableRequirements.emission_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableRequirements.requests_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableRequirements.generated_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableStableCoverage.stable_descendant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableStableCoverage.selected_instance_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableStableCoverage.dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableStableCoverage.dictionaries_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableStableExample.covered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableStableExample.every_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableStableExample.reachable_stable_unrecorded_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTree.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTree.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTree.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTree.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTree.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTree.selected_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_linked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.prepared_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.parent_conflict' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.parent_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.parent_not_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.unique_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_decisions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.child_support_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeChildSelected.reachable_classified_unstable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCoverage.selected_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCoverage.dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCoverage.dictionaries_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCoverage.reachable_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCycles.edge_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCycles.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeCycles.old_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.children_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.captures_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.child_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.leaf_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.child_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.child_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.full_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeEvidence.reachable_inhabited_full_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.nonterminal' does not depend on any axioms
'Yulang.GeneralDictionaryVariableTreeExample.actual_children_count' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.actual_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.inhabited_nonterminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeExample.actual_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.root_ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.initial_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.unrecorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.reachable_unrecorded_nonterminal_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.other_conflict' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.other_not_prepared' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInitialJoint.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.packet_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.novel' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.install_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.install_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryVariableTreeInstallation.not_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeSelected.other_failed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeSelected.not_mixed_recurs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeSelected.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeSelected.decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryVariableTreeSelected.support_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## lake env lean --trust=0 focused all-declaration gate for the28listed modules
Exit0
```text
FOCUSED-AXIOM-PASS: 486 declarations in cycle151 modules

```
