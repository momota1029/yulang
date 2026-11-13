# Cycle 154 focused verification

Full build and full supervisor gate intentionally not run.

## Focused build
```text
✔ [762/762] Built Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded (2.8s)
Build completed successfully (762 jobs).
```
Exit 0.

## All new declarations dependency gate
```text
FOCUSED-AXIOM-PASS: 444 declarations
```
Exit 0. Every declaration defined in all new modules was checked, not just public theorem lines.

## New audit shards
```text
'Yulang.GeneralDictionaryFiniteObservedExample.state_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.translation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.observed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.no_closed_tree' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.not_closed_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.tests_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.every_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.inhabited_request_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.named_request_present' depends on axioms: [propext]
'Yulang.GeneralDictionaryFiniteObservedExample.actual_requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.actual_request_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.ready' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.actual_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.full_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.actual_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExample.reachable_inhabited_named_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.generated_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.installs_committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.varying_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.refresh_large_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.point_closed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.feedback_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleStable.stable_reachable_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.no_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.no_candidate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.root_ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.children_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.support_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.stable_classified_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.value_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.value_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.value_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.value_classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleClassify.value_stable_classified_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.source_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.int_display_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.metadata' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.named_request_present' depends on axioms: [propext]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.nonterminal' does not depend on any axioms
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.every_source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.actual_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.initial_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.actual_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.root_ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.initial_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminal.actual_children_count' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.acyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.supported_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.supported_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.stable_classified_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClassification.value_installed_stable_classified_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.final_parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.final_child_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.edges_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.sites_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.generated_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.merges_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.varying_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.refresh_large_unknown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.context_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure.point_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.children_exact' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child_arguments' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child_instance' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.child_evidence' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.full_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalEvidence.reachable_inhabited_full_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.models_of_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.source_of_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.installed_models_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.final_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.nonempty_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence.reachable_full_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.packet_children' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.enabled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.children_nonempty' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.novel' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.install_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.install_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.not_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.installed_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalInstallation.value_install_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.observation_decreases' depends on axioms: [propext,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.no_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.no_candidate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalSelected.support_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable.installs_committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable.feedback_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable.stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable.stable_reachable_named_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.reserved_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.no_target_slot' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.not_observed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.source_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.actual_requests_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.initial_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.initial_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.tests_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReserved.initial_countermodel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive_source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.positive_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.branch_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.no_root' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.no_candidate' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.root_ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.children_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.packet_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.enabled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.novel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.value_install_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.installed_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.value_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.packet_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedPositive.journal_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded.recorded_request_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteObservedExampleReservedRecorded.reserved_install_regression' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.ready' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.instance_of_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.selected_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.selected_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.value_selected_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalTreeBranch.value_node_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.generated_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.extension_generated' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.at_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.trace_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.generated_models_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.generated_shape_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalRequestModels.actual_requests_models_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.subset_tests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.SchemaCoherent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.coherent_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.coherent_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.reachable_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.recorded_variableFree_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.reachable_root_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.subset_known' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.RequestsKnown' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.requestsKnown_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.requestsKnown_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.reachable_requestsKnown' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.reachable_subset_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryRecordedRequestModels.reachable_root_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.stable_site' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.selected_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.stable_joint_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.stable_joint_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.stable_joint_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.stable_merges_of_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.reachable_joint_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.reachable_joint_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.steps_reobservation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.reachable_reobservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.reachable_packetFree_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryValueEvidence.reachable_packetFree_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.at_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.trace_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.generated_models_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.generated_shape_after_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.value_generated_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryHistoricalValueRequests.value_generated_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
Exit 0.

## Diff-only supervisor script
```text
verify-lean: . @ 797889fdb (base c10b05194)
ok: no removed lines in lean/ since c10b05194
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
ok: lean/Audit/Cycle143.lean only appended (plus top import lines)
ok: lean/Audit/Cycle144.lean only appended (plus top import lines)
ok: lean/Audit/Cycle145.lean only appended (plus top import lines)
ok: lean/Audit/Cycle146.lean only appended (plus top import lines)
ok: lean/Audit/Cycle147.lean only appended (plus top import lines)
ok: lean/Audit/Cycle148.lean only appended (plus top import lines)
ok: lean/Audit/Cycle149.lean only appended (plus top import lines)
ok: lean/Audit/Cycle150.lean only appended (plus top import lines)
ok: lean/Audit/Cycle151.lean only appended (plus top import lines)
ok: lean/Audit/Cycle152.lean only appended (plus top import lines)
ok: lean/Audit/Cycle153.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalBudget.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalDownstream.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupport.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalSupportOrder.lean only appended (plus top import lines)
ok: lean/Audit/GeneralNominalValueProvenance.lean only appended (plus top import lines)
ok: lean/Audit/Recovery131135.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```
Exit 0. Local cache symlink excluded from untracked-source check; no source excluded.
