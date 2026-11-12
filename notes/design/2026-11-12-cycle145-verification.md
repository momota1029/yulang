# Cycle145 verification record

Focused checks only; this is not a whole-repository rebuild. All commands below
returned exit 0. Full theorem types are in the separate theorem inventory.
Public declarations (including definitions/abbreviations) exactly match audit
coverage: 280. Public theorems: 230 across 24 new modules. Only propext,
Classical.choice and Quot.sound occur; declarations with no axioms are included.

## Focused build and axiom audit

```sh
cd lean
lake build $(sed -n 's/^import //p' Audit/Cycle145.lean) --wfail
lake env lean --trust=0 Audit/Cycle145.lean
```

```text
Build completed successfully (760 jobs).
'Yulang.GeneralDictionaryAliasJoint.joint_at_related' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasJoint.joint_alias_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasJoint.representative_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFailedDiagnosticScope.no_selected_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFailedDiagnosticScope.no_children_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFailedDiagnosticScope.node_at_failed_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryJointMerge.evidence_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.evidence_merge_of_outputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.branch_extension' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.branch_extension_back' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.merge_sources' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.branch_merge' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.branch_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.alias_merge_first_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.joint_merge_shared' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.joint_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.joint_merge_of_outputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.branch_output_targets' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.joint_merge_registered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMerge.sourceformed_merge_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.models_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.evidence_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.evidence_at_final_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.event_atoms_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.models_events_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryMergeSequence.evidence_events_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeResidual.separate_joint_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeResidual.separate_joint_failure_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeResidual.recorded_key_conflict' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.sources_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.branch_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.packets_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.sites_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.joint_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.aliases_fold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.alias_edges_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.alias_events_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.joint_events_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.terminal_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.source_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.emissions_empty' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.schema_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.before_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.branch_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.same_inputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.dictionary_outputs' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.output_atoms_nonempty' depends on axioms: [propext]
'Yulang.GeneralDictionaryJointMergeExample.output_atoms_hold' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.merged_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.source_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.merged_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryScalarMerge.output_atoms_of_scalar_tests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarMerge.evidence_merge_of_scalar_tests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarMergeExample.generated_output_equations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryScalarMergeExample.complete_evidence_from_requests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.recovered' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.guard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.distinct' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.actual_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.enabled_nonempty_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFailedDiagnosticScope.b' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeEnabled.tracked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.outputEquation' does not depend on any axioms
'Yulang.GeneralDictionaryJointMergeExample.terminal' does not depend on any axioms
'Yulang.GeneralDictionaryJointMergeExample.registry' does not depend on any axioms
'Yulang.GeneralDictionaryJointMergeExample.source' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.context' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.demand' depends on axioms: [propext]
'Yulang.GeneralDictionaryJointMergeExample.root' depends on axioms: [propext]
'Yulang.GeneralDictionaryJointMergeExample.model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.first' depends on axioms: [propext]
'Yulang.GeneralDictionaryJointMergeExample.last' depends on axioms: [propext]
'Yulang.GeneralDictionaryJointMergeExample.before' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeExample.meaning' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeJournalScope.badModel' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeJournalScope.bad_source_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeJournalScope.lastPacket' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeJournalScope.bad_packet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryJointMergeJournalScope.no_empty_facts_formation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryJointMergeResidual.Shared' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryJointMergeSequence.Targets' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.firstClause' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeReachable.secondClause' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeReachable.declaration' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeReachable.registry' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeReachable.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.start' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.all_source_decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.query' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.outputTarget' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.output_nonzero' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.schema' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.child' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.children_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.packet' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.before' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.packet_guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.novel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.before_scheduled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.before_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.site' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.site_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.inputs_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.finish' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.actual_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.finish_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.actual_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.inhabited_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.output_atoms_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.output_targets_distinct' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.finish_sourceformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeReachable.reachable_nonempty_output_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScalarFacts.packet_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScalarFacts.requests' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScalarFacts.all_models_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScalarFacts.all_models_evidence_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScope.child_no_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScope.child_no_joint' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScope.child_no_instance' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScope.child_no_evidence' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeScope.reachable_without_child_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryScalarJournalMerge.Requests' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarJournalMerge.outputs_from_packets' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarJournalMerge.models_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryScalarJournalMerge.evidence_merge_iff' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.firstClause' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeSuccess.secondClause' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeSuccess.declaration' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.registry' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeSuccess.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.registry_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.start' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.all_source_decisions' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.query' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.outputTarget' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.output_nonzero' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.schema' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.prepared' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.survivor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.selected' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.child' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.children_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.packet' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.before' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.enabled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.packet_guard' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.novel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.source' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.before_scheduled' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.before_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.site' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.site_present' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.inputs_same' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.finish' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.actual_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.finish_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.actual_path' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.inhabited_early_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.output_atoms_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.output_targets_distinct' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.finish_sourceformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.reachable_nonempty_output_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal_report' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal_schema' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.terminal_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.final_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.current_terminal_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.current' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.output_reserved' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.sources_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.current_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.child_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.child_branch_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.old_alias_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.first_not_parent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.last_not_parent' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.sites_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.merged_alias_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.merged_child_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.merged_child_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeSuccess.reachable_joint_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRootEvidence.rootPayload' does not depend on any axioms
'Yulang.GeneralDictionaryOutputMergeRootEvidence.parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRootEvidence.current_parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRootEvidence.root_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRootEvidence.reachable_full_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.parent_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.source_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.output_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.terminal_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.terminal_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.current_parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.current_terminal_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.child_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeAllModels.full_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.branch_of_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.root_linked' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.root_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.child_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.root_alias_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.root_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.child_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeJointModels.inhabited_joint_and_universal_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeExactPayload.child_instance_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeExactPayload.parent_instance_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeExactPayload.child_payload_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeExactPayload.root_payload_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeExactPayload.evidence_iff_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.parent_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.child_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.parent_survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.child_survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.supported_parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.supported_child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeClassification.reachable_classified_full_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.source_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.journal_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.actual_step_of_novel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_reachable_of_novel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.not_stable_of_novel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_sourceformed_of_novel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.actual_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.not_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_sourceformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.next_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedback.classified_but_not_saturated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.badModel' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.output_above_one' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.at_zero' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.at_one' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.at_left' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.at_right' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.source_model' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.raw_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.not_output_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeRawModel.not_raw_equal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.nextContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.next_root_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.next_child_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.next_parent_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.next_child_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.acyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.parent_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.child_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.parent_survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.child_survivor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.supported_parent_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.supported_child_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryOutputMergeFeedbackClassification.reachable_classified_full_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## Direct kernel check of every added source

```sh
cd lean
for m in $(sed -n 's/^import Yulang\.//p' Audit/Cycle145.lean); do
  lake env lean --trust=0 -E warning "Yulang/$m.lean"
done
```

```text
DIRECT:GeneralDictionaryOutputMergeFeedbackClassification
DIRECT:GeneralDictionaryOutputMergeFeedback
DIRECT:GeneralDictionaryOutputMergeRawModel
DIRECT:GeneralDictionaryOutputMergeClassification
DIRECT:GeneralDictionaryOutputMergeExactPayload
DIRECT:GeneralDictionaryOutputMergeAllModels
DIRECT:GeneralDictionaryOutputMergeJointModels
DIRECT:GeneralDictionaryOutputMergeRootEvidence
DIRECT:GeneralDictionaryOutputMergeSuccess
DIRECT:GeneralDictionaryJointMergeJournalScope
DIRECT:GeneralDictionaryOutputMergeReachable
DIRECT:GeneralDictionaryOutputMergeScalarFacts
DIRECT:GeneralDictionaryOutputMergeScope
DIRECT:GeneralDictionaryScalarJournalMerge
DIRECT:GeneralDictionaryAliasJoint
DIRECT:GeneralDictionaryFailedDiagnosticScope
DIRECT:GeneralDictionaryJointMerge
DIRECT:GeneralDictionaryMergeSequence
DIRECT:GeneralDictionaryJointMergeResidual
DIRECT:GeneralDictionaryJointMergeSequence
DIRECT:GeneralDictionaryJointMergeExample
DIRECT:GeneralDictionaryScalarMerge
DIRECT:GeneralDictionaryScalarMergeExample
DIRECT:GeneralDictionaryJointMergeEnabled

```

## Development failures and correction

One initial tree creation hit an auto-review timeout; the explicitly permitted
single retry succeeded. No Git blob confirmation was requested. Local proof
iterations encountered an induction argument arity mismatch, a let-bound iff
rewrite requiring reduction, and generated-schema projection/singleton-membership
elaboration mismatches. These were corrected before publication; final focused
build, all source checks, type inventory and audits pass. One attempted worker
CLI --wfail option was unsupported by lean directly; the correct -E warning
source check was rerun successfully. No failed check is counted as a pass.
