# Cycle151 Joint worker final validation

Supersedes the earlier 6-module snapshot for this worker only. Final source commit7ef01d9d6: 10 modules, 78 public theorems, ALL242declared constants audited. Both audit and type print exit0 at22:48UTC. Integrated parent lake build is a separate check.

Every new source compiled with Lean4.35.0 `--trust=0 -DwarningAsError=true`, with existing verified dependency oleans and separate output directory. Final source checks emitted no diagnostics. No full-project build or Yulang2 runtime run by this worker.

Commands:
```text
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true -o /tmp/y151-joint-lib/Yulang/<module>.olean Yulang/<module>.lean
# Each of 10 modules: exit0, no output
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true /tmp/y151-joint-final-audit.lean
# exit0
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
FOCUSED-AXIOM-PASS: 242 declarations in ten cycle151 unrecorded alias modules
```

The gate enumerates the defining-module indices for all environment constants, selects exactly the10new worker modules, calls collectAxioms for EVERYconstant including private and generated declarations, and rejects dependencies outside propext/Classical.choice/Quot.sound or an empty scope. It is not merely a list of public #print axioms lines.

```text
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true /tmp/y151-joint-final-types.lean
# exit0
```
Complete quantified type output: dots-cycle-151-joint-final-types-1.md through -3.md. Earlier6-module logs remain historical. General V5 remains6/14supplied and8/14open.
