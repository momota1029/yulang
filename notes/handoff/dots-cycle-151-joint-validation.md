# Cycle151 independent Joint worker validation

Final 6 modules, 52 public theorems, all 167 declarations checked. The dependency modules GeneralDictionaryVariableRequirements and GeneralDictionaryVariableTree are independently supplied by the nonterminal worker.

Commands (Lean 4.35.0, exit 0 for every final source):

```text
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true -o /tmp/y151-joint-lib/Yulang/<module>.olean Yulang/<module>.lean
```

Modules: GeneralDictionaryUnrecordedAliasLeafJoint, GeneralDictionaryUnrecordedAliasLeafExample, GeneralDictionaryUnrecordedVariableJoint, GeneralDictionaryEarlyMergeScalarExample, GeneralDictionaryEarlyMergeScalarClassification, GeneralDictionaryEarlyMergeScalarJoint.

Each source emitted no diagnostics on final compilation. Dependencies used existing verified oleans and separate output-directory symlinks; no project-wide build was run by this worker. Full integrated focused lake build is the parent's separate check.

```text
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true /tmp/y151-joint-all-audit.lean
exit 0
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
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.distinct_children' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.children_aliased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.unrecorded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.actual_two_unrecorded_joints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryEarlyMergeScalarJoint.same_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
FOCUSED-AXIOM-PASS: 167 declarations in six cycle151 unrecorded alias modules
```

The gate enumerates environment constants whose defining module is exactly one of these six, then applies collectAxioms to every constant. It rejects any dependency other than propext, Classical.choice or Quot.sound and rejects an empty audit. Thus private and generated declarations are included, not only the 52 printed public theorems.

```text
LEAN_PATH=/tmp/y151-joint-lib lean --trust=0 -DwarningAsError=true /tmp/y151-joint-types.lean
exit 0
```

Complete type output is in dots-cycle-151-joint-types-1.md and -2.md. No old semantic definition or proof was edited; frozen aggregate Audit.lean and README were untouched. No general bridge count reduction or stable result for the new two-site merge fixture is claimed.
