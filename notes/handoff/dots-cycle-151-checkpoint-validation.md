# Cycle151 checkpoint verification

10 new modules,50 public theorems; general V5 remains6/14 supplied,8unresolved.

## lake build [10 modules listed by Audit/Cycle151 imports] --wfail
Exit0
```text
✔ [749/750] Built Yulang.GeneralDictionaryVariableTreeExample (2.7s)
✔ [750/750] Built Yulang.GeneralDictionaryVariableTreeEvidence (1.3s)
Build completed successfully (750 jobs).

```

## lake env lean --trust=0 Audit/Cycle151.lean
Exit0
```text
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

```

## lake env lean --trust=0 [scoped all-declaration gate for same10modules]
Exit0
```text
FOCUSED-AXIOM-PASS: 140 declarations in cycle151 modules

```
