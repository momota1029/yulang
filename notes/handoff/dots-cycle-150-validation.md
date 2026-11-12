# Cycle150 final focused verification

16modules,91public theorem checks,361scoped declarations. No local full build.

## build150
`cd lean && lake build Yulang.GeneralDictionaryAliasMixedLocality Yulang.GeneralDictionaryAliasRecordedLocality Yulang.GeneralDictionaryAliasTreeLocality Yulang.GeneralDictionaryBranchCoverage Yulang.GeneralDictionaryBranchLeaf Yulang.GeneralDictionaryBranchOrdinaryCoverage Yulang.GeneralDictionaryFiniteJournalJointExample Yulang.GeneralDictionaryNamedLocality Yulang.GeneralDictionaryNamedLocalityExample Yulang.GeneralDictionaryTreeCoverage Yulang.GeneralDictionaryTreeLeaf Yulang.GeneralNominalBranchExample Yulang.GeneralNominalBranchFacts Yulang.GeneralNominalBranchProjection Yulang.GeneralNominalTreeExample Yulang.GeneralNominalTreeFacts --wfail`
exit0
```text
Build completed successfully (748 jobs).

```

## audit150
`cd lean && lake env lean --trust=0 Audit/Cycle150.lean`
exit0
```text
'Yulang.GeneralDictionaryFiniteJournalJointExample.alias_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.actual_stable_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.coverage_from_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.forget_growth' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.covered_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.recursive_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.steps_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_aliases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_named' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_invariants' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.alias_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.related_locality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.root_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.child_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.actual_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.every_model_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.leaf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.covered_of_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasMixedLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.covered_of_locality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.related_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasRecordedLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchExample.state_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.actual_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchExample.not_unary_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchExample.inhabited_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalBranchProjection.point_argument_matches' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.append_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.spine_capture_name' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.inspect_fork' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_finished' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalBranchProjection.fork_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.dictionaries_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.of_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.recursive_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchCoverage.initial_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.leaf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_of_recorded' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.early_ordinary_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryAliasTreeLocality.covered_of_mixed' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.selected_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.dictionary_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.dictionaries_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.of_branch' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.recursive_fixture' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeCoverage.initial_dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.branch_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.ready' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.instance_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.selected_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.selected_of_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.spine_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryTreeLeaf.branch_covered' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.state_models' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.actual_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeExample.inner_not_spine' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.not_single_fork' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeExample.inhabited_tree_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeFacts.capture_name' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_projection' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_bindings' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_finished' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_bounds' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.tree_checked' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.report_exact' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.private_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralNominalTreeFacts.ofSpine_query' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralNominalTreeFacts.ofFork_query' depends on axioms: [propext, Quot.sound]

```

## scoped
`cd lean && lake env lean --trust=0 ScopedGate150.lean`
exit0
```text
FOCUSED-AXIOM-PASS: 361 declarations in cycle150 modules

```

All91theorem types are preserved separately in dots-cycle-150-types-*.md. The gate iterates every declaration whose module is one of the16imports and rejects dependencies outside propext, Classical.choice, Quot.sound.

## ScopedGate150.lean (complete generated check)
```lean
import Yulang.GeneralDictionaryAliasMixedLocality
import Yulang.GeneralDictionaryAliasRecordedLocality
import Yulang.GeneralDictionaryAliasTreeLocality
import Yulang.GeneralDictionaryBranchCoverage
import Yulang.GeneralDictionaryBranchLeaf
import Yulang.GeneralDictionaryBranchOrdinaryCoverage
import Yulang.GeneralDictionaryFiniteJournalJointExample
import Yulang.GeneralDictionaryNamedLocality
import Yulang.GeneralDictionaryNamedLocalityExample
import Yulang.GeneralDictionaryTreeCoverage
import Yulang.GeneralDictionaryTreeLeaf
import Yulang.GeneralNominalBranchExample
import Yulang.GeneralNominalBranchFacts
import Yulang.GeneralNominalBranchProjection
import Yulang.GeneralNominalTreeExample
import Yulang.GeneralNominalTreeFacts
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : List Name := [`Yulang.GeneralDictionaryAliasMixedLocality, `Yulang.GeneralDictionaryAliasRecordedLocality, `Yulang.GeneralDictionaryAliasTreeLocality, `Yulang.GeneralDictionaryBranchCoverage, `Yulang.GeneralDictionaryBranchLeaf, `Yulang.GeneralDictionaryBranchOrdinaryCoverage, `Yulang.GeneralDictionaryFiniteJournalJointExample, `Yulang.GeneralDictionaryNamedLocality, `Yulang.GeneralDictionaryNamedLocalityExample, `Yulang.GeneralDictionaryTreeCoverage, `Yulang.GeneralDictionaryTreeLeaf, `Yulang.GeneralNominalBranchExample, `Yulang.GeneralNominalBranchFacts, `Yulang.GeneralNominalBranchProjection, `Yulang.GeneralNominalTreeExample, `Yulang.GeneralNominalTreeFacts]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        for dependency in (← collectAxioms name) do
          unless allowed.contains dependency do
            throwError "FOCUSED-AXIOM-FAIL: {name}: {dependency}"
  if checked = 0 then throwError "empty audit"
  logInfo m!"FOCUSED-AXIOM-PASS: {checked} declarations in cycle150 modules"

```

## Diff-only gate
`tools/verify-lean.sh . origin/integration/m1-final --no-build`
exit0
```text
verify-lean: . @ 57477cf72 (base origin/integration/m1-final)
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
