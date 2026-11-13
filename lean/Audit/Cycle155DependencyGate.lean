import Yulang.GeneralDictionaryInstalledRequestProvenance
import Yulang.GeneralDictionaryNonterminalProvenanceApplication
import Yulang.GeneralDictionaryProvenanceClassification
import Yulang.GeneralDictionaryProvenanceHeadBranch
import Yulang.GeneralDictionaryProvenanceScalarBranch
import Yulang.GeneralDictionaryProvenanceTreeBranch
import Yulang.GeneralDictionaryRecordedBatchModels
import Yulang.GeneralDictionaryRecordedTreeBranch
import Yulang.GeneralDictionaryRequestBatchAssembly
import Yulang.GeneralDictionaryRequestProvenance
import Yulang.GeneralDictionaryRequestProvenanceTrace
import Yulang.GeneralDictionaryReservedClassifierSoundness
import Yulang.GeneralDictionaryReservedEqualityStep
import Yulang.GeneralDictionaryReservedInstalledClassification
import Yulang.GeneralDictionaryReservedInstalledEvidence
import Yulang.GeneralDictionaryReservedMixedProvenance
import Yulang.GeneralDictionaryReservedNominalRefresh
import Yulang.GeneralDictionaryReservedOutputEquality
import Yulang.GeneralDictionaryReservedRefreshedEvidence
import Yulang.GeneralDictionaryReservedSuccessorBoundary
import Yulang.GeneralDictionarySelectedProvenanceCoverage
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryInstalledRequestProvenance, `Yulang.GeneralDictionaryNonterminalProvenanceApplication, `Yulang.GeneralDictionaryProvenanceClassification, `Yulang.GeneralDictionaryProvenanceHeadBranch, `Yulang.GeneralDictionaryProvenanceScalarBranch, `Yulang.GeneralDictionaryProvenanceTreeBranch, `Yulang.GeneralDictionaryRecordedBatchModels, `Yulang.GeneralDictionaryRecordedTreeBranch, `Yulang.GeneralDictionaryRequestBatchAssembly, `Yulang.GeneralDictionaryRequestProvenance, `Yulang.GeneralDictionaryRequestProvenanceTrace, `Yulang.GeneralDictionaryReservedClassifierSoundness, `Yulang.GeneralDictionaryReservedEqualityStep, `Yulang.GeneralDictionaryReservedInstalledClassification, `Yulang.GeneralDictionaryReservedInstalledEvidence, `Yulang.GeneralDictionaryReservedMixedProvenance, `Yulang.GeneralDictionaryReservedNominalRefresh, `Yulang.GeneralDictionaryReservedOutputEquality, `Yulang.GeneralDictionaryReservedRefreshedEvidence, `Yulang.GeneralDictionaryReservedSuccessorBoundary, `Yulang.GeneralDictionarySelectedProvenanceCoverage]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} (module {moduleName}) depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
