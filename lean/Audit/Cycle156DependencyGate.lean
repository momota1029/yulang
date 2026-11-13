import Yulang.GeneralDictionaryCatalogEvidence
import Yulang.GeneralDictionaryCatalogMultiArgumentEvidence
import Yulang.GeneralDictionaryCollectedRequests
import Yulang.GeneralDictionaryMultiArgumentCoverage
import Yulang.GeneralDictionaryMultiScalarExample
import Yulang.GeneralDictionaryMultiScalarInspection
import Yulang.GeneralDictionaryProvenanceMultiScalarBranch
import Yulang.GeneralDictionaryReachableRequestHistory
import Yulang.GeneralDictionaryReservedCatalogEvidence
import Yulang.GeneralDictionaryReservedCollectedHistory
import Yulang.GeneralDictionaryReservedCompletedRun
import Yulang.GeneralDictionaryReservedRefreshedClassification
import Yulang.GeneralDictionaryReservedRefreshedStability
import Yulang.GeneralDictionaryReachableRootIntervals
import Yulang.GeneralDictionaryScalarIntervalInspection
import Yulang.GeneralDictionaryProvenanceScalarIntervalRoot
import Yulang.GeneralDictionaryCatalogScalarIntervalRoot
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryCatalogScalarIntervalRoot, `Yulang.GeneralDictionaryCatalogEvidence, `Yulang.GeneralDictionaryCatalogMultiArgumentEvidence, `Yulang.GeneralDictionaryCollectedRequests, `Yulang.GeneralDictionaryMultiArgumentCoverage, `Yulang.GeneralDictionaryMultiScalarExample, `Yulang.GeneralDictionaryMultiScalarInspection, `Yulang.GeneralDictionaryProvenanceMultiScalarBranch, `Yulang.GeneralDictionaryReachableRequestHistory, `Yulang.GeneralDictionaryReservedCatalogEvidence, `Yulang.GeneralDictionaryReservedCollectedHistory, `Yulang.GeneralDictionaryReservedCompletedRun, `Yulang.GeneralDictionaryReservedRefreshedClassification, `Yulang.GeneralDictionaryReservedRefreshedStability, `Yulang.GeneralDictionaryReachableRootIntervals, `Yulang.GeneralDictionaryScalarIntervalInspection, `Yulang.GeneralDictionaryProvenanceScalarIntervalRoot]
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
