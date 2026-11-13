import Yulang.GeneralDictionaryBindingSchemaReplay
import Yulang.GeneralDictionaryCapturedChildIntervals
import Yulang.GeneralDictionaryCapturedSchemaTransport
import Yulang.GeneralDictionaryComputedCatalogExample
import Yulang.GeneralDictionaryGeneratedIntervalCoverage
import Yulang.GeneralDictionaryGeneratedIntervalExample
import Yulang.GeneralDictionaryGeneratedIntervals
import Yulang.GeneralDictionaryGeneratedOrigins
import Yulang.GeneralDictionaryMixedCapturedReplay
import Yulang.GeneralDictionaryMixedCarrierRefresh
import Yulang.GeneralDictionaryMixedCatalogExample
import Yulang.GeneralDictionaryMixedCatalogInhabited
import Yulang.GeneralDictionaryMixedCatalogReachable
import Yulang.GeneralDictionaryPersistentCatalog
import Yulang.GeneralDictionaryProvenanceGeneratedIntervals
import Yulang.GeneralDictionaryRecordedScalarIntervalEvidence
import Yulang.GeneralDictionaryRequestCatalog
import Yulang.GeneralDictionaryRequestCatalogCompute
import Yulang.GeneralDictionaryRequestCatalogEvidence
import Yulang.GeneralDictionaryVariableClauseCatalog
import Yulang.GeneralDictionaryVariableClauseCatalogExample
import Yulang.GeneralDictionaryVariableRegistryIntervals
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryBindingSchemaReplay, `Yulang.GeneralDictionaryCapturedChildIntervals, `Yulang.GeneralDictionaryCapturedSchemaTransport, `Yulang.GeneralDictionaryComputedCatalogExample, `Yulang.GeneralDictionaryGeneratedIntervalCoverage, `Yulang.GeneralDictionaryGeneratedIntervalExample, `Yulang.GeneralDictionaryGeneratedIntervals, `Yulang.GeneralDictionaryGeneratedOrigins, `Yulang.GeneralDictionaryMixedCapturedReplay, `Yulang.GeneralDictionaryMixedCarrierRefresh, `Yulang.GeneralDictionaryMixedCatalogExample, `Yulang.GeneralDictionaryMixedCatalogInhabited, `Yulang.GeneralDictionaryMixedCatalogReachable, `Yulang.GeneralDictionaryPersistentCatalog, `Yulang.GeneralDictionaryProvenanceGeneratedIntervals, `Yulang.GeneralDictionaryRecordedScalarIntervalEvidence, `Yulang.GeneralDictionaryRequestCatalog, `Yulang.GeneralDictionaryRequestCatalogCompute, `Yulang.GeneralDictionaryRequestCatalogEvidence, `Yulang.GeneralDictionaryVariableClauseCatalog, `Yulang.GeneralDictionaryVariableClauseCatalogExample, `Yulang.GeneralDictionaryVariableRegistryIntervals]
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
