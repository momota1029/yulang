import Yulang.GeneralDictionarySharedCapturedInputReady
import Yulang.GeneralDictionarySharedCapturedProducer
import Yulang.GeneralDictionaryCapturedAliasCountermodel
import Yulang.GeneralDictionaryCapturedEvidenceDelay
import Yulang.GeneralDictionaryCapturedInputCountermodel
import Yulang.GeneralDictionaryCapturedInstallationBlocked
import Yulang.GeneralDictionaryCapturedSettlementBoundary
import Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence
import Yulang.GeneralDictionarySharedCapturedFinalEvidence
import Yulang.GeneralDictionarySharedCapturedReportTransport
import Yulang.GeneralNominalReportSourceTransport
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryCapturedAliasCountermodel, `Yulang.GeneralDictionaryCapturedEvidenceDelay, `Yulang.GeneralDictionaryCapturedInputCountermodel, `Yulang.GeneralDictionaryCapturedInstallationBlocked, `Yulang.GeneralDictionaryCapturedSettlementBoundary, `Yulang.GeneralDictionarySharedCapturedFinalCurrentEvidence, `Yulang.GeneralDictionarySharedCapturedFinalEvidence, `Yulang.GeneralDictionarySharedCapturedReportTransport, `Yulang.GeneralNominalReportSourceTransport, `Yulang.GeneralDictionarySharedCapturedInputReady, `Yulang.GeneralDictionarySharedCapturedProducer]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if wanted.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "AXIOM-GATE-FAIL: no declarations checked"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations"
