import Yulang.GeneralDictionaryIdentityCurrentEvidence
import Yulang.GeneralDictionaryIdentityEvidenceExample
import Yulang.GeneralDictionarySharedCapturedGuards
import Yulang.GeneralDictionarySharedCapturedInstallable
import Yulang.GeneralDictionarySharedCapturedInstallation
import Yulang.GeneralDictionarySharedCapturedModel
import Yulang.GeneralDictionarySharedMetadata
import Yulang.GeneralDictionarySharedOrdinaryHistory
import Yulang.GeneralDictionarySharedSourceRetention
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryIdentityCurrentEvidence, `Yulang.GeneralDictionaryIdentityEvidenceExample, `Yulang.GeneralDictionarySharedCapturedGuards, `Yulang.GeneralDictionarySharedCapturedInstallable, `Yulang.GeneralDictionarySharedCapturedInstallation, `Yulang.GeneralDictionarySharedCapturedModel, `Yulang.GeneralDictionarySharedMetadata, `Yulang.GeneralDictionarySharedOrdinaryHistory, `Yulang.GeneralDictionarySharedSourceRetention]
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
