import Yulang.GeneralDictionaryCapturedScalarRefresh
import Yulang.GeneralDictionaryCapturedTrustedBoundary
import Yulang.GeneralDictionarySharedCapturedConsequences
import Yulang.GeneralDictionarySharedCapturedNovelty
import Yulang.GeneralDictionarySharedCapturedPreparation
import Yulang.GeneralDictionarySharedCapturedProducerEnabled
import Yulang.GeneralDictionarySharedCapturedProducerEvidence
import Yulang.GeneralDictionarySharedCapturedProducerGuard
import Yulang.GeneralDictionarySharedCapturedProducerResolution
import Yulang.GeneralDictionarySharedCapturedResumption
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let wanted : List Name := [`Yulang.GeneralDictionaryCapturedScalarRefresh, `Yulang.GeneralDictionaryCapturedTrustedBoundary, `Yulang.GeneralDictionarySharedCapturedConsequences, `Yulang.GeneralDictionarySharedCapturedNovelty, `Yulang.GeneralDictionarySharedCapturedPreparation, `Yulang.GeneralDictionarySharedCapturedProducerEnabled, `Yulang.GeneralDictionarySharedCapturedProducerEvidence, `Yulang.GeneralDictionarySharedCapturedProducerGuard, `Yulang.GeneralDictionarySharedCapturedProducerResolution, `Yulang.GeneralDictionarySharedCapturedResumption]
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
