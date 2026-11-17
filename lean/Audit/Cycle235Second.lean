import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
import Yulang.GeneralNominalVersionedMixedCurrentEvidence235
import Yulang.GeneralNominalVersionedMixedEvidenceReduction235
import Yulang.GeneralNominalVersionedMixedFrameSelection235
import Yulang.GeneralNominalVersionedMixedGuardReduction235
import Yulang.GeneralNominalVersionedMixedSelectedEffect235
import Yulang.GeneralNominalVersionedMixedSelectedFrame235
import Yulang.GeneralNominalVersionedMixedStableEvidence235
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalVersionedMixedCurrentCandidate235,`Yulang.GeneralNominalVersionedMixedCurrentEvidence235,`Yulang.GeneralNominalVersionedMixedEvidenceReduction235,`Yulang.GeneralNominalVersionedMixedFrameSelection235,`Yulang.GeneralNominalVersionedMixedGuardReduction235,`Yulang.GeneralNominalVersionedMixedSelectedEffect235,`Yulang.GeneralNominalVersionedMixedSelectedFrame235,`Yulang.GeneralNominalVersionedMixedStableEvidence235]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE235-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE235-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE235-SECOND-PASS: {checked} constants in {modules.size} modules"
