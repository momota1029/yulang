import Yulang.GeneralNominalAcyclicEquations237
import Yulang.GeneralNominalExpressionIntervals237
import Yulang.GeneralNominalModeCompiler237
import Yulang.GeneralNominalModeIntervals237
import Yulang.GeneralNominalModePattern237
import Yulang.GeneralNominalVersionedChildClosure237
import Yulang.GeneralNominalVersionedChildIntervals237
import Yulang.GeneralNominalVersionedHistoryEquations237
import Yulang.GeneralNominalVersionedInvocationPool237
import Yulang.GeneralNominalVersionedMixedCenters237
import Yulang.GeneralNominalVersionedMixedSeedLedger237
import Yulang.GeneralNominalVersionedSupportedActual237
import Yulang.GeneralNominalVersionedSupportedCurrentHead237
import Yulang.GeneralNominalVersionedSupportedHead237
import Yulang.GeneralNominalVersionedTraceSiteSupport237
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalAcyclicEquations237, `Yulang.GeneralNominalExpressionIntervals237, `Yulang.GeneralNominalModeCompiler237, `Yulang.GeneralNominalModeIntervals237, `Yulang.GeneralNominalModePattern237, `Yulang.GeneralNominalVersionedChildClosure237, `Yulang.GeneralNominalVersionedChildIntervals237, `Yulang.GeneralNominalVersionedHistoryEquations237, `Yulang.GeneralNominalVersionedInvocationPool237, `Yulang.GeneralNominalVersionedMixedCenters237, `Yulang.GeneralNominalVersionedMixedSeedLedger237, `Yulang.GeneralNominalVersionedSupportedActual237, `Yulang.GeneralNominalVersionedSupportedCurrentHead237, `Yulang.GeneralNominalVersionedSupportedHead237, `Yulang.GeneralNominalVersionedTraceSiteSupport237]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE237-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE237-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE237-SECOND-PASS: {checked} constants in {modules.size} modules"
