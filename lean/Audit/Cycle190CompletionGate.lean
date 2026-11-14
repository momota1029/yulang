import Yulang.GeneralNominalRepeatedSuccessor190
import Yulang.GeneralNominalRepeatedLocal190
import Yulang.GeneralNominalInstallationBoundary190
import Yulang.GeneralNominalLeafWitnessInstall190
import Yulang.GeneralNominalAvailableNonvacuity190
import Yulang.GeneralNominalRepeatedPointRepair190
import Yulang.GeneralNominalRepeatedNamedPlan190
import Yulang.GeneralNominalSourceRepeatedEvidence190
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "190" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations including generated/private"
