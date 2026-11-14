import Yulang.GeneralNominalHeadLeafPlan189
import Yulang.GeneralNominalInitialFrameUnique189
import Yulang.GeneralNominalInitialLeafEvidence189
import Yulang.GeneralNominalInitialLeafFixture189
import Yulang.GeneralNominalInitialLeafLocal189
import Yulang.GeneralNominalInitialLeafNonvacuity189
import Yulang.GeneralNominalInitialLeafStep189
import Yulang.GeneralNominalInitialNamedEvidence189
import Yulang.GeneralNominalInitialNamedFixture189
import Yulang.GeneralNominalInitialNamedLocal189
import Yulang.GeneralNominalInitialNamedNonvacuity189
import Yulang.GeneralNominalInitialOutputExact189
import Yulang.GeneralNominalLinearNamedEvidence189
import Yulang.GeneralNominalLinearNamedPlan189
import Yulang.GeneralNominalLinearVariableModels189
import Yulang.GeneralNominalOutputCoverage189
import Yulang.GeneralNominalSingleVariableModels189
import Yulang.GeneralNominalSourceVariableEvidence189
import Yulang.GeneralNominalSourceVariableInstall189
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.endsWith "189" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked == 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations including generated/private"
