import Yulang.GeneralNominalVersionedMixedHistory235
import Yulang.GeneralNominalVersionedMixedPlanLedger235
import Yulang.GeneralNominalVersionedMixedReady235
import Yulang.GeneralNominalVersionedMixedRoles235
import Yulang.GeneralNominalVersionedMixedStableLaws235
import Yulang.GeneralNominalVersionedMixedTrace235
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalVersionedMixedHistory235,`Yulang.GeneralNominalVersionedMixedPlanLedger235,`Yulang.GeneralNominalVersionedMixedReady235,`Yulang.GeneralNominalVersionedMixedRoles235,`Yulang.GeneralNominalVersionedMixedStableLaws235,`Yulang.GeneralNominalVersionedMixedTrace235]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE235-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE235-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE235-FIRST-PASS: {checked} constants in {modules.size} modules"
