import Yulang.GeneralNominalVersionedMixedAdministrative236
import Yulang.GeneralNominalVersionedMixedAdministrativeOrder236
import Yulang.GeneralNominalVersionedMixedProgressSplit236
import Yulang.GeneralNominalVersionedMixedWhere236
import Yulang.GeneralNominalVersionedMixedResolver236
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalVersionedMixedAdministrative236, `Yulang.GeneralNominalVersionedMixedAdministrativeOrder236, `Yulang.GeneralNominalVersionedMixedProgressSplit236, `Yulang.GeneralNominalVersionedMixedWhere236, `Yulang.GeneralNominalVersionedMixedResolver236]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE236-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE236-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE236-FIRST-PASS: {checked} constants in {modules.size} modules"
