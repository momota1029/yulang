import Yulang.GeneralNominalVersionedCache232
import Yulang.GeneralNominalVersionedKernelCache232
import Yulang.GeneralNominalVersionedSourceInvariants232
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalVersionedCache232,`Yulang.GeneralNominalVersionedKernelCache232,`Yulang.GeneralNominalVersionedSourceInvariants232]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE232-FINAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE232-FINAL-FAIL: no constants checked"
  logInfo m!"CYCLE232-FINAL-PASS: {checked} constants in {modules.size} modules"
