import Yulang.GeneralNominalOrderedSupport248
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralNominalOrderedSupport248]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE248-CHECKPOINT-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE248-CHECKPOINT-FAIL: empty audit"
 logInfo m!"CYCLE248-CHECKPOINT-PASS: {checked} constants in {modules.size} modules"
