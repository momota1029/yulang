import Yulang.GeneralFiniteAssignment246
import Yulang.GeneralPresenceConsumerSupport246
import Yulang.GeneralPresenceGuardedBlock246
import Yulang.GeneralPresenceGuardedLayer246
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralFiniteAssignment246, `Yulang.GeneralPresenceConsumerSupport246, `Yulang.GeneralPresenceGuardedBlock246, `Yulang.GeneralPresenceGuardedLayer246]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE246-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE246-FAIL: empty audit"
 logInfo m!"CYCLE246-PASS: {checked} constants in {modules.size} modules"
