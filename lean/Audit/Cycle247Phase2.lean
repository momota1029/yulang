import Yulang.GeneralPresenceGuardedAbsorption247
import Yulang.GeneralPresenceGuardedAllocation247
import Yulang.GeneralPresenceGuardedCommutation247
import Yulang.GeneralPresenceGuardedCompression247
import Yulang.GeneralPresenceGuardedConsumers247
import Yulang.GeneralPresenceGuardedEnvironment247
import Yulang.GeneralPresenceGuardedExamples247
import Yulang.GeneralPresenceGuardedRebase247
import Yulang.GeneralPresenceGuardedRebaseExample247
import Yulang.GeneralPresenceGuardedRecovery247
import Yulang.GeneralPresenceOrderedBlock247
import Yulang.GeneralPresenceOrderedCheck247
import Yulang.GeneralPresenceOrderedDependence247
import Yulang.GeneralPresenceOrderedRebase247
import Yulang.GeneralPresenceOrderedRecovery247
import Yulang.GeneralPresenceOrderedSubstitution247
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralPresenceGuardedAbsorption247, `Yulang.GeneralPresenceGuardedAllocation247, `Yulang.GeneralPresenceGuardedCommutation247, `Yulang.GeneralPresenceGuardedCompression247, `Yulang.GeneralPresenceGuardedConsumers247, `Yulang.GeneralPresenceGuardedEnvironment247, `Yulang.GeneralPresenceGuardedExamples247, `Yulang.GeneralPresenceGuardedRebase247, `Yulang.GeneralPresenceGuardedRebaseExample247, `Yulang.GeneralPresenceGuardedRecovery247, `Yulang.GeneralPresenceOrderedBlock247, `Yulang.GeneralPresenceOrderedCheck247, `Yulang.GeneralPresenceOrderedDependence247, `Yulang.GeneralPresenceOrderedRebase247, `Yulang.GeneralPresenceOrderedRecovery247, `Yulang.GeneralPresenceOrderedSubstitution247]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE247-PHASE2-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE247-PHASE2-FAIL: empty audit"
 logInfo m!"CYCLE247-PHASE2-PASS: {checked} constants in {modules.size} modules"
