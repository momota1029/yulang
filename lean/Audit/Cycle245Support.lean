import Yulang.GeneralPresenceCheckClosureLimit245
import Yulang.GeneralPresenceRankedTable245
import Yulang.GeneralPresenceReadback245
import Yulang.GeneralPresenceReadbackLimit245
import Yulang.GeneralPresenceUsedSupport245
import Yulang.GeneralPresenceUsedTable245
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralPresenceCheckClosureLimit245, `Yulang.GeneralPresenceRankedTable245, `Yulang.GeneralPresenceReadback245, `Yulang.GeneralPresenceReadbackLimit245, `Yulang.GeneralPresenceUsedSupport245, `Yulang.GeneralPresenceUsedTable245]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE245-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE245-FAIL: empty audit"
 logInfo m!"CYCLE245-PASS: {checked} constants in {modules.size} modules"
