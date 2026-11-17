import Yulang.GeneralPresenceAbsorb245
import Yulang.GeneralPresenceCheckClosureLimit245
import Yulang.GeneralPresenceCommonLaws245
import Yulang.GeneralPresenceCommonObserved245
import Yulang.GeneralPresenceGuardedBlockLimit245
import Yulang.GeneralPresenceModelCongruence245
import Yulang.GeneralPresenceModelExtension245
import Yulang.GeneralPresenceObservedPlan245
import Yulang.GeneralPresencePlanTerminationLimit245
import Yulang.GeneralPresencePreorderExtension245
import Yulang.GeneralPresenceQueryTransport245
import Yulang.GeneralPresenceRankedTable245
import Yulang.GeneralPresenceReadback245
import Yulang.GeneralPresenceReadbackLimit245
import Yulang.GeneralPresenceRebaseExample245
import Yulang.GeneralPresenceRebasePlan245
import Yulang.GeneralPresenceUsedSupport245
import Yulang.GeneralPresenceUsedTable245
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralPresenceAbsorb245, `Yulang.GeneralPresenceCheckClosureLimit245, `Yulang.GeneralPresenceCommonLaws245, `Yulang.GeneralPresenceCommonObserved245, `Yulang.GeneralPresenceGuardedBlockLimit245, `Yulang.GeneralPresenceModelCongruence245, `Yulang.GeneralPresenceModelExtension245, `Yulang.GeneralPresenceObservedPlan245, `Yulang.GeneralPresencePlanTerminationLimit245, `Yulang.GeneralPresencePreorderExtension245, `Yulang.GeneralPresenceQueryTransport245, `Yulang.GeneralPresenceRankedTable245, `Yulang.GeneralPresenceReadback245, `Yulang.GeneralPresenceReadbackLimit245, `Yulang.GeneralPresenceRebaseExample245, `Yulang.GeneralPresenceRebasePlan245, `Yulang.GeneralPresenceUsedSupport245, `Yulang.GeneralPresenceUsedTable245]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE245-OBSERVED-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE245-OBSERVED-FAIL: empty audit"
 logInfo m!"CYCLE245-OBSERVED-PASS: {checked} constants in {modules.size} modules"
