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
import Yulang.GeneralPresenceOrderedAllocation247
import Yulang.GeneralPresenceOrderedBlock247
import Yulang.GeneralPresenceOrderedCheck247
import Yulang.GeneralPresenceOrderedCoherentAdapter247
import Yulang.GeneralPresenceOrderedCycleLimit247
import Yulang.GeneralPresenceOrderedDedup247
import Yulang.GeneralPresenceOrderedDependence247
import Yulang.GeneralPresenceOrderedPrepared247
import Yulang.GeneralPresenceOrderedQueries247
import Yulang.GeneralPresenceOrderedQueryLimit247
import Yulang.GeneralPresenceOrderedRebase247
import Yulang.GeneralPresenceOrderedRebaseExample247
import Yulang.GeneralPresenceOrderedRecovery247
import Yulang.GeneralPresenceOrderedRefreshSequence247
import Yulang.GeneralPresenceOrderedRefreshSyntax247
import Yulang.GeneralPresenceOrderedRewriteAbsorption247
import Yulang.GeneralPresenceOrderedSort247
import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceOrderedSupport247
import Yulang.GeneralPresenceOrderedSyntax247
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralPresenceGuardedAbsorption247, `Yulang.GeneralPresenceGuardedAllocation247, `Yulang.GeneralPresenceGuardedCommutation247, `Yulang.GeneralPresenceGuardedCompression247, `Yulang.GeneralPresenceGuardedConsumers247, `Yulang.GeneralPresenceGuardedEnvironment247, `Yulang.GeneralPresenceGuardedExamples247, `Yulang.GeneralPresenceGuardedRebase247, `Yulang.GeneralPresenceGuardedRebaseExample247, `Yulang.GeneralPresenceGuardedRecovery247, `Yulang.GeneralPresenceOrderedAllocation247, `Yulang.GeneralPresenceOrderedBlock247, `Yulang.GeneralPresenceOrderedCheck247, `Yulang.GeneralPresenceOrderedCoherentAdapter247, `Yulang.GeneralPresenceOrderedCycleLimit247, `Yulang.GeneralPresenceOrderedDedup247, `Yulang.GeneralPresenceOrderedDependence247, `Yulang.GeneralPresenceOrderedPrepared247, `Yulang.GeneralPresenceOrderedQueries247, `Yulang.GeneralPresenceOrderedQueryLimit247, `Yulang.GeneralPresenceOrderedRebase247, `Yulang.GeneralPresenceOrderedRebaseExample247, `Yulang.GeneralPresenceOrderedRecovery247, `Yulang.GeneralPresenceOrderedRefreshSequence247, `Yulang.GeneralPresenceOrderedRefreshSyntax247, `Yulang.GeneralPresenceOrderedRewriteAbsorption247, `Yulang.GeneralPresenceOrderedSort247, `Yulang.GeneralPresenceOrderedSubstitution247, `Yulang.GeneralPresenceOrderedSupport247, `Yulang.GeneralPresenceOrderedSyntax247]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE247-FINAL-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE247-FINAL-FAIL: empty audit"
 logInfo m!"CYCLE247-FINAL-PASS: {checked} constants in {modules.size} modules"
