import Yulang.GeneralNominalOrderedPacketModels248
import Yulang.GeneralNominalOrderedBundle248
import Yulang.GeneralNominalOrderedSupport248
import Yulang.GeneralNominalOrderedMerge248
import Yulang.GeneralNominalOrderedInitial248
import Yulang.GeneralNominalOrderedRaw248
import Yulang.GeneralNominalOrderedLive248
import Yulang.GeneralNominalOrderedViewSyntax248
import Yulang.GeneralNominalOrderedOrigin248
import Yulang.GeneralNominalOrderedPacket248
import Yulang.GeneralNominalOrderedMergeExample248
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let modules := #[`Yulang.GeneralNominalOrderedPacketModels248, `Yulang.GeneralNominalOrderedBundle248, `Yulang.GeneralNominalOrderedSupport248, `Yulang.GeneralNominalOrderedMerge248, `Yulang.GeneralNominalOrderedInitial248, `Yulang.GeneralNominalOrderedRaw248, `Yulang.GeneralNominalOrderedLive248, `Yulang.GeneralNominalOrderedViewSyntax248, `Yulang.GeneralNominalOrderedOrigin248, `Yulang.GeneralNominalOrderedPacket248, `Yulang.GeneralNominalOrderedMergeExample248]
 let mut checked : Nat := 0
 for (name, _) in environment.constants.toList do
  if let some index := environment.getModuleIdxFor? name then
   if modules.contains environment.header.moduleNames[index.toNat]! then
    checked := checked + 1
    for dependency in ← collectAxioms name do
     unless allowed.contains dependency do
      throwError "CYCLE248-PHASE3-FAIL: {name} depends on {dependency}"
 if checked = 0 then throwError "CYCLE248-PHASE3-FAIL: empty audit"
 logInfo m!"CYCLE248-PHASE3-PASS: {checked} constants in {modules.size} modules"
