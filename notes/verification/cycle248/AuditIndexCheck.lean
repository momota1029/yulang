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
 let e ← getEnv
 for name in [``Yulang.GeneralNominalOrderedSupport248.row_sources, ``Yulang.GeneralNominalOrderedMerge248.prepared, ``Yulang.GeneralNominalOrderedBundle248.public_models_iff] do
  let idx := e.getModuleIdxFor? name
  logInfo m!"NAME {name} IDX {idx} MOD {idx.map (fun i => e.header.moduleNames[i.toNat]!)}"
 for (name, _) in e.constants.toList do
  if let some index := e.getModuleIdxFor? name then
   if e.header.moduleNames[index.toNat]! == `Yulang.GeneralNominalOrderedSupport248 then
    logInfo m!"SUPPORT {name}"
