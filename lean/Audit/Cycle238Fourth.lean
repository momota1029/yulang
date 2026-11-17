import Yulang.GeneralDictionaryVersionLoopFamilyBase238
import Yulang.GeneralDictionaryVersionLoopFamilySnapshot238
import Yulang.GeneralDictionaryVersionLoopFamilyPacket238
import Yulang.GeneralDictionaryVersionLoopFamilyHead238
import Yulang.GeneralDictionaryVersionLoopFamilyFull238
import Yulang.GeneralDictionaryVersionLoopFamilyRefines238
import Yulang.GeneralDictionaryVersionLoopFamilyFresh238
import Yulang.GeneralDictionaryVersionLoopFamilyRevision238
import Yulang.GeneralDictionaryVersionLoopFamilyBack238
import Yulang.GeneralDictionaryCompoundSites238
import Yulang.GeneralDictionaryCompoundNoInstance238
import Yulang.GeneralDictionaryCompoundPointModel238
import Yulang.GeneralDictionaryCompoundPointHead238
import Yulang.GeneralDictionaryCompoundPrepared238
import Yulang.GeneralDictionaryCompoundOperational238
import Yulang.GeneralDictionaryCompoundFeasible238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryVersionLoopFamilyBase238, `Yulang.GeneralDictionaryVersionLoopFamilySnapshot238, `Yulang.GeneralDictionaryVersionLoopFamilyPacket238, `Yulang.GeneralDictionaryVersionLoopFamilyHead238, `Yulang.GeneralDictionaryVersionLoopFamilyFull238, `Yulang.GeneralDictionaryVersionLoopFamilyRefines238, `Yulang.GeneralDictionaryVersionLoopFamilyFresh238, `Yulang.GeneralDictionaryVersionLoopFamilyRevision238, `Yulang.GeneralDictionaryVersionLoopFamilyBack238, `Yulang.GeneralDictionaryCompoundSites238, `Yulang.GeneralDictionaryCompoundNoInstance238, `Yulang.GeneralDictionaryCompoundPointModel238, `Yulang.GeneralDictionaryCompoundPointHead238, `Yulang.GeneralDictionaryCompoundPrepared238, `Yulang.GeneralDictionaryCompoundOperational238, `Yulang.GeneralDictionaryCompoundFeasible238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE238-FOURTH-PASS: {checked} constants in {modules.size} modules"
