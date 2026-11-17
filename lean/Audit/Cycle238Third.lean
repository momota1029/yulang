import Yulang.GeneralNominalSchemaCongruence238
import Yulang.GeneralNominalVersionedPacketCongruence238
import Yulang.GeneralNominalVersionedEffectCongruence238
import Yulang.GeneralNominalVersionedSourceCongruence238
import Yulang.GeneralDictionaryCompoundReplay238
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralNominalSchemaCongruence238, `Yulang.GeneralNominalVersionedPacketCongruence238, `Yulang.GeneralNominalVersionedEffectCongruence238, `Yulang.GeneralNominalVersionedSourceCongruence238, `Yulang.GeneralDictionaryCompoundReplay238]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE238-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE238-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE238-THIRD-PASS: {checked} constants in {modules.size} modules"
