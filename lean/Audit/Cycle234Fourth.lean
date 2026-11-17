import Yulang.GeneralDictionaryMixedGround218Frame234
import Yulang.GeneralDictionaryMixedGround218Install234
import Yulang.GeneralDictionaryMixedGround218Obstruction234
import Yulang.GeneralDictionaryMixedGround218Packet234
import Yulang.GeneralNominalVersionedSupportUnion234
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedGround218Frame234,`Yulang.GeneralDictionaryMixedGround218Install234,`Yulang.GeneralDictionaryMixedGround218Obstruction234,`Yulang.GeneralDictionaryMixedGround218Packet234,`Yulang.GeneralNominalVersionedSupportUnion234]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE234-FOURTH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE234-FOURTH-FAIL: no constants checked"
  logInfo m!"CYCLE234-FOURTH-PASS: {checked} constants in {modules.size} modules"
