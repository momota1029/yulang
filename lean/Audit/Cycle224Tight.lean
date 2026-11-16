import Yulang.GeneralDictionaryTightProjection224
import Yulang.GeneralDictionaryTightPacket224
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryTightProjection224,`Yulang.GeneralDictionaryTightPacket224]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE224-TIGHT-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE224-TIGHT-FAIL: no constants checked"
  logInfo m!"CYCLE224-TIGHT-PASS: {checked} constants in {modules.size} modules"
