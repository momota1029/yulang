import Yulang.B4TargetV8
import Yulang.B4SkeletonV8
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.B4TargetV8, `Yulang.B4SkeletonV8]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE220-TARGET-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE220-TARGET-FAIL: no constants checked"
  logInfo m!"CYCLE220-TARGET-PASS: {checked} constants in {modules.size} modules"
