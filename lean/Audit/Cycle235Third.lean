import Yulang.GeneralDictionaryMixedGround218Leaf235
import Yulang.GeneralDictionaryMixedGround218Fresh235
import Yulang.GeneralDictionaryMixedGround218Cycles235
import Yulang.GeneralDictionaryMixedGround218LeafFrame235
import Yulang.GeneralDictionaryMixedGround218Safety235
import Yulang.GeneralDictionaryMixedGround218Rejection235
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryMixedGround218Leaf235,`Yulang.GeneralDictionaryMixedGround218Fresh235,`Yulang.GeneralDictionaryMixedGround218Cycles235,`Yulang.GeneralDictionaryMixedGround218LeafFrame235,`Yulang.GeneralDictionaryMixedGround218Safety235,`Yulang.GeneralDictionaryMixedGround218Rejection235]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE235-THIRD-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE235-THIRD-FAIL: no constants checked"
  logInfo m!"CYCLE235-THIRD-PASS: {checked} constants in {modules.size} modules"
