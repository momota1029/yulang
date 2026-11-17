import Yulang.GeneralDictionaryLooseIterationNontermination240
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      if env.header.moduleNames[index.toNat]! == `Yulang.GeneralDictionaryLooseIterationNontermination240 then
        checked := checked + 1
        for dependency in (← collectAxioms name) do
          unless allowed.contains dependency do throwError "Unexpected axiom {dependency} in {name}"
  if checked == 0 then throwError "No declarations checked"
  logInfo m!"IndependentNontermination240-PASS: {checked} declarations"
