import Yulang.GeneralDictionaryCompoundChild239
import Yulang.GeneralDictionaryCompoundFailure239
import Yulang.GeneralDictionaryCompoundNoInstance239
import Yulang.GeneralDictionaryCompoundObstruction239
import Yulang.GeneralDictionaryCompoundRoot239
import Yulang.GeneralDictionaryCompoundVacuity239
import Yulang.GeneralDictionaryVersionLoopInstall239
import Yulang.GeneralDictionaryVersionLoopIteration239
import Yulang.GeneralDictionaryVersionLoopNontermination239
import Yulang.GeneralDictionaryVersionLoopRound239
import Yulang.GeneralDictionaryVersionLoopSafety239
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCompoundChild239, `Yulang.GeneralDictionaryCompoundFailure239, `Yulang.GeneralDictionaryCompoundNoInstance239, `Yulang.GeneralDictionaryCompoundObstruction239, `Yulang.GeneralDictionaryCompoundRoot239, `Yulang.GeneralDictionaryCompoundVacuity239, `Yulang.GeneralDictionaryVersionLoopInstall239, `Yulang.GeneralDictionaryVersionLoopIteration239, `Yulang.GeneralDictionaryVersionLoopNontermination239, `Yulang.GeneralDictionaryVersionLoopRound239, `Yulang.GeneralDictionaryVersionLoopSafety239]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE239-SECOND-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE239-SECOND-FAIL: no constants checked"
  logInfo m!"CYCLE239-SECOND-PASS: {checked} constants in {modules.size} modules"
