import Yulang.GeneralDictionaryOptionalCurrent229
import Yulang.GeneralDictionaryOptionalCycles229
import Yulang.GeneralDictionaryOptionalEnable229
import Yulang.GeneralDictionaryOptionalExpression229
import Yulang.GeneralDictionaryOptionalInitial229
import Yulang.GeneralDictionaryOptionalInstall229
import Yulang.GeneralDictionaryOptionalOutput229
import Yulang.GeneralDictionaryOptionalRaw229
import Yulang.GeneralDictionaryOptionalRawStage229
import Yulang.GeneralDictionaryOptionalReachable229
import Yulang.GeneralDictionaryOptionalRegression229
import Yulang.GeneralDictionaryOptionalSelected229
import Yulang.GeneralDictionaryOptionalSource229
import Yulang.GeneralDictionaryOptionalStage229
import Yulang.GeneralDictionaryOptionalStageSafety229
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryOptionalCurrent229,`Yulang.GeneralDictionaryOptionalCycles229,`Yulang.GeneralDictionaryOptionalEnable229,`Yulang.GeneralDictionaryOptionalExpression229,`Yulang.GeneralDictionaryOptionalInitial229,`Yulang.GeneralDictionaryOptionalInstall229,`Yulang.GeneralDictionaryOptionalOutput229,`Yulang.GeneralDictionaryOptionalRaw229,`Yulang.GeneralDictionaryOptionalRawStage229,`Yulang.GeneralDictionaryOptionalReachable229,`Yulang.GeneralDictionaryOptionalRegression229,`Yulang.GeneralDictionaryOptionalSelected229,`Yulang.GeneralDictionaryOptionalSource229,`Yulang.GeneralDictionaryOptionalStage229,`Yulang.GeneralDictionaryOptionalStageSafety229]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE229-OPTIONAL-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE229-OPTIONAL-FAIL: no constants checked"
  logInfo m!"CYCLE229-OPTIONAL-PASS: {checked} constants in {modules.size} modules"
