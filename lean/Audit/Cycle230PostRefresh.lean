import Yulang.GeneralDictionaryUpper230Models
import Yulang.GeneralDictionaryUpper230Support
import Yulang.GeneralDictionaryUpper230Current
import Yulang.GeneralDictionaryUpper230Raw
import Yulang.GeneralDictionaryUpper230Prepared
import Yulang.GeneralDictionaryUpper230Safety
import Yulang.GeneralDictionaryUpper230Selected
import Yulang.GeneralDictionaryUpper230Administrative
import Yulang.GeneralDictionaryUpper230Joint
import Yulang.GeneralDictionaryUpper230Closure
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryUpper230Models,`Yulang.GeneralDictionaryUpper230Support,`Yulang.GeneralDictionaryUpper230Current,`Yulang.GeneralDictionaryUpper230Raw,`Yulang.GeneralDictionaryUpper230Prepared,`Yulang.GeneralDictionaryUpper230Safety,`Yulang.GeneralDictionaryUpper230Selected,`Yulang.GeneralDictionaryUpper230Administrative,`Yulang.GeneralDictionaryUpper230Joint,`Yulang.GeneralDictionaryUpper230Closure]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE230-POSTREFRESH-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE230-POSTREFRESH-FAIL: no constants checked"
  logInfo m!"CYCLE230-POSTREFRESH-PASS: {checked} constants in {modules.size} modules"
