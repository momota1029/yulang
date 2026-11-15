import Yulang.GeneralDictionaryDefaultComposition211
import Yulang.GeneralDictionaryDefaultFreshProbe211Conflict
import Yulang.GeneralDictionaryDefaultFreshProbe211Install
import Yulang.GeneralDictionaryDefaultFreshProbe211Refutation
import Yulang.GeneralDictionaryDefaultFreshProbe211Source
import Yulang.GeneralDictionaryDefaultFreshProbe211Stable
import Yulang.GeneralDictionaryDefaultFreshProbe211State
import Yulang.GeneralDictionaryDefaultRegistered211
import Yulang.GeneralDictionaryDefaultSelectedGeneration211
import Yulang.GeneralDictionaryDefaultSoundness211
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryDefaultComposition211, `Yulang.GeneralDictionaryDefaultFreshProbe211Conflict, `Yulang.GeneralDictionaryDefaultFreshProbe211Install, `Yulang.GeneralDictionaryDefaultFreshProbe211Refutation, `Yulang.GeneralDictionaryDefaultFreshProbe211Source, `Yulang.GeneralDictionaryDefaultFreshProbe211Stable, `Yulang.GeneralDictionaryDefaultFreshProbe211State, `Yulang.GeneralDictionaryDefaultRegistered211, `Yulang.GeneralDictionaryDefaultSelectedGeneration211, `Yulang.GeneralDictionaryDefaultSoundness211]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if modules.contains moduleName then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE211-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE211-GATE-FAIL: no constants checked"
  logInfo m!"CYCLE211-GATE-PASS: {checked} constants in {modules.size} modules"
