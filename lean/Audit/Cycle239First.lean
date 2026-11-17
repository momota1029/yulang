import Yulang.GeneralDictionaryCompoundBase239
import Yulang.GeneralDictionaryCompoundRefresh239
import Yulang.GeneralDictionaryCompoundRefreshStep239
import Yulang.GeneralDictionaryCompoundSnapshot239
import Yulang.GeneralDictionaryCompoundTrust239
import Yulang.GeneralDictionaryVersionLoopAtomSupport239
import Yulang.GeneralDictionaryVersionLoopBook239
import Yulang.GeneralDictionaryVersionLoopBookSupport239
import Yulang.GeneralDictionaryVersionLoopFamilyNovel239
import Yulang.GeneralDictionaryVersionLoopFrame239
import Yulang.GeneralDictionaryVersionLoopFresh239
import Yulang.GeneralDictionaryVersionLoopPacketSupport239
import Yulang.GeneralDictionaryVersionLoopPatched239
import Yulang.GeneralDictionaryVersionLoopStage239
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Yulang.GeneralDictionaryCompoundBase239, `Yulang.GeneralDictionaryCompoundRefresh239, `Yulang.GeneralDictionaryCompoundRefreshStep239, `Yulang.GeneralDictionaryCompoundSnapshot239, `Yulang.GeneralDictionaryCompoundTrust239, `Yulang.GeneralDictionaryVersionLoopAtomSupport239, `Yulang.GeneralDictionaryVersionLoopBook239, `Yulang.GeneralDictionaryVersionLoopBookSupport239, `Yulang.GeneralDictionaryVersionLoopFamilyNovel239, `Yulang.GeneralDictionaryVersionLoopFrame239, `Yulang.GeneralDictionaryVersionLoopFresh239, `Yulang.GeneralDictionaryVersionLoopPacketSupport239, `Yulang.GeneralDictionaryVersionLoopPatched239, `Yulang.GeneralDictionaryVersionLoopStage239]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      if modules.contains environment.header.moduleNames[index.toNat]! then
        checked := checked + 1
        let axioms ← collectAxioms name
        for dependency in axioms do
          unless allowed.contains dependency do
            throwError "CYCLE239-FIRST-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "CYCLE239-FIRST-FAIL: no constants checked"
  logInfo m!"CYCLE239-FIRST-PASS: {checked} constants in {modules.size} modules"
