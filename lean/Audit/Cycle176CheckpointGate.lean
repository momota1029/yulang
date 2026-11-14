import Yulang.GeneralDictionaryCenteredCandidate176
import Yulang.GeneralDictionaryCenteredFlexible176
import Yulang.GeneralDictionaryCenteredLedger176
import Yulang.GeneralDictionaryCenteredReady176
import Yulang.GeneralDictionaryCenteredRecorded176
import Yulang.GeneralDictionaryCenteredRegression176
import Yulang.GeneralDictionaryCenteredSharedMerge176
import Yulang.GeneralDictionaryCenteredTree176
import Lean
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in environment.constants.toList do
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.startsWith "Yulang.GeneralDictionary" && moduleName.toString.endsWith "176" then
        checked := checked + 1
        for dependency in ← collectAxioms name do
          unless allowed.contains dependency do
            throwError "AXIOM-GATE-FAIL: {name} depends on {dependency}"
  if checked = 0 then throwError "empty gate"
  logInfo m!"AXIOM-GATE-PASS: {checked} declarations (definitions/private/generated included)"
