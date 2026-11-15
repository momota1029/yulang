import Yulang.GeneralDictionaryAllocDefaultCounterexample202
import Yulang.GeneralDictionaryAllocDefaultLocal202
import Yulang.GeneralDictionaryAllocDefaultSource202
import Yulang.GeneralDictionaryAllocProductionSplit202
import Yulang.GeneralDictionaryAllocRecordedChildren202
import Yulang.GeneralDictionaryAllocRecordedRegression202
import Yulang.GeneralDictionarySelectedInterface202
import Lean
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Yulang.GeneralDictionaryAllocDefaultCounterexample202,`Yulang.GeneralDictionaryAllocDefaultLocal202,`Yulang.GeneralDictionaryAllocDefaultSource202,`Yulang.GeneralDictionaryAllocProductionSplit202,`Yulang.GeneralDictionaryAllocRecordedChildren202,`Yulang.GeneralDictionaryAllocRecordedRegression202,`Yulang.GeneralDictionarySelectedInterface202]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if modules.contains e.header.moduleNames[i.toNat]! then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
