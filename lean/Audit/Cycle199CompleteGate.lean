import Yulang.GeneralDictionaryMatEmptyLeaf199
import Yulang.GeneralDictionaryMatGuardObstruction199
import Yulang.GeneralDictionaryMatGuardTrace199
import Yulang.GeneralDictionaryMatGuardWitness199
import Yulang.GeneralDictionaryMatPriorConflict199
import Yulang.GeneralDictionaryMatPriorConflictLocal199
import Yulang.GeneralDictionaryMatPriorConflictSource199
import Yulang.GeneralDictionaryMatVariableNode199
import Lean
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`Yulang.GeneralDictionaryMatEmptyLeaf199,`Yulang.GeneralDictionaryMatGuardObstruction199,`Yulang.GeneralDictionaryMatGuardTrace199,`Yulang.GeneralDictionaryMatGuardWitness199,`Yulang.GeneralDictionaryMatPriorConflict199,`Yulang.GeneralDictionaryMatPriorConflictLocal199,`Yulang.GeneralDictionaryMatPriorConflictSource199,`Yulang.GeneralDictionaryMatVariableNode199]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if modules.contains e.header.moduleNames[i.toNat]! then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
