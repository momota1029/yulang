import Yulang.GeneralNominalRootedViewExample196
import Lean
#check Yulang.GeneralNominalRootedViewExample196.supported
#print axioms Yulang.GeneralNominalRootedViewExample196.supported
#check Yulang.GeneralNominalRootedViewExample196.not_global
#print axioms Yulang.GeneralNominalRootedViewExample196.not_global

open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i.toNat]!.toString.endsWith "196" then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
