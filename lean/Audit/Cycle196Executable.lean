import Yulang.GeneralNominalExecutableView196
import Lean

#check Yulang.GeneralNominalExecutableView196.replaced
#print axioms Yulang.GeneralNominalExecutableView196.replaced
#check Yulang.GeneralNominalExecutableView196.actual_step
#print axioms Yulang.GeneralNominalExecutableView196.actual_step
#check Yulang.GeneralNominalExecutableView196.same_models
#print axioms Yulang.GeneralNominalExecutableView196.same_models
#check Yulang.GeneralNominalExecutableView196.inhabited
#print axioms Yulang.GeneralNominalExecutableView196.inhabited
#check Yulang.GeneralNominalExecutableView196.descriptor_changed
#print axioms Yulang.GeneralNominalExecutableView196.descriptor_changed
#check Yulang.GeneralNominalExecutableView196.preserve_variable_evidence
#print axioms Yulang.GeneralNominalExecutableView196.preserve_variable_evidence

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
