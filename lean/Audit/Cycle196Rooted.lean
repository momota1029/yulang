import Yulang.GeneralNominalRootedView196
import Lean

#check Yulang.GeneralNominalRootedView196.node_transport
#print axioms Yulang.GeneralNominalRootedView196.node_transport
#check Yulang.GeneralNominalRootedView196.tree_transport
#print axioms Yulang.GeneralNominalRootedView196.tree_transport
#check Yulang.GeneralNominalRootedView196.readback_transport
#print axioms Yulang.GeneralNominalRootedView196.readback_transport
#check Yulang.GeneralNominalRootedView196.node_of_variables
#print axioms Yulang.GeneralNominalRootedView196.node_of_variables
#check Yulang.GeneralNominalRootedView196.support_of_global
#print axioms Yulang.GeneralNominalRootedView196.support_of_global

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
