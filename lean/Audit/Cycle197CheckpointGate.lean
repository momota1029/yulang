import Yulang.GeneralNominalTraceRefreshExample197
import Lean
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let modules := #["Yulang.GeneralNominalInspectionTrace197", "Yulang.GeneralNominalTraceDictionary197", "Yulang.GeneralNominalTraceRefreshExample197"]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if modules.contains e.header.moduleNames[i.toNat]!.toString then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
#print axioms Yulang.GeneralNominalInspectionTrace197.trace_report
#print axioms Yulang.GeneralNominalInspectionTrace197.traces_report
