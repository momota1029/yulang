import Yulang.GeneralNominalFinishedObservation197
import Yulang.GeneralNominalInspectionTrace197
import Yulang.GeneralNominalMixedExample197
import Yulang.GeneralNominalMixedJournal197
import Yulang.GeneralNominalRefinementExample197
import Yulang.GeneralNominalRefinementTrace197
import Yulang.GeneralNominalSyntaxExample197
import Yulang.GeneralNominalSyntaxRefresh197
import Yulang.GeneralNominalTraceDictionary197
import Yulang.GeneralNominalTraceEvidence197
import Yulang.GeneralNominalTraceRefreshExample197
import Lean
open Lean Elab Command in
run_cmd do
  let e ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (n, _) in e.constants.toList do
    if let some i := e.getModuleIdxFor? n then
      if e.header.moduleNames[i.toNat]!.toString.endsWith "197" then
        count := count + 1
        for a in ← collectAxioms n do
          unless allowed.contains a do throwError "bad axiom {n}: {a}"
  if count == 0 then throwError "empty audit"
  logInfo m!"AXIOM-GATE-PASS: {count} declarations"
