import Yulang.GeneralRebaseAffectedMerge264
import Yulang.GeneralRebaseLiveMeaning264
import Yulang.GeneralRebaseLiveProjection264
import Yulang.GeneralRebaseMergeRequests264
import Yulang.GeneralRebaseProjectedBudget264
import Yulang.GeneralRebaseProspectiveCurrent264
import Yulang.GeneralRebaseProspectiveFixture264
import Yulang.GeneralRebaseProspectiveStep264
import Yulang.GeneralRebaseSourceInstallProjection264
import Yulang.GeneralRebaseSourceProjection264
import Yulang.GeneralRebaseSourceRequests264
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseAffectedMerge264.", "Yulang.GeneralRebaseLiveMeaning264.", "Yulang.GeneralRebaseLiveProjection264.", "Yulang.GeneralRebaseMergeRequests264.", "Yulang.GeneralRebaseProjectedBudget264.", "Yulang.GeneralRebaseProspectiveCurrent264.", "Yulang.GeneralRebaseProspectiveFixture264.", "Yulang.GeneralRebaseProspectiveStep264.", "Yulang.GeneralRebaseSourceInstallProjection264.", "Yulang.GeneralRebaseSourceProjection264.", "Yulang.GeneralRebaseSourceRequests264."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE264-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
