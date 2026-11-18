import Yulang.GeneralRebaseBodyTable261
import Yulang.GeneralRebaseClassTable261
import Yulang.GeneralRebaseClassCheck261
import Yulang.GeneralRebaseClassRun261
import Yulang.GeneralRebaseMergeRequests261
import Yulang.GeneralRebaseMergeMeaning261
import Yulang.GeneralRebaseMergeRun261
import Yulang.GeneralRebaseMergeFrame261
import Yulang.GeneralRebaseMergePacket261
import Yulang.GeneralRebaseMergeHistory261
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseBodyTable261.", "Yulang.GeneralRebaseClassTable261.", "Yulang.GeneralRebaseClassCheck261.", "Yulang.GeneralRebaseClassRun261.", "Yulang.GeneralRebaseMergeRequests261.", "Yulang.GeneralRebaseMergeMeaning261.", "Yulang.GeneralRebaseMergeRun261.", "Yulang.GeneralRebaseMergeFrame261.", "Yulang.GeneralRebaseMergePacket261.", "Yulang.GeneralRebaseMergeHistory261."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE261-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
