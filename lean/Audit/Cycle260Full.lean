import Yulang.GeneralRebaseOutputKeys260
import Yulang.GeneralRebaseOutputDecoder260
import Yulang.GeneralOutputRebaseSource260
import Yulang.GeneralOutputRebaseModels260
import Yulang.GeneralOutputRebaseInstalled260
import Yulang.GeneralOutputRebaseRun260
import Yulang.GeneralOutputRebasePublic260
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralRebaseOutputKeys260.", "Yulang.GeneralRebaseOutputDecoder260.", "Yulang.GeneralOutputRebaseSource260.", "Yulang.GeneralOutputRebaseModels260.", "Yulang.GeneralOutputRebaseInstalled260.", "Yulang.GeneralOutputRebaseRun260.", "Yulang.GeneralOutputRebasePublic260."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE260-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
