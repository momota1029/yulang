import Yulang.GeneralNominalQueryReadback254
import Yulang.GeneralNominalInputReadback254
import Yulang.GeneralNominalOutputReadback254

import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralNominalQueryReadback254.", "Yulang.GeneralNominalInputReadback254.", "Yulang.GeneralNominalOutputReadback254."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE254-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
