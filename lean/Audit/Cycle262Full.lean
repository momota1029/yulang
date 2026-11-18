import Yulang.GeneralFiniteAliasClosure262
import Yulang.GeneralFiniteAliasSearch262
import Yulang.GeneralRebaseExecutableRequests262
import Yulang.GeneralRebaseExecutableSnapshot262
import Yulang.GeneralRebaseRootTrace262
import Yulang.GeneralRebaseAliasRegression262
import Yulang.GeneralRebaseChildRequestPool262
import Yulang.GeneralRebaseSourceRequestPool262
import Yulang.GeneralRebaseDynamicSource262
import Yulang.GeneralRebaseSourceObserver262
import Yulang.GeneralRebaseDynamicTrace262
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralFiniteAliasClosure262.", "Yulang.GeneralFiniteAliasSearch262.", "Yulang.GeneralRebaseExecutableRequests262.", "Yulang.GeneralRebaseExecutableSnapshot262.", "Yulang.GeneralRebaseRootTrace262.", "Yulang.GeneralRebaseAliasRegression262.", "Yulang.GeneralRebaseChildRequestPool262.", "Yulang.GeneralRebaseSourceRequestPool262.", "Yulang.GeneralRebaseDynamicSource262.", "Yulang.GeneralRebaseSourceObserver262.", "Yulang.GeneralRebaseDynamicTrace262."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE262-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
