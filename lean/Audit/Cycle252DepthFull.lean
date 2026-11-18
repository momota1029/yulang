import Yulang.GeneralDictionaryOutputDepthInstall252
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  let spelling := name.toString
  if spelling.startsWith "Yulang.GeneralDictionaryOutputDepth" ||
     spelling.startsWith "_private.Yulang.GeneralDictionaryOutputDepth" then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE252-DEPTH-COMPLETEAUDIT-PASS: {count} declarations including generated and private declarations"
