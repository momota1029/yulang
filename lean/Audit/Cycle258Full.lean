import Yulang.GeneralDictionaryFamilyRecognition258
import Yulang.GeneralDictionaryUniformFill258
import Yulang.GeneralDictionaryUniformBlock258
import Yulang.GeneralDictionaryUniformView258
import Yulang.GeneralDictionaryUniformJournal258
import Yulang.GeneralDictionaryUniformAlias258
import Yulang.GeneralDictionaryDirectView258
import Yulang.GeneralDictionaryInitialFill258
import Yulang.GeneralDictionarySourceExtension258
import Yulang.GeneralDictionaryPrivateBoundary258
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralDictionaryFamilyRecognition258.", "Yulang.GeneralDictionaryUniformFill258.", "Yulang.GeneralDictionaryUniformBlock258.", "Yulang.GeneralDictionaryUniformView258.", "Yulang.GeneralDictionaryUniformJournal258.", "Yulang.GeneralDictionaryUniformAlias258.", "Yulang.GeneralDictionaryDirectView258.", "Yulang.GeneralDictionaryInitialFill258.", "Yulang.GeneralDictionarySourceExtension258.", "Yulang.GeneralDictionaryPrivateBoundary258."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE258-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
