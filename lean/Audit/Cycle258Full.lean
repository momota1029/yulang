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
import Yulang.GeneralDictionaryEarlySearch258
import Yulang.GeneralDictionarySearchCost258
import Yulang.GeneralDictionaryFastFill258
import Yulang.GeneralDictionaryPendingOutput258
import Yulang.GeneralDictionaryOutputPremise258
import Yulang.GeneralDictionaryOutputInputs258
import Yulang.GeneralNominalActiveSupport258
import Yulang.GeneralDictionaryOutputFrame258
import Yulang.GeneralDictionaryOutputCompletion258
import Yulang.GeneralDictionaryOutputEvidence258
import Yulang.GeneralDictionaryOutputPublic258
import Yulang.GeneralDictionaryCompletedReadback258
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralDictionaryFamilyRecognition258.", "Yulang.GeneralDictionaryUniformFill258.", "Yulang.GeneralDictionaryUniformBlock258.", "Yulang.GeneralDictionaryUniformView258.", "Yulang.GeneralDictionaryUniformJournal258.", "Yulang.GeneralDictionaryUniformAlias258.", "Yulang.GeneralDictionaryDirectView258.", "Yulang.GeneralDictionaryInitialFill258.", "Yulang.GeneralDictionarySourceExtension258.", "Yulang.GeneralDictionaryPrivateBoundary258.", "Yulang.GeneralDictionaryEarlySearch258.", "Yulang.GeneralDictionarySearchCost258.", "Yulang.GeneralDictionaryFastFill258.", "Yulang.GeneralDictionaryPendingOutput258.", "Yulang.GeneralDictionaryOutputPremise258.", "Yulang.GeneralDictionaryOutputInputs258.", "Yulang.GeneralNominalActiveSupport258.", "Yulang.GeneralDictionaryOutputFrame258.", "Yulang.GeneralDictionaryOutputCompletion258.", "Yulang.GeneralDictionaryOutputEvidence258.", "Yulang.GeneralDictionaryOutputPublic258.", "Yulang.GeneralDictionaryCompletedReadback258."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE258-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
