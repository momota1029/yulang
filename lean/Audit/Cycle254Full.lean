import Yulang.GeneralNominalQueryReadback254
import Yulang.GeneralNominalInputReadback254
import Yulang.GeneralNominalOutputReadback254
import Yulang.GeneralNominalBinderProducer254
import Yulang.GeneralNominalDefaultReadback254
import Yulang.GeneralNominalCapturedOutput254
import Yulang.GeneralNominalEvidenceOutput254
import Yulang.GeneralNominalSourceReadback254
import Yulang.GeneralNominalProducerOrder254
import Yulang.GeneralNominalOutputMenu254
import Yulang.GeneralNominalProducerRank254
import Yulang.GeneralNominalSourceOutputDepth254
import Yulang.GeneralDictionaryOutputReadback254
import Yulang.GeneralNominalRawOutputBudget254
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralNominalQueryReadback254.", "Yulang.GeneralNominalInputReadback254.", "Yulang.GeneralNominalOutputReadback254.", "Yulang.GeneralNominalBinderProducer254.", "Yulang.GeneralNominalDefaultReadback254.", "Yulang.GeneralNominalCapturedOutput254.", "Yulang.GeneralNominalEvidenceOutput254.", "Yulang.GeneralNominalSourceReadback254.", "Yulang.GeneralNominalProducerOrder254.", "Yulang.GeneralNominalOutputMenu254.", "Yulang.GeneralNominalProducerRank254.", "Yulang.GeneralNominalSourceOutputDepth254.", "Yulang.GeneralDictionaryOutputReadback254.", "Yulang.GeneralNominalRawOutputBudget254.", "Cycle254", "_private.Audit.Cycle254Usage."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE254-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
