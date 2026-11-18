import Yulang.GeneralPatternAdditiveDepth253
import Yulang.GeneralNominalExprDepth253
import Yulang.GeneralNominalOutputNames253
import Yulang.GeneralNominalRawFinite253
import Yulang.GeneralNominalPublicPorts253
import Yulang.GeneralDictionaryCompoundPool253
import Yulang.GeneralDictionaryCompoundPoolRepair253
import Yulang.GeneralPatternDependencyDepth253
import Yulang.GeneralDictionaryOutputDepthRepair253
import Yulang.GeneralDeclarationProducerRank253
import Yulang.GeneralDeclarationOutputDepth253
import Yulang.GeneralNominalPublicBasis253
import Yulang.GeneralNominalAllHeadReadback253
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralPatternAdditiveDepth253.", "_private.Yulang.GeneralPatternAdditiveDepth253.",
  "Yulang.GeneralNominalExprDepth253.", "_private.Yulang.GeneralNominalExprDepth253.",
  "Yulang.GeneralNominalOutputNames253.", "_private.Yulang.GeneralNominalOutputNames253.",
  "Yulang.GeneralNominalRawFinite253.", "_private.Yulang.GeneralNominalRawFinite253.",
  "Yulang.GeneralNominalPublicPorts253.", "_private.Yulang.GeneralNominalPublicPorts253.",
  "Yulang.GeneralDictionaryCompoundPool253.", "_private.Yulang.GeneralDictionaryCompoundPool253.",
  "Yulang.GeneralDictionaryCompoundPoolRepair253.", "_private.Yulang.GeneralDictionaryCompoundPoolRepair253.",
  "Yulang.GeneralPatternDependencyDepth253.", "_private.Yulang.GeneralPatternDependencyDepth253.",
  "Yulang.GeneralDictionaryOutputDepthRepair253.", "_private.Yulang.GeneralDictionaryOutputDepthRepair253.",
  "Yulang.GeneralDeclarationProducerRank253.", "_private.Yulang.GeneralDeclarationProducerRank253.",
  "Yulang.GeneralDeclarationOutputDepth253.", "_private.Yulang.GeneralDeclarationOutputDepth253.",
  "Yulang.GeneralNominalPublicBasis253.", "_private.Yulang.GeneralNominalPublicBasis253.",
  "Yulang.GeneralNominalAllHeadReadback253.", "_private.Yulang.GeneralNominalAllHeadReadback253."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE253-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
