import Yulang.GeneralDictionarySourceAtom255
import Yulang.GeneralNominalViewTypeTerms255
import Yulang.GeneralNominalViewTypeMap255
import Yulang.GeneralNominalViewNormal255
import Yulang.GeneralDictionaryViewNormal255
import Yulang.GeneralPresenceSourceSupport255
import Yulang.GeneralNominalSourceViewSupport255
import Yulang.GeneralNominalSourceBasis255
import Yulang.GeneralNominalViewTypeImage255
import Yulang.GeneralNominalViewFixed255
import Yulang.GeneralNominalTemplateChoices255
import Yulang.GeneralNominalTemplateCongruence255
import Yulang.GeneralNominalTemplateNormal255
import Yulang.GeneralNominalSourceTemplateMenu255
import Yulang.GeneralNominalTemplateSupport255
import Yulang.GeneralNominalCanonicalBasis255
import Yulang.GeneralNominalNormalizedDepth255
import Lean
open Lean Elab Command in
run_cmd do
 let environment ← getEnv
 let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
 let prefixes := #["Yulang.GeneralDictionarySourceAtom255.", "Yulang.GeneralNominalViewTypeTerms255.", "Yulang.GeneralNominalViewTypeMap255.", "Yulang.GeneralNominalViewNormal255.", "Yulang.GeneralDictionaryViewNormal255.", "Yulang.GeneralPresenceSourceSupport255.", "Yulang.GeneralNominalSourceViewSupport255.", "Yulang.GeneralNominalSourceBasis255.", "Yulang.GeneralNominalViewTypeImage255.", "Yulang.GeneralNominalViewFixed255.", "Yulang.GeneralNominalTemplateChoices255.", "Yulang.GeneralNominalTemplateCongruence255.", "Yulang.GeneralNominalTemplateNormal255.", "Yulang.GeneralNominalSourceTemplateMenu255.", "Yulang.GeneralNominalTemplateSupport255.", "Yulang.GeneralNominalCanonicalBasis255.", "Yulang.GeneralNominalNormalizedDepth255."]
 let mut count : Nat := 0
 for (name, _) in environment.constants.toList do
  if prefixes.any (fun pfx => name.toString.startsWith pfx || name.toString.startsWith ("_private." ++ pfx)) then
   for dependency in ← collectAxioms name do
    unless allowed.contains dependency do throwError "Forbidden dependency {name}: {dependency}"
   count := count + 1
 logInfo m!"CYCLE255-FULL-AUDIT-PASS: {count} declarations including generated and private declarations"
