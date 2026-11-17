import Yulang.GeneralDictionaryOptionalRegression229

namespace Yulang.GeneralDictionaryOptionalJoint229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229 GeneralDictionaryOptionalSelected229
open CommonNominalFullCarrier
open GeneralDeclarations GeneralDeclarationPatterns

theorem lower_output (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models stage m) :
    Equivalent (m lo).1 GeneralDictionaryOptionalOutput229.value := by
  have installedValid := (stage_models m).mp valid
  have old := (GeneralNominalCenteredHeadMatStepJournal.install_models (state := start) (effect := effect) rfl).mp installedValid
  have packetValid : GeneralNominalCenteredHeadMatStepPackets.Holds plan m := old.2.1
  have merges := packetValid.2.1.1.2.1
  rw [bindings_exact] at merges
  have bound := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [Declaration.inputNames,variablesArgs,normalizeArgs,normalize,Pattern.variables]) merges
  change Equivalent (m lo).1 (m 4).1 at bound
  have output := packetValid.2.2
  change (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
    (GeneralNominalCenteredHeadMatEffects.variables plan m) m at output
  rw [emitted_schema] at output
  have emitted := output ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
  exact ⟨subtype_trans bound.1 emitted.1,subtype_trans emitted.2 bound.2⟩

theorem no_current_packet (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models stage m) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds currentPlan m := by
  intro current
  have merges := current.2.1.1.2.1
  rw [GeneralDictionaryOptionalCurrent229.bindings_exact] at merges
  have bound := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [Declaration.inputNames,variablesArgs,normalizeArgs,normalize,Pattern.variables]) merges
  change Equivalent (m lo).1 (m 2).1 at bound
  have source := valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
  have output := lower_output m valid
  apply GeneralDictionaryOptionalOutput229.not_width
  exact ⟨subtype_trans output.2 (subtype_trans bound.1 source.1),
    subtype_trans (subtype_trans source.2 bound.2) output.1⟩

theorem no_install (next : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (enabled : GeneralDictionaryDefaultKernel208.Installable registry stage next)
    (focused : next.plan.packet.site.occurrence = root) : False := by
  have framed := next.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,focused] at framed
  have same := GeneralDictionaryOptionalCurrent229.frame_plan allocated reserved ordinary
    context_eq raw_sites centers framed
  obtain ⟨m,valid,packetValid,rest⟩ := enabled.common
  rw [same] at packetValid
  exact no_current_packet m valid packetValid

end Yulang.GeneralDictionaryOptionalJoint229
