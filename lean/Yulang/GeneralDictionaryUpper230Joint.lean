import Yulang.GeneralDictionaryUpper230Selected
import Yulang.GeneralDictionaryUpper230Administrative
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Joint
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDeclarations GeneralDeclarationPatterns CommonNominalFullCarrier

theorem no_current_packet (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models after m) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds currentPlan m := by
  intro current
  have merges := current.2.1.1.2.1
  rw [GeneralDictionaryUpper230Current.bindings_exact] at merges
  have bound := GeneralDictionaryDefaultMergeRevisionProbe210.repeated_lower_value
    (name := 0) (by simp [Declaration.inputNames,variablesArgs,normalizeArgs,normalize,Pattern.variables]) merges
  change Equivalent (m lo).1 (m 2).1 at bound
  have width := valid.1.1.2.1 (2 : Fin 6) .emptyRecord rfl
  have output := GeneralDictionaryOptionalJoint229.lower_output m ((models m).mp valid)
  exact GeneralDictionaryOptionalOutput229.not_width
    ⟨subtype_trans output.2 (subtype_trans bound.1 width.1),
      subtype_trans (subtype_trans width.2 bound.2) output.1⟩

theorem no_install (next : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (enabled : GeneralDictionaryDefaultKernel208.Installable registry after next)
    (focused : next.plan.packet.site.occurrence = root) : False := by
  have framed := next.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,focused] at framed
  have same := GeneralDictionaryUpper230Current.frame_plan rfl rfl rfl framed
  obtain ⟨m,valid,packetValid,rest⟩ := enabled.common
  rw [same] at packetValid
  exact no_current_packet m valid packetValid

theorem no_instance : ¬ GeneralDictionaryTotalEvidence206.Instance registry after.core model root key children :=
  GeneralDictionaryUpper230Current.no_instance rfl rfl rfl model rfl lower_value

theorem selected_without_instance :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root after ∧
    GeneralNominalCenteredHeadMatStepJournal.Models after model ∧
    GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry after root
      (.selected declaration.id currentPacket.children) ∧
    ¬ GeneralDictionaryTotalEvidence206.Instance registry after.core model root declaration.id currentPacket.children :=
  ⟨GeneralDictionaryUpper230Step.reachable,GeneralDictionaryUpper230Step.inhabited,selected,no_instance⟩

end Yulang.GeneralDictionaryUpper230Joint
