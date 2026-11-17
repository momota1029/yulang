import Yulang.GeneralDictionaryOptionalReachable229
import Yulang.GeneralDictionaryOptionalRaw229
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOptionalRawStage229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh
    (GeneralNominalAllocation.merges snapshot registry root.identity declaration packet.bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh
      (GeneralNominalAllocation.equations lo (.union (.var 4) (.var 4)) ++
        GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (modelHigh lo).1 (.union .emptyRecord .emptyRecord) ∧
      Equivalent (modelHigh hi).1 (.inter .emptyRecord .emptyRecord)
    rw [GeneralDictionaryOptionalRaw229.high_fresh 0, GeneralDictionaryOptionalRaw229.high_fresh 1]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩


theorem old_raw : GeneralNominalState.Models packet.privateContext.state modelHigh := by
  unfold GeneralNominalSaturationState.Packet.privateContext
  unfold privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_models true,?_,merge_model⟩,?_⟩
  · change GeneralNominalAllocation.Compatible packet.bindings modelHigh
    rw [bindings_exact]
    intro first one last two _
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals exact subtype_refl _
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals exact subtype_refl _

theorem current_raw : GeneralNominalState.Models
    (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary).state modelHigh :=
  (GeneralDictionaryJournalRefinement228Reobserve.extended_models_iff allocated reserved ordinary modelHigh).mpr old_raw

theorem current_head : GeneralNominalCenteredHeadCandidates.HeadModels registry
    (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary)
    root declaration [(0,0)] modelHigh :=
  GeneralDictionaryOptionalRaw229.head_model allocated reserved ordinary current_raw

theorem current_prepared : GeneralNominalCenteredHeadCandidates.Prepared registry
    (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary)
    root declaration := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,?_,
    [(0,0)],?_,?_,modelHigh,current_head⟩
  · intro index
    constructor <;> apply List.mem_append_left <;> apply List.mem_append_left <;> apply List.mem_append_left
    all_goals simp [base,root,GeneralNominalCenteredHeadCandidates.inputs]
  · intro key member _
    change key ∈ snapshot.allocated ++ GeneralNominalAllocation.keys registry root.identity
    exact List.mem_append_right _ member
  · decide +kernel
  · rw [GeneralDictionaryOptionalCurrent229.report_exact]
    exact ⟨rfl,rfl,rfl⟩

/-- Raw applicability can survive even when this full journal model cannot
produce any current instance. This does not establish Stable or selected Local. -/
theorem prepared_without_instance :
    GeneralNominalCenteredHeadCandidates.Prepared registry
      (GeneralDictionaryOptionalCurrent229.currentContext allocated reserved ordinary) root declaration ∧
    GeneralNominalCenteredHeadMatStepJournal.Models stage GeneralDictionaryOptionalInstall229.model ∧
    ¬ GeneralDictionaryTotalEvidence206.Instance registry stage.core
      GeneralDictionaryOptionalInstall229.model root key children :=
  ⟨current_prepared,stage_model,no_instance⟩

end Yulang.GeneralDictionaryOptionalRawStage229
