import Yulang.GeneralNominalVersionedSupport233
import Yulang.GeneralDictionaryVersionedSecondRefresh233
set_option backward.isDefEq.respectTransparency false
/-! Concrete availability in the auxiliary versioned slice system only.
This does not replace the live kernel's legacy cache certificate. -/
namespace Yulang.GeneralDictionaryVersionedTrusted233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPointStage233 (allocated reserved ordinary)
open GeneralDictionaryVersionedSecondInstall233
open GeneralNominalVersionedSupport233
open CommonNominalFullCarrier

 theorem readback : Readback installed [] plan := by
  intro slot member test observation head model valid
  exact GeneralDictionaryJournalRefinement228Reobserve.recorded_source allocated reserved ordinary
    model valid.1 (GeneralNominalSupport.head_recorded head)

 theorem input_trusted : Trusted installed [.input plan] :=
  .input plan .source (List.mem_cons_self ..) readback

 theorem class_readback : ClassReadback installed [.input plan] effect := by
  intro site member alias
  change site ∈ GeneralDictionaryVersionedPointStage233.point.core.sites at member
  rw [GeneralDictionaryVersionedPointStage233.centered_sites] at member
  cases List.mem_singleton.mp member
  constructor
  · rfl
  · change GeneralNominalDemandMerging.All₂ _ [some (GeneralNominalRecursiveInspection.Origin.source 0)] [some (GeneralNominalRecursiveInspection.Origin.source 0)]
    exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

 theorem settled : PacketSettled installed plan := terminal_settled (List.mem_cons_self ..) terminal

 theorem output_trusted : Trusted installed [.output effect,.input plan] :=
  .output effect input_trusted (List.mem_cons_self ..) (List.mem_cons_self ..)
    (List.mem_cons_self ..) class_readback settled

 theorem aggregates {model : GeneralNominalCommonBridge.Assignment} (valid : SliceModels installed [.input plan] model) :
    Equivalent (model (GeneralDictionaryVersionedNames231.freshName 0)).1 .emptyRecord ∧
    Equivalent (model (GeneralDictionaryVersionedNames231.freshName 1)).1 .emptyRecord := by
  have input := valid.2.2 (.input plan) (List.mem_cons_self ..)
  have merges := input.1.2.1
  rw [GeneralDictionaryVersionedPoint233.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((GeneralNominalAllocation.equations _ (.union (.var 2) (.var 2)) ++
      GeneralNominalAllocation.equations _ (.inter (.var 2) (.var 2))) ++ _) at merges
  have pair := (PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1
  have lower := (GeneralNominalCaptureMerges.equations_exact ..).mp pair.1
  have upper := (GeneralNominalCaptureMerges.equations_exact ..).mp pair.2
  have width := valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
  change Equivalent (model _).1 (.union (model 2).1 (model 2).1) at lower
  change Equivalent (model _).1 (.inter (model 2).1 (model 2).1) at upper
  have join : Equivalent (.union (model 2).1 (model 2).1) (model 2).1 :=
    ⟨(common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩,
      ((common_union_is_join ..).mp (subtype_refl _)).1⟩
  have meet : Equivalent (.inter (model 2).1 (model 2).1) (model 2).1 :=
    ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
      (common_inter_is_meet ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
  exact ⟨⟨subtype_trans lower.1 (subtype_trans join.1 width.1),
    subtype_trans width.2 (subtype_trans join.2 lower.2)⟩,
    ⟨subtype_trans upper.1 (subtype_trans meet.1 width.1),
    subtype_trans width.2 (subtype_trans meet.2 upper.2)⟩⟩
theorem source_cut_not_input_slice :
    ¬ SliceModels installed [.input plan] GeneralDictionaryOptionalSource229.modelLow := by
  intro valid
  have lower := (aggregates valid).1
  have high := GeneralDictionaryVersionedNames231.fresh_above 0
  have same : (GeneralDictionaryOptionalSource229.modelLow
      (GeneralDictionaryVersionedNames231.freshName 0)).1 = GeneralDictionaryOptionalOutput229.value := by
    simp [GeneralDictionaryOptionalSource229.modelLow,
      show GeneralDictionaryVersionedNames231.freshName 0 ≠ 0 by omega,
      show GeneralDictionaryVersionedNames231.freshName 0 ≠ 1 by omega,
      show GeneralDictionaryVersionedNames231.freshName 0 ≠ 2 by omega,
      show GeneralDictionaryVersionedNames231.freshName 0 ≠ 3 by omega]
  rw [same] at lower
  exact GeneralDictionaryOptionalOutput229.not_width lower

end Yulang.GeneralDictionaryVersionedTrusted233
