import Yulang.GeneralDictionaryVersionLoopPrefix238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopSecondPacket238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopRetarget237 (retargeted retargeted_model)
open GeneralDictionaryVersionLoopNext237 (current report_exact bindings_exact)
open GeneralDictionaryVersionLoopPacket237 (origin0 origin1 seen0 seen1 observed_value actual actual_value above_value)
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
noncomputable abbrev packet := GeneralDictionaryVersionLoopNext237.packet
noncomputable abbrev plan : Plan roles := ⟨packet,rootSite 3 root,rfl⟩
abbrev oldLo := GeneralDictionaryVersionLoopPacket237.lo
abbrev lo := GeneralDictionaryVersionLoopNext237.nextLo
abbrev hi := GeneralDictionaryVersionLoopNext237.nextHi
theorem lower_value : (model lo).1 = F := above_value _ (GeneralNominalAggregateVersion231.above_seed ..)
theorem upper_value : (model hi).1 = F := above_value _ (GeneralNominalAggregateVersion231.above_seed ..)
theorem source_model : GeneralNominalState.Models current.state model := retargeted_model.1.1
theorem fit_observed {value : Ty} (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 3) 5 index) value) :
    Fits current.state model ((4 : Fin 5),(4 : Fin 5)) value := by
  have equal := observed_value index small seen
  change Subtype (model oldLo).1 value ∧ Subtype value (model oldLo).1
  rw [GeneralDictionaryVersionLoopPacket237.lower_value]
  exact ⟨equal.2,equal.1⟩

theorem raw_projection : ProjectionModels current.state (report current declaration [((3 : Fin 5),(3 : Fin 5))]) model := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0⟩,fun _ seen => fit_observed 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1⟩,fun _ seen => fit_observed 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed 0 (by decide) seen | exact fit_observed 1 (by decide) seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x F := by first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX
      have ey : Equivalent y F := by first | exact observed_value 0 (by decide) seenY | exact observed_value 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalVersionedAllocation231.merges current.state registry root.identity declaration packet.bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations lo (.union (.var oldLo) (.var oldLo)) ++
        GeneralNominalAllocation.equations hi (.inter (.var oldLo) (.var oldLo))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (model lo).1 (.union (model oldLo).1 (model oldLo).1) ∧
      Equivalent (model hi).1 (.inter (model oldLo).1 (model oldLo).1)
    rw [lower_value,upper_value,GeneralDictionaryVersionLoopPacket237.lower_value]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model model (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model : GeneralNominalVersionedCandidates231.HeadModels registry current root declaration [((3 : Fin 5),(3 : Fin 5))] model := by
  refine ⟨?_,raw_projection⟩
  unfold GeneralNominalVersionedCandidates231.privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalVersionedAllocation231.propagate_models ..).mpr ⟨source_model,?_,merge_model⟩,?_⟩
  · change GeneralNominalAllocation.Compatible packet.bindings model
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
    all_goals first | exact subtype_refl _ | exact subtype_refl _

end Yulang.GeneralDictionaryVersionLoopSecondPacket238
