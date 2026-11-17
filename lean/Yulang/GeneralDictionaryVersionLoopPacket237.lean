import Yulang.GeneralDictionaryVersionLoopSource237
import Yulang.GeneralNominalVersionedHeadReadback237
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionLoopPacket237
open GeneralDictionaryVersionLoopSource237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
abbrev packet : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(3,3)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
abbrev lo := GeneralNominalAggregateVersion231.slot 3 0 0 0 0 [(0,2,2),(0,2,2)]
abbrev hi := GeneralNominalAggregateVersion231.slot 3 0 0 1 0 [(0,2,2),(0,2,2)]
abbrev actual := fresh 3 0 0 8 0 0

theorem above_value (n : Nat) (above : 3 < n) : (model n).1 = F := by
 unfold GeneralDictionaryVersionLoopSource237.model GeneralDictionaryVersionLoopSource237.value
 split <;> first | rfl | omega

theorem lower_value : (model lo).1 = F := above_value _ (GeneralNominalAggregateVersion231.above_seed ..)
theorem upper_value : (model hi).1 = F := above_value _ (GeneralNominalAggregateVersion231.above_seed ..)
theorem actual_value : (model actual).1 = F := above_value _ (GeneralNominalIdentities.source_above_seed ..)
theorem query : GeneralNominalInspection.queries snapshot interpretation declaration =
    [.nominal 5 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

abbrev origin0 : Origin := .nominal (.source 3) 5 0
abbrev origin1 : Origin := .nominal (.source 3) 5 1
abbrev calculated : Report snapshot where
  captures := [⟨0,(2,2),some origin0⟩,⟨0,(2,2),some origin1⟩]
  inspected := [(3,3)]
  checked := [(3,3),(3,3),(2,2),(2,2)]
  anchors := [(origin0,(2,2)),(origin1,(2,2))]

theorem report_exact : report context declaration [(3,3)] = calculated := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,calculated,snapshot]
  rw [inspectMany.eq_2,inspectMany.eq_2,inspectMany.eq_1]
  simp only [inspect.eq_1,Report.append]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem bindings_exact : packet.bindings = [(0,2,2),(0,2,2)] := by
  change bindings snapshot (report context declaration [(3,3)]) = _
  rw [report_exact]; rfl

theorem seen0 : Observes model origin0 F :=
  .nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl
theorem seen1 : Observes model origin1 F :=
  .nominal (.source 3) ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem observed_value {value : Ty} (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 3) 5 index) value) :
    Equivalent value F := by
  have observed : Observes model (.nominal (.source 3) 5 index) F := by
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact seen0
    · exact seen1
  exact nominal_observation_unique model (.argument (.source 3) 5 index) value F seen observed

theorem fit_observed {value : Ty} (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 3) 5 index) value) :
    Fits snapshot model (2,2) value := by
  have equal := observed_value index small seen
  exact ⟨subtype_trans (subtype_refl _) equal.2,equal.1⟩

theorem raw_projection : ProjectionModels snapshot (report context declaration [(3,3)]) model := by
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
    (GeneralNominalVersionedAllocation231.merges snapshot registry root.identity declaration packet.bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations lo (.union (.var 2) (.var 2)) ++
        GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (model lo).1 (.union F F) ∧
      Equivalent (model hi).1 (.inter F F)
    rw [lower_value,upper_value]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model model (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model : GeneralNominalVersionedCandidates231.HeadModels registry context root declaration [(3,3)] model := by
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


end Yulang.GeneralDictionaryVersionLoopPacket237
