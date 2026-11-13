import Yulang.GeneralNominalPointCycleSource
import Yulang.GeneralNominalActualInspectionSteps

/-! The retained nominal argument is cyclic although its inspection bounds
are separate acyclic observations. The added actual-position guard blocks it. -/
namespace Yulang.GeneralNominalPointCycleInspection
open GeneralNominalPointCycleSource GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralNominalActualInspectionSteps
open CommonNominalFullCarrier

abbrev packet : Packet roles :=
  ⟨registry,context true,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
abbrev argument : Origin := .nominal (.source 0) 0 0
abbrev payload : Origin := .structural argument (.variant 0) 0
abbrev oldReport := GeneralNominalRecursiveCandidates.report (context true) declaration [(0,0)]

theorem old_inspected : oldReport.inspected = [(0,0),(3,4)] := by decide +kernel
theorem old_finished : Finished oldReport := by
  unfold Finished
  decide +kernel
theorem old_omits_cycle : ∀ visited ∈ oldReport.inspected, visited.1 ≠ (2 : Fin 7) := by
  rw [old_inspected]
  decide +kernel
theorem old_retains_origin : oldReport.tests = [(argument,.structural (.variant 0))] := by cbv
theorem old_capture : oldReport.captures = [⟨0,(5,6),some payload⟩] := by cbv

theorem recovered_inputs :
    (GeneralNominalFeedbackSites.recover refreshed.current packet.site).inputs = [some (.source 0)] := by
  simp [GeneralNominalFeedbackSites.recover,GeneralNominalFeedbackSites.recoverOrigin,
    packet,GeneralNominalDemandMerging.pointSite,List.ofFn_succ,roles,
    GeneralDeclarationExamples.bareRole]

theorem actual_tests : (inspection refreshed.current packet).tests =
    [(.source 0,.nominal 0 1),(argument,.structural (.variant 0))] := by
  unfold inspection
  rw [recovered_inputs]
  cbv

theorem actual_inspected : (inspection refreshed.current packet).inspected = [(0,0),(3,4)] := by
  unfold inspection
  rw [recovered_inputs]
  cbv

theorem argument_readback : Represents refreshed.current argument 2 := by
  apply nominal_alias_readback refreshed.current (fun m valid => alias_zero m valid.1)
  exact point_argument_readback refreshed.current (1 : Fin 7) (2 : Fin 7) (descriptor (2,2)) rfl rfl

theorem cycle_two : GeneralNominalFeedbackK2.RecursAt refreshed.current 2 := by
  refine ⟨⟨2,⟨source_member true 2,source_member true 2,Or.inl ?_⟩,.nil 2⟩,model,refreshed_models⟩
  exact ⟨(2 : Fin 7),(2 : Fin 7),⟨(0 : Fin 1),(fun _ => (2 : Fin 7)),rfl,(0 : Fin 1),rfl⟩,
    GeneralNominalFeedbackK2.equal_refl _ 2,GeneralNominalFeedbackK2.equal_refl _ 2⟩

theorem actual_cycle : Cyclic refreshed.current argument := ⟨2,argument_readback,cycle_two⟩

theorem first_round_blocked (support : List (GeneralSourceDictionaries.Occurrence roles)) :
    ¬ PacketGuard refreshed packet support := by
  apply tested_cycle_blocks (origin := argument) (test := .structural (.variant 0))
  · rw [actual_tests]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · exact actual_cycle

theorem point_start : SourceFormed registry root start := .initial (context false) initial_source

theorem actual_refresh : Step registry root start refreshed :=
  ⟨root,.root,.administrative root _ (.refresh root (context true) certificate 0
    (source_member false 0) zero_unknown ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩)⟩

theorem actual_formed : SourceFormed registry root refreshed := .update point_start actual_refresh

end Yulang.GeneralNominalPointCycleInspection
