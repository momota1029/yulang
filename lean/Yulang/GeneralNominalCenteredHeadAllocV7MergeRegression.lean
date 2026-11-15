import Yulang.GeneralNominalCenteredHeadAllocV7Composition
import Yulang.GeneralNominalCenteredHeadAllocV7Completion
import Yulang.GeneralNominalCenteredHeadAllocMergeConflict

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalCenteredHeadAllocMergeSource GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState GeneralNominalCenteredHeadAllocMergeStable
open GeneralNominalCenteredHeadAllocMergedConflict
open GeneralNominalCenteredHeadMatStepJournal (Models)
open GeneralNominalCenteredHeadOutputs (requests EqualOutputs)
open GeneralNominalSaturationState (Alias)
abbrev focus := GeneralNominalCenteredHeadAllocMergeConflict.focus

theorem history : HistoryModels (stage atoms) witness := by
  refine ⟨source_witness,?_,?_,?_⟩
  · intro site member; cases List.mem_singleton.mp member
    exact point_root_holds snapshot.seed root (fun _ => rfl) witness
  · intro candidate member; cases List.mem_singleton.mp member; exact packet_models
  · intro candidate member; cases List.mem_singleton.mp member
    exact ⟨head_equations source_witness,effects witness⟩

theorem merged_class : MergedClass (stage atoms) focus :=
  ⟨aSite.occurrence.identity,bSite.occurrence.identity,List.mem_singleton_self _,child_ids_distinct,.refl _⟩

theorem impossible_class : ¬ ∃ model, HistoryModels (stage atoms) model ∧ ClassEquations (stage atoms) focus model := by
  rintro ⟨model,valid,equations⟩
  have outputs := (valid.2.2.1 plan (List.mem_singleton_self _)).2.2
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at outputs
  rw [schema_exact] at outputs
  have one := outputs _ List.mem_cons_self
  have two := outputs _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have firstRequest : ⟨0,aTarget⟩ ∈ requests (stage atoms).core focus :=
    GeneralNominalCenteredHeadOutputs.request_retained aSite.observed
      (List.mem_cons_of_mem _ List.mem_cons_self) (.refl _) (a_outputs.symm ▸ List.mem_singleton_self _)
  have lastRequest : ⟨0,bTarget⟩ ∈ requests (stage atoms).core focus :=
    GeneralNominalCenteredHeadOutputs.request_retained bSite.observed
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      (.edge (List.mem_singleton_self _)) (b_outputs.symm ▸ List.mem_singleton_self _)
  have equal := equations.1 _ firstRequest _ lastRequest rfl
  exact GeneralNominalCenteredHeadMatCompletionCollisionPackets.int_not_variant
    ⟨subtype_trans one.2 (subtype_trans equal.1 two.1),subtype_trans two.2 (subtype_trans equal.2 one.1)⟩

theorem conflict_stage : MergedOutputConflict (stage atoms) focus :=
  base_conflict merged_class ⟨witness,history⟩ impossible_class

theorem final_conflict : MergedOutputConflict final focus := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]; exact conflict_stage

theorem final_rejected : GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final focus .rejected := by
  obtain ⟨atoms,good,supported,same⟩ := final_shape
  rw [same]
  exact B4TargetV7.merged_unique_rejected conflict_stage (GeneralNominalCenteredHeadAllocMergeConflict.unique good supported)

theorem final_not_selected : ¬ GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final focus (.selected key children) :=
  fun chosen => (B4TargetV7.selected_iff.mp chosen).2 final_conflict

theorem final_not_pending : ¬ GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final focus .pending :=
  B4TargetV7.conflict_not_pending final_conflict

theorem final_classifies_rejected : B4TargetV7.Classify (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
    sourceRegistry final focus .rejected := .rejected final_rejected

/-- The same checked source and actual execution now report the class error. -/
theorem regression :
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Checked sourceRegistry ∧
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Initial sourceRegistry root start ∧
    Models start witness ∧ Models installed witness ∧
    B4Target.Steps (GeneralNominalCenteredHeadAllocV7Boundary.Step sourceRegistry root) start final ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Stable sourceRegistry final focus ∧
    GeneralNominalSaturationState.Generated final.core.erased.current root focus ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final focus .rejected :=
  ⟨⟨rfl,source_checked⟩,initial_source,inhabited,installed_models,
    GeneralNominalCenteredHeadAllocMergeConflict.final_trace,
    GeneralNominalCenteredHeadAllocMergeConflict.final_stable_focus,
    GeneralNominalCenteredHeadAllocMergeConflict.final_generated,final_rejected⟩

end Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression
