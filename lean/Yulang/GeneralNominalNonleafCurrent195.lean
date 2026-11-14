import Yulang.GeneralNominalCurrentTree195
import Yulang.GeneralNominalNonleafCatalogue195

/-! The current-only completion contract is inhabited by the actual nonleaf
example, independently of its incomplete recorded journal. -/
namespace Yulang.GeneralNominalNonleafCurrent195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193
open GeneralNominalNonleafChild193
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralDeclarationExamples (roles display)
open GeneralNominalNonleafFinal194 (parentPacket parentPlan)
open GeneralNominalReuseCatalogue195 (Reusable)
open GeneralNominalCurrentTree195 (TotalCompletion)
open GeneralNominalCommonBridge (Assignment)

theorem current_instance (assignment : Assignment) (valid : Models finish assignment) :
    GeneralDictionaryRecursiveEvidence.Instance registry current assignment displayRoot 1 [displayChild] := by
  have source := GeneralNominalOrdinaryJournal194.packet_instance
    GeneralNominalNonleafCatalogue195.ordinary_path packet (by change packet ∈ [packet]; simp) assignment valid
  change GeneralDictionaryRecursiveEvidence.Instance registry current assignment displayRoot 1 plan.packet.children at source
  rw [children_exact] at source
  exact source

/-- Reconstruct the current branch and readiness from the independently
transported source instance; no final Installable certificate is used. -/
theorem current_branch (assignment : Assignment) (valid : Models finish assignment) :
    GeneralNominalRecursiveCandidates.RequestReady registry current displayRoot display
      GeneralDeclarationExamples.display_checked [((0 : Fin 2),(0 : Fin 2))] ∧ parentPacket.Holds assignment := by
  obtain ⟨decl,present,checked,key,role,bounds,located,finished,ready,kids,metadata,branch⟩ := current_instance assignment valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · cases key
  · have same : [((0 : Fin 2),(0 : Fin 2))] = bounds := Option.some.inj located
    subst bounds
    exact ⟨ready,branch⟩
  · cases key

/-- For this actual fixture the whole model ledger follows from its raw journal
model. This is not asserted for arbitrary states. -/
theorem lift_raw_model (assignment : Assignment)
    (valid : GeneralNominalSaturationState.Models finish.core.erased.current assignment) :
    Models finish assignment := by
  have old := GeneralNominalRefinements.models
    (GeneralNominalRefinements.installed registry (GeneralNominalExamples.context true)
      displayRoot display packet.bounds) assignment valid.1
  exact (install_models enabled assignment).mpr (installation_models assignment old)

theorem parent_children : parentPacket.children = [displayChild] := by
  have found := GeneralNominalNonleafFinal194.survivor
  obtain ⟨_,decl,present,check,key,role,bounds,located,ready,kids⟩ := found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  · cases key
  · have same : [((0 : Fin 2),(0 : Fin 2))] = bounds := Option.some.inj located
    subst bounds
    exact kids.symm
  · cases key

theorem parent_committed : GeneralNominalFeedbackSteps.Committed finish.core.erased.current parentPacket := by
  constructor
  · intro assignment valid
    exact (current_branch assignment (lift_raw_model assignment valid)).2
  · intro child member
    rw [parent_children] at member
    cases List.mem_singleton.mp member
    change (displayRoot,displayChild) ∈ [] ++ plan.packet.children.map _
    rw [children_exact]
    exact List.mem_singleton_self _

theorem parent_reusable : Reusable registry finish parentPlan :=
  ⟨GeneralNominalNonleafFinal194.frame,(current_branch model final_model).1,parent_committed⟩

theorem generated_cases {focus : Occurrence roles}
    (generated : GeneralNominalSaturationState.Generated finish.core.erased.current displayRoot focus) :
    focus = displayRoot ∨ focus = displayChild := by
  induction generated with
  | root => exact Or.inl rfl
  | @child parent child prior member ih =>
    change (parent,child) ∈ [] ++ plan.packet.children.map _ at member
    rw [children_exact] at member
    have same := List.mem_singleton.mp member
    exact Or.inr (congrArg Prod.snd same)
  | alias prior first last related ih =>
    rw [GeneralNominalNonleafAdministrative193.raw_sites] at last
    simp only [List.mem_cons,List.not_mem_nil,or_false] at last
    rcases last with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem total_completion : TotalCompletion registry finish displayRoot := by
  intro focus generated
  rcases generated_cases generated with rfl | rfl
  · exact ⟨parentPlan,rfl,parent_reusable⟩
  · exact ⟨childPlan,rfl,GeneralNominalNonleafCatalogue195.reusable childPlan (List.mem_singleton_self _)⟩

theorem uniform_current_dictionary :
    ∃ tree : Dictionary roles, tree.root = displayRoot ∧
      GeneralSourceDictionaries.Evidence (GeneralNominalCurrentTree195.Rule registry finish) tree ∧
      ∀ assignment, Models finish assignment →
        (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry finish assignment displayRoot (erase tree) :=
  GeneralNominalCurrentTree195.uniform_dictionary total_completion
theorem selected_current_sound : ∀ assignment, Models finish assignment →
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry finish assignment displayRoot
      (.node 1 [.node 3 []]) :=
  GeneralNominalCurrentCompletion195.selected_sound
    (GeneralNominalCurrentTree195.selected_completion total_completion) _
    GeneralNominalNonleafFinal194.parent_classify

end Yulang.GeneralNominalNonleafCurrent195
