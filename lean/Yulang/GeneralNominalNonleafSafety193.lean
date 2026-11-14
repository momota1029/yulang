import Yulang.GeneralNominalNonleafInstallation193
import Yulang.GeneralDictionarySupportRecursiveClassification

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafSafety193
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193
open GeneralNominalExamples (registry context state displayRoot displayChild model listDescriptor)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters GeneralNominalCenteredSteps
noncomputable abbrev current := finish.core.erased.current.context

theorem feedback_acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.core.erased.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model final_model.1.1
    (fun source => if source = 0 then 1 else 0)
    (by intro source; by_cases zero : source = 0 <;> simp [zero,GeneralNominalOutputGrowth.tower] <;> rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

theorem graph_tests : (graph finish.core).tests = [(.source 0,.nominal 0 1)] := by
  change GeneralNominalCenteredSteps.Plan.tests plan ++ [] = _
  rw [List.append_nil]
  unfold GeneralNominalCenteredSteps.Plan.tests
  rw [head_schema,named_empty]
  simp [GeneralNominalCenters.Plan.schema,GeneralNominalCenters.Plan.childRequests,
    plan,packet,GeneralDeclarationExamples.display,List.ofFn_succ,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
    GeneralDeclarationPatterns.normalize]

theorem center_distinct : ¬ GeneralNominalOriginTerms.Same model (.source 0) (.source 1) := by
  intro same
  have equal := same.2.2 _ _ (.source 0) (.source 1)
  have impossible : 1 = 0 := (GeneralNominalOutputGrowth.tower_equivalent 1 0).mp equal
  cases impossible

private theorem recorded_shapes (recorded : GeneralNominalCenteredGraph.Recorded (graph finish.core) first last) :
    GeneralNominalOriginTerms.Same model first (.source 0) ∧
    GeneralNominalOriginTerms.Same model last (.source 1) := by
  cases recorded with
  | structural shape index member => simp [graph_tests] at member
  | nominal name arity index member =>
    have same := List.mem_singleton.mp (graph_tests ▸ member)
    cases same
    have zero : index.val = 0 := by omega
    rw [zero]
    refine ⟨GeneralNominalOriginTerms.source_self model 0,?_⟩
    have eqs := equations model (GeneralNominalExamples.state_models true)
    have actual := eqs.2.2.1.2
    rw [head_schema] at actual
    have same := actual ⟨0,origin,.actual⟩ (List.mem_singleton_self _)
    simpa only [ite_true,binder_zero] using same

theorem centered_acyclic (origin : GeneralNominalRecursiveInspection.Origin) : ¬ Cyclic finish.core origin := by
  rintro (⟨source,_,cycle,_⟩ | cycle)
  · exact feedback_acyclic source cycle
  · have endpoints {first last} (edge : GeneralNominalCenteredGraph.Edge (graph finish.core) first last) :
        GeneralNominalOriginTerms.Same model first (.source 0) ∧
        GeneralNominalOriginTerms.Same model last (.source 1) := by
      obtain ⟨parent,child,recorded,left,right⟩ := edge
      have shape := recorded_shapes recorded
      exact ⟨GeneralNominalOriginTerms.same_trans (left model final_model.1) shape.1,
        GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm (right model final_model.1)) shape.2⟩
    obtain ⟨⟨next,edge,path⟩,_⟩ := cycle
    have one := endpoints edge
    cases path with
    | nil => exact center_distinct (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm one.1) one.2)
    | cons edge rest =>
      have two := endpoints edge
      exact center_distinct (GeneralNominalOriginTerms.same_trans (GeneralNominalOriginTerms.same_symm two.1) one.2)

theorem ready_at (slot : Fin 2) : GeneralNominalSharedSupport.ReadyAt finish.core.erased slot.val := by
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero; subst slot
    exact ⟨_,_,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl,
      GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.nominal (snapshot := state true) 0 listDescriptor rfl)⟩
  · have same : slot = 1 := by apply Fin.ext; have bound := slot.isLt; omega
    subst slot
    exact ⟨_,_,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl,
      GeneralNominalSharedSupport.source_head _ (GeneralNominalSupport.Head.scalar (snapshot := state true) 1 .int rfl)⟩

theorem child_decision : DecisionGuard registry finish.core displayChild :=
  GeneralNominalCenteredSupport.legacy_decision ⟨fun _ => ready_at 1,fun _ _ _ _ _ slot _ => ready_at slot⟩

theorem parent_decision : DecisionGuard registry finish.core displayRoot :=
  GeneralNominalCenteredSupport.legacy_decision ⟨fun _ => ready_at 0,fun _ _ _ _ _ slot _ => ready_at slot⟩

theorem feedback_selected {demand : GeneralSourceDictionaries.Occurrence roles} {key kids}
    (old : GeneralNominalFeedbackK2.Local registry GeneralDictionarySupportRecursiveExample.finish.current demand (.selected key kids)) :
    GeneralNominalFeedbackK2.Local registry finish.core.erased.current demand (.selected key kids) := by
  cases old with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,safe.2.2.2⟩ unique
    · rintro (raw | ⟨_,_,index,cycle,_⟩)
      · exact safe.2.1 (Or.inl raw)
      · exact feedback_acyclic _ cycle
    · rintro (raw | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
      · exact safe.2.2.1 (Or.inl raw)
      · exact feedback_acyclic _ cycle

theorem child_center_selected : GeneralNominalCenteredBoundary.Local registry finish.core displayChild (.selected 3 []) :=
  GeneralNominalCenteredBoundary.selected_of_old (feedback_selected GeneralDictionarySupportRecursiveClassification.leaf_selected) centered_acyclic child_decision

theorem parent_center_selected : GeneralNominalCenteredBoundary.Local registry finish.core displayRoot (.selected 1 [displayChild]) :=
  GeneralNominalCenteredBoundary.selected_of_old (feedback_selected GeneralDictionarySupportRecursiveClassification.parent_selected) centered_acyclic parent_decision
end Yulang.GeneralNominalNonleafSafety193
