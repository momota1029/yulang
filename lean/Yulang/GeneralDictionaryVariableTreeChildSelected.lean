import Yulang.GeneralDictionaryVariableTreeInstallation

namespace Yulang.GeneralDictionaryVariableTreeChildSelected
open GeneralDictionaryVariableTreeExample GeneralDictionaryVariableTreeEvidence
open GeneralDictionaryVariableTreeInitialJoint GeneralDictionaryVariableTreeCycles
open GeneralNominalBranchExample (state context root model state_models)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem child_input (index) : child.demand.arguments index = (1,1) := by
  simp [child,GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,
    frame,GeneralNominalAllocation.frame,GeneralNominalAllocation.capture,captures_exact,
    GeneralNominalAllocation.occurrences,GeneralDeclarationPatterns.normalize]

theorem child_ready : ¬ GeneralNominalState.RootPending state child.demand := by
  rintro ⟨index,unknown⟩
  apply unknown
  rw [child_input]
  exact ⟨1,rfl,Or.inr ⟨GeneralNominalBranchExample.left,rfl⟩⟩

theorem child_linked : GeneralNominalState.Linked state child.demand := by
  constructor
  · intro index
    rw [child_input]
    constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro output member
    cases member

theorem prepared_child : Prepared registry context child leafDeclaration leaf_checked := by
  refine ⟨metadata,child_linked,
    GeneralNominalSourceFormation.initial_fresh context initial_source child.identity,
    [(1,1)],child_arguments,?_,GeneralDictionaryTreeLeaf.ready context registry child leafDeclaration leaf_checked leafShape,
    model,GeneralDictionaryTreeLeaf.branch_models context registry child leafDeclaration leaf_checked leafShape model state_models⟩
  rw [GeneralNominalTreeFacts.report_exact context leafDeclaration leafShape.tree leafShape.query]
  exact GeneralNominalTreeFacts.tree_finished state leafShape.tree none

theorem child_survivor : Survivor registry context child leafDeclaration.id [] :=
  ⟨child_ready,leafDeclaration,by simp,leaf_checked,rfl,rfl,[(1,1)],child_arguments,prepared_child,
    (GeneralDictionaryLinearLeaf.children_empty context registry child leafDeclaration leaf_checked rfl _).symm⟩

theorem parent_conflict : (report context declaration [(1,1)]).conflicts ≠ [] := by decide +kernel

theorem parent_failed
    (check : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration) :
    Failed registry context child declaration check := by
  refine ⟨metadata,GeneralNominalSourceFormation.initial_fresh context initial_source child.identity,
    [(1,1)],child_arguments,?_,?_,Or.inl parent_conflict⟩ <;> decide +kernel

theorem parent_not_prepared
    (check : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration) :
    ¬ Prepared registry context child declaration check := by
  rintro ⟨_,_,_,bounds,located,finished,_⟩
  rw [child_arguments] at located
  cases Option.some.inj located
  exact parent_conflict finished.2.1

theorem unique_child : GeneralNominalLocalBoundary.Unique (GeneralNominalFeedbackK2.fields roles)
    registry start.current child leafDeclaration.id [] := by
  change Survivor registry context child leafDeclaration.id [] ∧
    ∀ key kids, Survivor registry context child key kids → key = leafDeclaration.id ∧ kids = []
  refine ⟨child_survivor,?_⟩
  rintro key kids ⟨_,decl,visible,check,identity,_,bounds,located,ready,emitted⟩
  rcases List.mem_cons.mp visible with first | rest
  · subst decl
    exact False.elim (parent_not_prepared check ready)
  · have same := List.mem_singleton.mp rest
    subst decl
    rw [child_arguments] at located
    cases Option.some.inj located
    exact ⟨identity.symm,emitted.trans (GeneralDictionaryLinearLeaf.children_empty context registry child leafDeclaration check rfl _)⟩

theorem child_selected : GeneralNominalFeedbackK2.Local registry start.current child
    (.selected leafDeclaration.id []) := by
  refine .selected ⟨child_ready,?_,?_,?_⟩ unique_child
  · rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
    · exact old_acyclic slot recurs
    · exact acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact old_acyclic visited.1 recurs
    · exact acyclic _ cycle
  · rintro (⟨_,decl,visible,check,_,notFailed,unprepared⟩ | ⟨_,legacy⟩)
    · rcases List.mem_cons.mp visible with first | rest
      · subst decl
        exact notFailed (parent_failed check)
      · have same := List.mem_singleton.mp rest
        subst decl
        exact unprepared prepared_child
    · rcases legacy with ⟨bad,_⟩ | ⟨bad,_⟩
      · obtain ⟨_,_,_,slot,_,recurrent⟩ := bad
        exact GeneralDictionaryVariableTreeSelected.not_mixed_recurs slot recurrent
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,recurrent⟩ := bad
        exact GeneralDictionaryVariableTreeSelected.not_mixed_recurs visited.1 recurrent

theorem child_decisions : GeneralNominalSupport.DecisionGuard start registry child [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    rw [show (child.demand.arguments index).1 = 1 by rw [child_input]]
    exact GeneralNominalSupport.source_ready start 1 (.nominal 2 0) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 GeneralNominalBranchExample.left rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 1 GeneralNominalBranchExample.left rfl) []
  · intro decl visible role bounds located slot member
    change Fin 3 at slot
    have head := GeneralNominalSupport.Head.nominal (snapshot := state) slot
      (if slot = 0 then GeneralNominalBranchExample.parent else if slot = 1 then GeneralNominalBranchExample.left else GeneralNominalBranchExample.right) rfl
    exact GeneralNominalSupport.source_ready start _ _ _ _ head head []

theorem child_support_selected : GeneralNominalSupportBoundary.Local registry start child
    (.selected leafDeclaration.id []) :=
  GeneralNominalSupportBoundary.selected_supported child_selected [] child_decisions

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry start root (.selected (.node declaration.id [.node leafDeclaration.id []])) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry start root _).mpr
    GeneralDictionaryVariableTreeSelected.support_selected
  have leaf := (GeneralNominalSupportBoundary.local_correspondence registry start child _).mpr child_support_selected
  rw [children_exact] at parent
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected leafSafe leafUnique => exact .cons (.selected leafSafe leafUnique .nil) .nil

/-- Declarative recursive classification already succeeds in this initial
state, but a real guarded install is still possible: this is not a final run. -/
theorem reachable_classified_unstable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry start root (.selected (.node declaration.id [.node leafDeclaration.id []])) ∧
    ¬ GeneralNominalSupportSteps.Stable registry start root :=
  ⟨actual_reachable,initial_models,classified,GeneralDictionaryVariableTreeInstallation.not_stable⟩
end Yulang.GeneralDictionaryVariableTreeChildSelected
