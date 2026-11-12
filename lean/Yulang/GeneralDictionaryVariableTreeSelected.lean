import Yulang.GeneralDictionaryVariableTreeCycles

namespace Yulang.GeneralDictionaryVariableTreeSelected
open GeneralDictionaryVariableTreeExample GeneralDictionaryVariableTreeInitialJoint
open GeneralDictionaryVariableTreeCycles
open GeneralNominalBranchExample (state context root)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem other_failed
    (check : GeneralDeclarations.DeclarationChecked registry.constructors roles leafDeclaration) :
    Failed registry context root leafDeclaration check := by
  refine ⟨metadata,GeneralNominalSourceFormation.initial_fresh context initial_source root.identity,
    [(0,0)],rfl,?_,?_,Or.inl other_conflict⟩ <;> decide +kernel

theorem not_mixed_recurs (slot : Fin 3) : ¬ GeneralNominalMixedRecurrence.RecursAt state slot := by
  rintro ⟨⟨kind,_,_⟩,_⟩
  exact Fin.elim0 kind

theorem selected : GeneralNominalFeedbackK2.Local registry start.current root
    (.selected declaration.id children) := by
  refine .selected ⟨root_ready,?_,?_,?_⟩ unique
  · rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
    · exact old_acyclic slot recurs
    · exact acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact old_acyclic visited.1 recurs
    · exact acyclic _ cycle
  · rintro (⟨_,decl,visible,check,_,notFailed,unprepared⟩ | ⟨_,legacy⟩)
    · rcases List.mem_cons.mp visible with first | rest
      · subst decl
        exact unprepared prepared
      · have same := List.mem_singleton.mp rest
        subst decl
        exact notFailed (other_failed check)
    · rcases legacy with ⟨bad,_⟩ | ⟨bad,_⟩
      · obtain ⟨_,_,_,slot,_,recurrent⟩ := bad
        exact not_mixed_recurs slot recurrent
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,recurrent⟩ := bad
        exact not_mixed_recurs visited.1 recurrent

theorem decisions : GeneralNominalSupport.DecisionGuard start registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    exact GeneralNominalSupport.source_ready start 0 (.nominal 5 2) _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state) 0 GeneralNominalBranchExample.parent rfl)
      (GeneralNominalSupport.Head.nominal (snapshot := state) 0 GeneralNominalBranchExample.parent rfl) []
  · intro decl visible role bounds located slot member
    change Fin 3 at slot
    have head := GeneralNominalSupport.Head.nominal (snapshot := state) slot
      (if slot = 0 then GeneralNominalBranchExample.parent else if slot = 1 then GeneralNominalBranchExample.left else GeneralNominalBranchExample.right) rfl
    exact GeneralNominalSupport.source_ready start _ _ _ _ head head []

theorem support_selected : GeneralNominalSupportBoundary.Local registry start root
    (.selected declaration.id children) :=
  GeneralNominalSupportBoundary.selected_supported selected [] decisions
end Yulang.GeneralDictionaryVariableTreeSelected
