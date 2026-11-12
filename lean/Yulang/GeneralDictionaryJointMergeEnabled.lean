import Yulang.GeneralDictionaryJointMergeExample

/-! The positive nonempty-output fixture has an actual enabled support merge.
The manually registered starting journal is NOT claimed SourceFormed. -/
namespace Yulang.GeneralDictionaryJointMergeEnabled
open GeneralDictionaryJointMergeExample
open GeneralNominalSaturationState GeneralNominalSupportSteps
open GeneralNominalDemandMerging (pointSite)
open GeneralNominalRecursiveInspection

abbrev tracked : GeneralNominalSupport.Tracked GeneralDeclarationExamples.roles :=
  ⟨context,before,[]⟩

theorem recovered (identity target : Nat) :
    GeneralNominalFeedbackSites.recover before (pointSite (root identity target)) =
      pointSite (root identity target) := by
  simp [GeneralNominalFeedbackSites.recover,
      pointSite,root,demand,List.ofFn_succ]
  change List.ofFn (fun index : Fin 1 =>
    GeneralNominalFeedbackSites.recoverOrigin before (pointSite (root identity target)) index) = _
  rw [List.ofFn_succ,List.ofFn_zero]
  rfl

theorem same (models : GeneralNominalCommonBridge.Assignment → Prop) :
    GeneralNominalDemandMerging.SameInputs models
      (GeneralNominalFeedbackSites.recover before first)
      (GeneralNominalFeedbackSites.recover before last) := by
  rw [recovered,recovered]
  exact ⟨rfl,.cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil⟩

theorem guard : GeneralNominalSupportChoices.MergeGuard tracked first last [] := by
  refine ⟨same _,?_,?_⟩
  · intro index absent
    have eq : index = ⟨0,by decide⟩ := Fin.ext (Nat.lt_one_iff.mp index.isLt)
    subst index
    cases absent
  · intro index absent
    have eq : index = ⟨0,by decide⟩ := Fin.ext (Nat.lt_one_iff.mp index.isLt)
    subst index
    cases absent

theorem distinct : ¬ Alias before first.occurrence.identity last.occurrence.identity := by
  have empty : ∀ a b, Alias before a b → a = b := by
    intro a b related
    induction related with
    | refl => rfl
    | edge member => cases member
    | symm _ ih => exact ih.symm
    | trans _ _ one two => exact one.trans two
  intro related
  have impossible := empty _ _ related
  contradiction

theorem actual_step :
    Step registry first.occurrence tracked (GeneralNominalSupportSteps.merge tracked first last []) :=
  ⟨first.occurrence,.root,.merge first last [] (by simp) (by simp) (same _) distinct guard⟩

theorem enabled_nonempty_joint :
    Step registry first.occurrence tracked (GeneralNominalSupportSteps.merge tracked first last []) ∧
    GeneralNominalDemandMerging.outputAtoms first last =
      [.tyLe (.var 1) (.var 3),.tyLe (.var 3) (.var 1)] ∧
    GeneralNominalJointCandidates.Joint registry
      (GeneralNominalSupportSteps.merge tracked first last []).current first.occurrence 7 :=
  ⟨actual_step,output_atoms_nonempty,merged_joint⟩

end Yulang.GeneralDictionaryJointMergeEnabled
